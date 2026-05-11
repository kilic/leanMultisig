use backend::*;
use lean_vm::{
    ColIndex, EF, F, NUM_SHA256_COMPRESS_RN_COLS, SHA256_RN_COL_FLAG, SHA256_RN_COL_W_START, SHA256_RN_COMPRESS_ROUNDS,
    SHA256_RN_SCHEDULE_EXTENSIONS, SHA256_RN_U32_LIMBS, Sha256RnSchedulingRoundCols, Table, TableTrace,
};
use std::{collections::BTreeMap, marker::PhantomData, mem::size_of};
use sub_protocols::{
    AuxTrace, ENDIANNESS_PIVOT_GKR, StackSectionDescriptor, StackSectionId, prove_gkr_quotient, verify_gkr_quotient,
};
use utils::{ToUsize, build_prover_state, finger_print, finger_print_packed, from_end};

pub const SHA256_RN_RANGE_CHECK_ADD_LOG_N_ROWS: usize = 19;
pub const SHA256_RN_RANGE_CHECK_ADD_N_ROWS: usize = 1 << SHA256_RN_RANGE_CHECK_ADD_LOG_N_ROWS;
pub const SHA256_RN_RANGE_CHECK_ADD_N_COLUMNS: usize = 4;
pub const SHA256_RN_RANGE_CHECK_ADD_STACKED_N_VARS: usize =
    SHA256_RN_RANGE_CHECK_ADD_LOG_N_ROWS + SHA256_RN_RANGE_CHECK_ADD_N_COLUMNS.ilog2() as usize;
pub const SHA256_RN_CARRY_4_MULT_AUX_LABEL: &str = "sha256_rn_range_check_add_carry_4_mult";
pub const SHA256_RN_CARRY_4_MULT_AUX_N_COLUMNS: usize = 1;

const SHA256_RN_FIXED_LOOKUP_TRANSCRIPT_DOMAIN: usize = 0x5A_52_4E;
const SHA256_RN_FIXED_LOOKUP_TRANSCRIPT_VERSION: usize = 2;
const SHA256_RN_ADD4_FIXED_LOOKUP_DOMAINSEP: usize = 0xAD_D4;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sha256RnRangeCheckAddVerifierSetup {
    pub log_n_rows: usize,
    pub n_columns: usize,
    pub stacked_n_vars: usize,
    pub root: [F; DIGEST_ELEMS],
    pub ood_points: Vec<EF>,
    pub ood_answers: Vec<EF>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sha256RnFixedLookupVerifierSetup {
    pub range_check_add: Sha256RnRangeCheckAddVerifierSetup,
}

impl Sha256RnFixedLookupVerifierSetup {
    pub fn transcript_scalars(&self) -> Vec<F> {
        let mut scalars = vec![
            F::from_usize(SHA256_RN_FIXED_LOOKUP_TRANSCRIPT_DOMAIN),
            F::from_usize(SHA256_RN_FIXED_LOOKUP_TRANSCRIPT_VERSION),
            F::from_usize(self.range_check_add.log_n_rows),
            F::from_usize(self.range_check_add.n_columns),
            F::from_usize(self.range_check_add.stacked_n_vars),
        ];
        scalars.extend(self.range_check_add.root);
        scalars.extend(flatten_scalars_to_base::<F, EF>(&self.range_check_add.ood_points));
        scalars.extend(flatten_scalars_to_base::<F, EF>(&self.range_check_add.ood_answers));
        scalars
    }
}

impl Sha256RnRangeCheckAddVerifierSetup {
    pub fn parsed_commitment(&self) -> ParsedCommitment<F, EF> {
        ParsedCommitment {
            num_variables: self.stacked_n_vars,
            root: self.root,
            ood_points: self.ood_points.clone(),
            ood_answers: self.ood_answers.clone(),
            base_field: PhantomData,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Sha256RnRangeCheckAddFixedColumns {
    pub value: Vec<F>,
    pub carry_4: Vec<F>,
    pub carry_7: Vec<F>,
    pub carry_8: Vec<F>,
}

impl Sha256RnRangeCheckAddFixedColumns {
    pub fn generate() -> Self {
        let mut value = Vec::with_capacity(SHA256_RN_RANGE_CHECK_ADD_N_ROWS);
        let mut carry_4 = Vec::with_capacity(SHA256_RN_RANGE_CHECK_ADD_N_ROWS);
        let mut carry_7 = Vec::with_capacity(SHA256_RN_RANGE_CHECK_ADD_N_ROWS);
        let mut carry_8 = Vec::with_capacity(SHA256_RN_RANGE_CHECK_ADD_N_ROWS);

        for row in 0..SHA256_RN_RANGE_CHECK_ADD_N_ROWS {
            let slot = row & 7;
            value.push(F::from_usize(row >> 3));
            carry_4.push(F::from_usize(if slot < 4 { slot } else { 0 }));
            carry_7.push(F::from_usize(if slot < 7 { slot } else { 0 }));
            carry_8.push(F::from_usize(slot));
        }

        Self {
            value,
            carry_4,
            carry_7,
            carry_8,
        }
    }

    pub fn columns(&self) -> [&[F]; SHA256_RN_RANGE_CHECK_ADD_N_COLUMNS] {
        [&self.value, &self.carry_4, &self.carry_7, &self.carry_8]
    }

    pub fn stacked_polynomial(&self) -> Vec<F> {
        let mut polynomial = F::zero_vec(SHA256_RN_RANGE_CHECK_ADD_N_ROWS * SHA256_RN_RANGE_CHECK_ADD_N_COLUMNS);
        for (col_idx, col) in self.columns().iter().enumerate() {
            let start = col_idx << SHA256_RN_RANGE_CHECK_ADD_LOG_N_ROWS;
            polynomial[start..start + SHA256_RN_RANGE_CHECK_ADD_N_ROWS].copy_from_slice(col);
        }
        polynomial
    }
}

#[derive(Debug, Clone)]
pub struct Sha256RnRangeCheckAddProverSetup {
    pub columns: Sha256RnRangeCheckAddFixedColumns,
    pub polynomial: Vec<F>,
    pub whir_witness: Witness<EF>,
}

#[derive(Debug, Clone)]
pub struct Sha256RnFixedLookupProverSetup {
    pub range_check_add: Sha256RnRangeCheckAddProverSetup,
    pub verifier: Sha256RnFixedLookupVerifierSetup,
}

impl Sha256RnFixedLookupProverSetup {
    pub fn verifier_setup(&self) -> &Sha256RnFixedLookupVerifierSetup {
        &self.verifier
    }
}

pub fn setup_sha256_rn_fixed_lookups(whir_config: &WhirConfigBuilder) -> Sha256RnFixedLookupProverSetup {
    let columns = Sha256RnRangeCheckAddFixedColumns::generate();
    let polynomial = columns.stacked_polynomial();
    let mle = MleOwned::Base(polynomial.clone());
    let mut setup_state = build_prover_state();
    let whir = WhirConfig::new(whir_config, SHA256_RN_RANGE_CHECK_ADD_STACKED_N_VARS);
    let (whir_witness, root) = whir.commit_with_root(&mut setup_state, &mle, polynomial.len());

    let verifier = Sha256RnFixedLookupVerifierSetup {
        range_check_add: Sha256RnRangeCheckAddVerifierSetup {
            log_n_rows: SHA256_RN_RANGE_CHECK_ADD_LOG_N_ROWS,
            n_columns: SHA256_RN_RANGE_CHECK_ADD_N_COLUMNS,
            stacked_n_vars: SHA256_RN_RANGE_CHECK_ADD_STACKED_N_VARS,
            root,
            ood_points: whir_witness.ood_points.clone(),
            ood_answers: whir_witness.ood_answers.clone(),
        },
    };

    Sha256RnFixedLookupProverSetup {
        range_check_add: Sha256RnRangeCheckAddProverSetup {
            columns,
            polynomial,
            whir_witness,
        },
        verifier,
    }
}

pub fn sha256_rn_add4_aux_trace_layout() -> StackSectionDescriptor {
    StackSectionDescriptor {
        id: StackSectionId::Aux(SHA256_RN_CARRY_4_MULT_AUX_LABEL),
        log_n_rows: SHA256_RN_RANGE_CHECK_ADD_LOG_N_ROWS,
        n_columns: SHA256_RN_CARRY_4_MULT_AUX_N_COLUMNS,
    }
}

pub fn build_sha256_rn_add4_carry_4_mult_trace(traces: &BTreeMap<Table, TableTrace>) -> AuxTrace {
    let rn_trace = &traces[&Table::sha256_compress_rn()];
    let mut mult = F::zero_vec(SHA256_RN_RANGE_CHECK_ADD_N_ROWS);
    if rn_trace.columns.is_empty() {
        return AuxTrace {
            label: SHA256_RN_CARRY_4_MULT_AUX_LABEL,
            log_n_rows: SHA256_RN_RANGE_CHECK_ADD_LOG_N_ROWS,
            columns: vec![mult],
        };
    }

    for row in 0..(1 << rn_trace.log_n_rows) {
        if rn_trace.columns[SHA256_RN_COL_FLAG][row] != F::ONE {
            continue;
        }
        for (value_col, carry_col) in sha256_rn_add4_request_columns() {
            let value = rn_trace.columns[value_col][row].to_usize();
            let carry = rn_trace.columns[carry_col][row].to_usize();
            assert!(value < 1 << 16, "sha256_rn add4 lookup value out of range");
            assert!(carry < 4, "sha256_rn add4 lookup carry out of range");
            mult[(value << 3) + carry] += F::ONE;
        }
    }

    AuxTrace {
        label: SHA256_RN_CARRY_4_MULT_AUX_LABEL,
        log_n_rows: SHA256_RN_RANGE_CHECK_ADD_LOG_N_ROWS,
        columns: vec![mult],
    }
}

fn sha256_rn_add4_request_columns() -> Vec<(ColIndex, ColIndex)> {
    let scheduling_start = SHA256_RN_COL_W_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_U32_LIMBS;
    let scheduling_round_width = size_of::<Sha256RnSchedulingRoundCols<u8>>();
    let carry_low_offset = scheduling_round_width - 2;
    let carry_high_offset = scheduling_round_width - 1;

    let mut request_columns = Vec::with_capacity(SHA256_RN_SCHEDULE_EXTENSIONS * SHA256_RN_U32_LIMBS);
    for round in 0..SHA256_RN_SCHEDULE_EXTENSIONS {
        let w_col = SHA256_RN_COL_W_START + (16 + round) * SHA256_RN_U32_LIMBS;
        let scheduling_round_start = scheduling_start + round * scheduling_round_width;
        request_columns.push((w_col, scheduling_round_start + carry_low_offset));
        request_columns.push((w_col + 1, scheduling_round_start + carry_high_offset));
    }

    debug_assert!(
        request_columns
            .iter()
            .all(|(value, carry)| { *value < NUM_SHA256_COMPRESS_RN_COLS && *carry < NUM_SHA256_COMPRESS_RN_COLS })
    );
    request_columns
}

#[derive(Debug, Clone)]
pub struct Sha256RnAdd4FixedLookupStatements {
    pub rn_claim: (MultilinearPoint<EF>, BTreeMap<ColIndex, EF>),
    pub aux_claim: (MultilinearPoint<EF>, BTreeMap<ColIndex, EF>),
    pub setup_statements: Vec<SparseStatement<EF>>,
}

#[allow(clippy::too_many_lines)]
pub fn prove_sha256_rn_add4_fixed_lookup(
    prover_state: &mut impl FSProver<EF>,
    traces: &BTreeMap<Table, TableTrace>,
    carry_4_mult_aux_trace: &AuxTrace,
    setup: &Sha256RnFixedLookupProverSetup,
) -> Sha256RnAdd4FixedLookupStatements {
    let rn_trace = &traces[&Table::sha256_compress_rn()];
    let rn_log_n_rows = rn_trace.log_n_rows;
    let rn_n_rows = 1 << rn_log_n_rows;
    let fixed_n_rows = SHA256_RN_RANGE_CHECK_ADD_N_ROWS;
    let requests = sha256_rn_add4_request_columns();
    let total_active_len = requests.len() * rn_n_rows + fixed_n_rows;
    let total_len = 1usize << log2_ceil_usize(total_active_len);
    let width = packing_width::<EF>();
    assert!(total_len.is_multiple_of(width));

    let c = prover_state.sample();
    let alphas = prover_state.sample_vec(log2_ceil_usize(3));
    let alphas_eq_poly = eval_eq(&alphas);
    let c_packed = EFPacking::<EF>::from(c);
    let alphas_packed: Vec<EFPacking<EF>> = alphas_eq_poly.iter().map(|a| EFPacking::<EF>::from(*a)).collect();
    let table_contrib =
        EFPacking::<EF>::from(*alphas_eq_poly.last().unwrap() * F::from_usize(SHA256_RN_ADD4_FIXED_LOOKUP_DOMAINSEP));

    let pivot = ENDIANNESS_PIVOT_GKR.min(rn_log_n_rows.min(SHA256_RN_RANGE_CHECK_ADD_LOG_N_ROWS));
    assert!(pivot > packing_log_width::<EF>());
    let chunk_size = 1usize << pivot;
    let chunk_shift = usize::BITS as usize - pivot;
    let chunk_mask = chunk_size - 1;
    let src_idx = |p: usize, w: usize| -> usize {
        let x = p * width + w;
        (x & !chunk_mask) | ((x & chunk_mask).reverse_bits() >> chunk_shift)
    };

    let mut numerators = F::zero_vec(total_len);
    let mut denominators = vec![EFPacking::<EF>::ONE; total_len / width];
    let mut offset = 0;

    let mult = &carry_4_mult_aux_trace.columns[0];
    assert_eq!(mult.len(), fixed_n_rows);
    numerators[offset..offset + fixed_n_rows]
        .chunks_exact_mut(chunk_size)
        .enumerate()
        .for_each(|(chunk, dst)| {
            let src = &mult[chunk * chunk_size..][..chunk_size];
            for (i, slot) in dst.iter_mut().enumerate() {
                *slot = -src[i.reverse_bits() >> chunk_shift];
            }
        });
    let fixed_columns = &setup.range_check_add.columns;
    denominators[offset / width..][..fixed_n_rows / width]
        .iter_mut()
        .enumerate()
        .for_each(|(p, slot)| {
            *slot = c_packed
                - finger_print_packed::<EF>(
                    table_contrib,
                    &[
                        PFPacking::<EF>::from_fn(|w| fixed_columns.value[src_idx(p, w)]),
                        PFPacking::<EF>::from_fn(|w| fixed_columns.carry_4[src_idx(p, w)]),
                    ],
                    &alphas_packed,
                );
        });
    offset += fixed_n_rows;

    for &(value_col, carry_col) in &requests {
        numerators[offset..offset + rn_n_rows]
            .chunks_exact_mut(chunk_size)
            .enumerate()
            .for_each(|(chunk, dst)| {
                let src = &rn_trace.columns[SHA256_RN_COL_FLAG][chunk * chunk_size..][..chunk_size];
                for (i, slot) in dst.iter_mut().enumerate() {
                    *slot = src[i.reverse_bits() >> chunk_shift];
                }
            });
        denominators[offset / width..][..rn_n_rows / width]
            .iter_mut()
            .enumerate()
            .for_each(|(p, slot)| {
                *slot = c_packed
                    - finger_print_packed::<EF>(
                        table_contrib,
                        &[
                            PFPacking::<EF>::from_fn(|w| rn_trace.columns[value_col][src_idx(p, w)]),
                            PFPacking::<EF>::from_fn(|w| rn_trace.columns[carry_col][src_idx(p, w)]),
                        ],
                        &alphas_packed,
                    );
            });
        offset += rn_n_rows;
    }
    assert_eq!(offset, total_active_len);

    let (sum, gkr_point) = prove_gkr_quotient::<EF>(
        prover_state,
        PFPacking::<EF>::pack_slice(&numerators),
        &denominators,
        pivot,
    );
    assert_eq!(sum, EF::ZERO);

    let rn_point = MultilinearPoint(from_end(&gkr_point.0, rn_log_n_rows).to_vec());
    let fixed_point = MultilinearPoint(from_end(&gkr_point.0, SHA256_RN_RANGE_CHECK_ADD_LOG_N_ROWS).to_vec());

    let mult_eval = mult.evaluate(&fixed_point);
    prover_state.add_extension_scalar(mult_eval);
    let aux_values = BTreeMap::from([(0, mult_eval)]);

    let fixed_value_eval = fixed_columns.value.evaluate(&fixed_point);
    let fixed_carry_4_eval = fixed_columns.carry_4.evaluate(&fixed_point);
    prover_state.add_extension_scalars(&[fixed_value_eval, fixed_carry_4_eval]);

    let mut rn_values = BTreeMap::new();
    let flag_eval = rn_trace.columns[SHA256_RN_COL_FLAG].evaluate(&rn_point);
    prover_state.add_extension_scalar(flag_eval);
    rn_values.insert(SHA256_RN_COL_FLAG, flag_eval);
    for &(value_col, carry_col) in &requests {
        let value_eval = rn_trace.columns[value_col].evaluate(&rn_point);
        prover_state.add_extension_scalar(value_eval);
        rn_values.insert(value_col, value_eval);

        let carry_eval = rn_trace.columns[carry_col].evaluate(&rn_point);
        prover_state.add_extension_scalar(carry_eval);
        rn_values.insert(carry_col, carry_eval);
    }
    Sha256RnAdd4FixedLookupStatements {
        rn_claim: (rn_point, rn_values),
        aux_claim: (fixed_point.clone(), aux_values),
        setup_statements: vec![SparseStatement::new(
            SHA256_RN_RANGE_CHECK_ADD_STACKED_N_VARS,
            fixed_point,
            vec![
                SparseValue::new(0, fixed_value_eval),
                SparseValue::new(1, fixed_carry_4_eval),
            ],
        )],
    }
}

pub fn verify_sha256_rn_add4_fixed_lookup(
    verifier_state: &mut impl FSVerifier<EF>,
    rn_log_n_rows: usize,
) -> ProofResult<Sha256RnAdd4FixedLookupStatements> {
    let requests = sha256_rn_add4_request_columns();
    let rn_n_rows = 1 << rn_log_n_rows;
    let fixed_n_rows = SHA256_RN_RANGE_CHECK_ADD_N_ROWS;
    let total_active_len = requests.len() * rn_n_rows + fixed_n_rows;
    let total_gkr_n_vars = log2_ceil_usize(total_active_len);

    let c = verifier_state.sample();
    let alphas = verifier_state.sample_vec(log2_ceil_usize(3));
    let alphas_eq_poly = eval_eq(&alphas);

    let (sum, gkr_point, numerators_value, denominators_value) = verify_gkr_quotient(verifier_state, total_gkr_n_vars)?;
    if sum != EF::ZERO {
        return Err(ProofError::InvalidProof);
    }

    let pref_at = |offset: usize, log_height: usize| {
        let n_missing = total_gkr_n_vars - log_height;
        let bits = to_big_endian_in_field::<EF>(offset >> log_height, n_missing);
        MultilinearPoint(bits).eq_poly_outside(&MultilinearPoint(gkr_point.0[..n_missing].to_vec()))
    };

    let rn_point = MultilinearPoint(from_end(&gkr_point.0, rn_log_n_rows).to_vec());
    let fixed_point = MultilinearPoint(from_end(&gkr_point.0, SHA256_RN_RANGE_CHECK_ADD_LOG_N_ROWS).to_vec());

    let mut retrieved_numerators_value = EF::ZERO;
    let mut retrieved_denominators_value = EF::ZERO;
    let mut offset = 0;

    let mult_eval = verifier_state.next_extension_scalar()?;
    let aux_values = BTreeMap::from([(0, mult_eval)]);
    let fixed_evals = verifier_state.next_extension_scalars_vec(2)?;
    let fixed_value_eval = fixed_evals[0];
    let fixed_carry_4_eval = fixed_evals[1];

    let pref = pref_at(offset, SHA256_RN_RANGE_CHECK_ADD_LOG_N_ROWS);
    retrieved_numerators_value -= pref * mult_eval;
    retrieved_denominators_value += pref
        * (c - finger_print(
            F::from_usize(SHA256_RN_ADD4_FIXED_LOOKUP_DOMAINSEP),
            &[fixed_value_eval, fixed_carry_4_eval],
            &alphas_eq_poly,
        ));
    offset += fixed_n_rows;

    let mut rn_values = BTreeMap::new();
    let flag_eval = verifier_state.next_extension_scalar()?;
    rn_values.insert(SHA256_RN_COL_FLAG, flag_eval);

    for &(value_col, carry_col) in &requests {
        let value_eval = verifier_state.next_extension_scalar()?;
        rn_values.insert(value_col, value_eval);
        let carry_eval = verifier_state.next_extension_scalar()?;
        rn_values.insert(carry_col, carry_eval);

        let pref = pref_at(offset, rn_log_n_rows);
        retrieved_numerators_value += pref * flag_eval;
        retrieved_denominators_value += pref
            * (c - finger_print(
                F::from_usize(SHA256_RN_ADD4_FIXED_LOOKUP_DOMAINSEP),
                &[value_eval, carry_eval],
                &alphas_eq_poly,
            ));
        offset += rn_n_rows;
    }

    retrieved_denominators_value += mle_of_zeros_then_ones(offset, &gkr_point.0);
    if retrieved_numerators_value != numerators_value || retrieved_denominators_value != denominators_value {
        return Err(ProofError::InvalidProof);
    }
    Ok(Sha256RnAdd4FixedLookupStatements {
        rn_claim: (rn_point, rn_values),
        aux_claim: (fixed_point.clone(), aux_values),
        setup_statements: vec![SparseStatement::new(
            SHA256_RN_RANGE_CHECK_ADD_STACKED_N_VARS,
            fixed_point,
            vec![
                SparseValue::new(0, fixed_value_eval),
                SparseValue::new(1, fixed_carry_4_eval),
            ],
        )],
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::default_whir_config;

    fn one_row_rn_trace(active: bool) -> BTreeMap<Table, TableTrace> {
        let mut rn_trace = TableTrace {
            columns: vec![vec![F::ZERO; 1]; NUM_SHA256_COMPRESS_RN_COLS],
            non_padded_n_rows: usize::from(active),
            log_n_rows: 0,
        };
        if active {
            rn_trace.columns[SHA256_RN_COL_FLAG][0] = F::ONE;
        }
        BTreeMap::from([(Table::sha256_compress_rn(), rn_trace)])
    }

    #[test]
    fn range_check_add_fixed_columns_match_rn_indexing() {
        let columns = Sha256RnRangeCheckAddFixedColumns::generate();
        assert_eq!(columns.value.len(), SHA256_RN_RANGE_CHECK_ADD_N_ROWS);
        assert_eq!(columns.carry_4.len(), SHA256_RN_RANGE_CHECK_ADD_N_ROWS);
        assert_eq!(columns.carry_7.len(), SHA256_RN_RANGE_CHECK_ADD_N_ROWS);
        assert_eq!(columns.carry_8.len(), SHA256_RN_RANGE_CHECK_ADD_N_ROWS);

        let assert_row = |row: usize, value: usize, carry_4: usize, carry_7: usize, carry_8: usize| {
            assert_eq!(columns.value[row], F::from_usize(value));
            assert_eq!(columns.carry_4[row], F::from_usize(carry_4));
            assert_eq!(columns.carry_7[row], F::from_usize(carry_7));
            assert_eq!(columns.carry_8[row], F::from_usize(carry_8));
        };

        assert_row(0, 0, 0, 0, 0);
        assert_row(3, 0, 3, 3, 3);
        assert_row(4, 0, 0, 4, 4);
        assert_row(6, 0, 0, 6, 6);
        assert_row(7, 0, 0, 0, 7);
        assert_row(8, 1, 0, 0, 0);
        assert_row(11, 1, 3, 3, 3);
        assert_row(SHA256_RN_RANGE_CHECK_ADD_N_ROWS - 1, (1 << 16) - 1, 0, 0, 7);
    }

    #[test]
    fn sha256_rn_fixed_lookup_setup_is_deterministic() {
        let whir_config = default_whir_config(1);
        let setup_a = setup_sha256_rn_fixed_lookups(&whir_config);
        let setup_b = setup_sha256_rn_fixed_lookups(&whir_config);
        assert_eq!(setup_a.verifier, setup_b.verifier);
    }

    #[test]
    fn sha256_rn_add4_multiplicity_one_row_has_96_requests() {
        let traces = one_row_rn_trace(true);
        let aux = build_sha256_rn_add4_carry_4_mult_trace(&traces);
        let total = aux.columns[0].iter().map(|x| x.to_usize()).sum::<usize>();
        assert_eq!(total, SHA256_RN_SCHEDULE_EXTENSIONS * SHA256_RN_U32_LIMBS);
    }

    #[test]
    fn sha256_rn_add4_multiplicity_inactive_row_is_zero() {
        let traces = one_row_rn_trace(false);
        let aux = build_sha256_rn_add4_carry_4_mult_trace(&traces);
        assert!(aux.columns[0].iter().all(|x| *x == F::ZERO));
    }

    #[test]
    fn sha256_rn_add4_multiplicity_uses_value_shifted_by_three_plus_carry() {
        let mut traces = one_row_rn_trace(true);
        let (value_col, carry_col) = sha256_rn_add4_request_columns()[0];
        let rn_trace = traces.get_mut(&Table::sha256_compress_rn()).unwrap();
        rn_trace.columns[value_col][0] = F::from_usize(7);
        rn_trace.columns[carry_col][0] = F::from_usize(3);

        let aux = build_sha256_rn_add4_carry_4_mult_trace(&traces);
        assert_eq!(aux.columns[0][(7 << 3) + 3], F::ONE);
    }
}
