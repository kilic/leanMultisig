use backend::*;
use lean_vm::{
    BITS_PER_LIMB, BigSigma0, BigSigma1, ColIndex, EF, F, LIMB_MASK, NUM_SHA256_COMPRESS_RN_COLS, SHA256_RN_COL_FLAG,
    SHA256_RN_COMPRESS_ROUNDS, SHA256_RN_K, SHA256_RN_VIRTUAL_BIG_SIGMA0_I0_ARITY,
    SHA256_RN_VIRTUAL_BIG_SIGMA0_I0_START, SHA256_RN_VIRTUAL_BIG_SIGMA0_I1_ARITY,
    SHA256_RN_VIRTUAL_BIG_SIGMA0_I1_START, SHA256_RN_VIRTUAL_BIG_SIGMA0_O2_ARITY,
    SHA256_RN_VIRTUAL_BIG_SIGMA0_O2_START, SHA256_RN_VIRTUAL_BIG_SIGMA1_I0_ARITY,
    SHA256_RN_VIRTUAL_BIG_SIGMA1_I0_START, SHA256_RN_VIRTUAL_BIG_SIGMA1_I1_ARITY,
    SHA256_RN_VIRTUAL_BIG_SIGMA1_I1_START, SHA256_RN_VIRTUAL_BIG_SIGMA1_O2_ARITY,
    SHA256_RN_VIRTUAL_BIG_SIGMA1_O2_START, Sha256CompressRnCols, Sha256RnCols, TableTrace, big_sigma0, big_sigma1,
    pext_u32,
};
use std::{borrow::Borrow, collections::BTreeMap};
use sub_protocols::{
    AuxTrace, ENDIANNESS_PIVOT_GKR, StackSectionDescriptor, StackSectionId, prove_gkr_quotient, verify_gkr_quotient,
};
use utils::{ToUsize, VarCount, finger_print, finger_print_packed, from_end};

pub const SHA256_RN_BIG_SIGMA0_I0: u32 =
    BigSigma0::I0_L | (BigSigma0::I0_H0 << BITS_PER_LIMB) | (BigSigma0::I0_H1 << 24);
pub const SHA256_RN_BIG_SIGMA0_I1: u32 =
    BigSigma0::I1_L0 | (BigSigma0::I1_L1 << 8) | (BigSigma0::I1_H << BITS_PER_LIMB);
pub const SHA256_RN_BIG_SIGMA0_I0_LOG_N_ROWS: usize = SHA256_RN_BIG_SIGMA0_I0.count_ones() as usize;
pub const SHA256_RN_BIG_SIGMA0_I1_LOG_N_ROWS: usize = SHA256_RN_BIG_SIGMA0_I1.count_ones() as usize;
pub const SHA256_RN_BIG_SIGMA0_O2_INPUT_LOG_N_ROWS: usize = BigSigma0::O2.count_ones() as usize;
pub const SHA256_RN_BIG_SIGMA0_O2_LOG_N_ROWS: usize = 2 * SHA256_RN_BIG_SIGMA0_O2_INPUT_LOG_N_ROWS;
pub const SHA256_RN_BIG_SIGMA0_I0_N_ROWS: usize = 1 << SHA256_RN_BIG_SIGMA0_I0_LOG_N_ROWS;
pub const SHA256_RN_BIG_SIGMA0_I1_N_ROWS: usize = 1 << SHA256_RN_BIG_SIGMA0_I1_LOG_N_ROWS;
pub const SHA256_RN_BIG_SIGMA0_O2_N_ROWS: usize = 1 << SHA256_RN_BIG_SIGMA0_O2_LOG_N_ROWS;
pub const SHA256_RN_BIG_SIGMA0_IO_N_COLUMNS: usize = 6;
pub const SHA256_RN_BIG_SIGMA0_IO_PADDED_N_COLUMNS: usize = 8;
pub const SHA256_RN_BIG_SIGMA0_O2_N_COLUMNS: usize = 4;
pub const SHA256_RN_BIG_SIGMA0_I0_MULT_SECTION: &str = "sha256_rn_big_sigma0_i0_mult";
pub const SHA256_RN_BIG_SIGMA0_I1_MULT_SECTION: &str = "sha256_rn_big_sigma0_i1_mult";
pub const SHA256_RN_BIG_SIGMA0_O2_MULT_SECTION: &str = "sha256_rn_big_sigma0_o2_mult";

pub const SHA256_RN_BIG_SIGMA1_I0_LOG_N_ROWS: usize = BigSigma1::I0.count_ones() as usize;
pub const SHA256_RN_BIG_SIGMA1_I1_LOG_N_ROWS: usize = BigSigma1::I1.count_ones() as usize;
pub const SHA256_RN_BIG_SIGMA1_O2_INPUT_LOG_N_ROWS: usize = BigSigma1::O2.count_ones() as usize;
pub const SHA256_RN_BIG_SIGMA1_O2_LOG_N_ROWS: usize = 2 * SHA256_RN_BIG_SIGMA1_O2_INPUT_LOG_N_ROWS;
pub const SHA256_RN_BIG_SIGMA1_I0_N_ROWS: usize = 1 << SHA256_RN_BIG_SIGMA1_I0_LOG_N_ROWS;
pub const SHA256_RN_BIG_SIGMA1_I1_N_ROWS: usize = 1 << SHA256_RN_BIG_SIGMA1_I1_LOG_N_ROWS;
pub const SHA256_RN_BIG_SIGMA1_O2_N_ROWS: usize = 1 << SHA256_RN_BIG_SIGMA1_O2_LOG_N_ROWS;
pub const SHA256_RN_BIG_SIGMA1_IO_N_COLUMNS: usize = 5;
pub const SHA256_RN_BIG_SIGMA1_IO_PADDED_N_COLUMNS: usize = 8;
pub const SHA256_RN_BIG_SIGMA1_O2_N_COLUMNS: usize = 4;
pub const SHA256_RN_BIG_SIGMA1_I0_STACKED_N_VARS: usize = SHA256_RN_BIG_SIGMA1_I0_LOG_N_ROWS + 3;
pub const SHA256_RN_BIG_SIGMA1_I1_STACKED_N_VARS: usize = SHA256_RN_BIG_SIGMA1_I1_LOG_N_ROWS + 3;
pub const SHA256_RN_BIG_SIGMA1_O2_STACKED_N_VARS: usize = SHA256_RN_BIG_SIGMA1_O2_LOG_N_ROWS + 2;
pub const SHA256_RN_BIG_SIGMA1_I0_MULT_SECTION: &str = "sha256_rn_big_sigma1_i0_mult";
pub const SHA256_RN_BIG_SIGMA1_I1_MULT_SECTION: &str = "sha256_rn_big_sigma1_i1_mult";
pub const SHA256_RN_BIG_SIGMA1_O2_MULT_SECTION: &str = "sha256_rn_big_sigma1_o2_mult";

pub const SHA256_RN_BIG_SIGMA_BATCH_N_COLUMNS: usize = 6;
pub const SHA256_RN_BIG_SIGMA_BATCH_N_AUX: usize = 6;

const SHA256_RN_FIXED_LOOKUP_TRANSCRIPT_DOMAIN: usize = 0x5A_52_4E;
const SHA256_RN_FIXED_LOOKUP_TRANSCRIPT_VERSION: usize = 6;
const SHA256_RN_BIG_SIGMA0_I0_FIXED_LOOKUP_DOMAINSEP: usize = 0xB0_10;
const SHA256_RN_BIG_SIGMA0_I1_FIXED_LOOKUP_DOMAINSEP: usize = 0xB0_11;
const SHA256_RN_BIG_SIGMA0_O2_FIXED_LOOKUP_DOMAINSEP: usize = 0xB0_02;
const SHA256_RN_BIG_SIGMA1_I0_FIXED_LOOKUP_DOMAINSEP: usize = 0xB1_10;
const SHA256_RN_BIG_SIGMA1_I1_FIXED_LOOKUP_DOMAINSEP: usize = 0xB1_11;
const SHA256_RN_BIG_SIGMA1_O2_FIXED_LOOKUP_DOMAINSEP: usize = 0xB1_02;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sha256RnFixedTableVerifierSetup {
    pub log_n_rows: usize,
    pub n_columns: usize,
    pub padded_n_columns: usize,
    pub stacked_n_vars: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sha256RnFixedLookupVerifierSetup {
    pub fixed_tables: BTreeMap<Sha256RnRelation, Sha256RnFixedTableVerifierSetup>,
}

impl Sha256RnFixedLookupVerifierSetup {
    pub fn transcript_scalars(&self) -> Vec<F> {
        let mut scalars = vec![
            F::from_usize(SHA256_RN_FIXED_LOOKUP_TRANSCRIPT_DOMAIN),
            F::from_usize(SHA256_RN_FIXED_LOOKUP_TRANSCRIPT_VERSION),
        ];
        for relation in relations() {
            scalars.push(F::from_usize(relation.domain_separator().to_usize()));
            self.fixed_tables[&relation].append_transcript_scalars(&mut scalars);
        }
        scalars
    }
}

impl Sha256RnFixedTableVerifierSetup {
    fn append_transcript_scalars(&self, scalars: &mut Vec<F>) {
        scalars.extend([
            F::from_usize(self.log_n_rows),
            F::from_usize(self.n_columns),
            F::from_usize(self.padded_n_columns),
            F::from_usize(self.stacked_n_vars),
        ]);
    }
}

#[derive(Debug, Clone)]
pub struct Sha256RnFixedLookupColumns {
    pub i0: Vec<Vec<F>>,
    pub i1: Vec<Vec<F>>,
    pub o2: Vec<Vec<F>>,
}

impl Sha256RnFixedLookupColumns {
    pub fn generate_big_sigma0() -> Self {
        Self {
            i0: generate_big_sigma0_i0_columns(),
            i1: generate_big_sigma0_i1_columns(),
            o2: generate_big_sigma0_o2_columns(),
        }
    }

    pub fn generate_big_sigma1() -> Self {
        Self {
            i0: generate_big_sigma1_i0_columns(),
            i1: generate_big_sigma1_i1_columns(),
            o2: generate_big_sigma1_o2_columns(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Sha256RnFixedTableProverSetup {
    pub columns: Vec<Vec<F>>,
}

#[derive(Debug, Clone)]
pub struct Sha256RnFixedLookupProverSetup {
    pub fixed_tables: BTreeMap<Sha256RnRelation, Sha256RnFixedTableProverSetup>,
    pub verifier: Sha256RnFixedLookupVerifierSetup,
}

impl Sha256RnFixedLookupProverSetup {
    pub fn verifier_setup(&self) -> &Sha256RnFixedLookupVerifierSetup {
        &self.verifier
    }
}

#[derive(Debug, Clone)]
pub struct MultiplicityTrace {
    pub relation: Sha256RnRelation,
    pub log_n_rows: VarCount,
    pub column: Vec<F>,
}

impl MultiplicityTrace {
    pub fn into_aux_trace(self) -> AuxTrace {
        AuxTrace {
            id: StackSectionId::Aux(match self.relation {
                Sha256RnRelation::BigSigma1I0 => SHA256_RN_BIG_SIGMA1_I0_MULT_SECTION,
                Sha256RnRelation::BigSigma1I1 => SHA256_RN_BIG_SIGMA1_I1_MULT_SECTION,
                Sha256RnRelation::BigSigma1O2 => SHA256_RN_BIG_SIGMA1_O2_MULT_SECTION,
                Sha256RnRelation::BigSigma0I0 => SHA256_RN_BIG_SIGMA0_I0_MULT_SECTION,
                Sha256RnRelation::BigSigma0I1 => SHA256_RN_BIG_SIGMA0_I1_MULT_SECTION,
                Sha256RnRelation::BigSigma0O2 => SHA256_RN_BIG_SIGMA0_O2_MULT_SECTION,
            }),
            log_n_rows: self.log_n_rows,
            columns: vec![self.column],
        }
    }
}

fn scatter_subset(mut index: usize, mut mask: u32) -> u32 {
    let mut out = 0u32;
    while mask != 0 {
        let bit = mask & mask.wrapping_neg();
        if index & 1 != 0 {
            out |= bit;
        }
        index >>= 1;
        mask ^= bit;
    }
    out
}

fn generate_big_sigma0_i0_columns() -> Vec<Vec<F>> {
    let mut columns = vec![F::zero_vec(SHA256_RN_BIG_SIGMA0_I0_N_ROWS); SHA256_RN_BIG_SIGMA0_IO_N_COLUMNS];
    for row in 0..SHA256_RN_BIG_SIGMA0_I0_N_ROWS {
        let x = scatter_subset(row, SHA256_RN_BIG_SIGMA0_I0);
        let y = big_sigma0(x);
        columns[0][row] = F::from_u32(x & BigSigma0::I0_L);
        columns[1][row] = F::from_u32((x >> BITS_PER_LIMB) & BigSigma0::I0_H0);
        columns[2][row] = F::from_u32((x >> 24) & BigSigma0::I0_H1);
        columns[3][row] = F::from_u32(y & BigSigma0::O0_L);
        columns[4][row] = F::from_u32((y >> BITS_PER_LIMB) & BigSigma0::O0_H);
        columns[5][row] = F::from_u32(pext_u32(y & BigSigma0::O2, BigSigma0::O2));
    }
    columns
}

fn generate_big_sigma0_i1_columns() -> Vec<Vec<F>> {
    let mut columns = vec![F::zero_vec(SHA256_RN_BIG_SIGMA0_I1_N_ROWS); SHA256_RN_BIG_SIGMA0_IO_N_COLUMNS];
    for row in 0..SHA256_RN_BIG_SIGMA0_I1_N_ROWS {
        let x = scatter_subset(row, SHA256_RN_BIG_SIGMA0_I1);
        let y = big_sigma0(x);
        columns[0][row] = F::from_u32(x & BigSigma0::I1_L0);
        columns[1][row] = F::from_u32((x >> 8) & BigSigma0::I1_L1);
        columns[2][row] = F::from_u32((x >> BITS_PER_LIMB) & BigSigma0::I1_H);
        columns[3][row] = F::from_u32(y & BigSigma0::O1_L);
        columns[4][row] = F::from_u32((y >> BITS_PER_LIMB) & BigSigma0::O1_H);
        columns[5][row] = F::from_u32(pext_u32(y & BigSigma0::O2, BigSigma0::O2));
    }
    columns
}

fn generate_big_sigma0_o2_columns() -> Vec<Vec<F>> {
    let mut columns = vec![F::zero_vec(SHA256_RN_BIG_SIGMA0_O2_N_ROWS); SHA256_RN_BIG_SIGMA0_O2_N_COLUMNS];
    let side_len = 1 << SHA256_RN_BIG_SIGMA0_O2_INPUT_LOG_N_ROWS;
    for left_idx in 0..side_len {
        let left = scatter_subset(left_idx, BigSigma0::O2);
        for right_idx in 0..side_len {
            let right = scatter_subset(right_idx, BigSigma0::O2);
            let row = (left_idx << SHA256_RN_BIG_SIGMA0_O2_INPUT_LOG_N_ROWS) + right_idx;
            let xor = left ^ right;
            columns[0][row] = F::from_usize(left_idx);
            columns[1][row] = F::from_usize(right_idx);
            columns[2][row] = F::from_u32(xor & LIMB_MASK);
            columns[3][row] = F::from_u32(xor >> BITS_PER_LIMB);
        }
    }
    columns
}

fn generate_big_sigma1_i0_columns() -> Vec<Vec<F>> {
    let mut columns = vec![F::zero_vec(SHA256_RN_BIG_SIGMA1_I0_N_ROWS); SHA256_RN_BIG_SIGMA1_IO_N_COLUMNS];
    for row in 0..SHA256_RN_BIG_SIGMA1_I0_N_ROWS {
        let x = scatter_subset(row, BigSigma1::I0);
        let y = big_sigma1(x);
        columns[0][row] = F::from_u32(x & BigSigma1::I0_L);
        columns[1][row] = F::from_u32((x >> BITS_PER_LIMB) & BigSigma1::I0_H);
        columns[2][row] = F::from_u32(y & BigSigma1::O0_L);
        columns[3][row] = F::from_u32((y >> BITS_PER_LIMB) & BigSigma1::O0_H);
        columns[4][row] = F::from_u32(pext_u32(y & BigSigma1::O2, BigSigma1::O2));
    }
    columns
}

fn generate_big_sigma1_i1_columns() -> Vec<Vec<F>> {
    let mut columns = vec![F::zero_vec(SHA256_RN_BIG_SIGMA1_I1_N_ROWS); SHA256_RN_BIG_SIGMA1_IO_N_COLUMNS];
    for row in 0..SHA256_RN_BIG_SIGMA1_I1_N_ROWS {
        let x = scatter_subset(row, BigSigma1::I1);
        let y = big_sigma1(x);
        columns[0][row] = F::from_u32(x & BigSigma1::I1_L);
        columns[1][row] = F::from_u32((x >> BITS_PER_LIMB) & BigSigma1::I1_H);
        columns[2][row] = F::from_u32(y & BigSigma1::O1_L);
        columns[3][row] = F::from_u32((y >> BITS_PER_LIMB) & BigSigma1::O1_H);
        columns[4][row] = F::from_u32(pext_u32(y & BigSigma1::O2, BigSigma1::O2));
    }
    columns
}

fn generate_big_sigma1_o2_columns() -> Vec<Vec<F>> {
    let mut columns = vec![F::zero_vec(SHA256_RN_BIG_SIGMA1_O2_N_ROWS); SHA256_RN_BIG_SIGMA1_O2_N_COLUMNS];
    let side_len = 1 << SHA256_RN_BIG_SIGMA1_O2_INPUT_LOG_N_ROWS;
    for left_idx in 0..side_len {
        let left = scatter_subset(left_idx, BigSigma1::O2);
        for right_idx in 0..side_len {
            let right = scatter_subset(right_idx, BigSigma1::O2);
            let row = (left_idx << SHA256_RN_BIG_SIGMA1_O2_INPUT_LOG_N_ROWS) + right_idx;
            let xor = left ^ right;
            columns[0][row] = F::from_usize(left_idx);
            columns[1][row] = F::from_usize(right_idx);
            columns[2][row] = F::from_u32(xor & LIMB_MASK);
            columns[3][row] = F::from_u32(xor >> BITS_PER_LIMB);
        }
    }
    columns
}

fn stack_fixed_columns(columns: &[Vec<F>], log_n_rows: usize, padded_n_columns: usize) -> Vec<F> {
    let n_rows = 1 << log_n_rows;
    let mut polynomial = F::zero_vec(n_rows * padded_n_columns);
    for (col_idx, col) in columns.iter().enumerate() {
        assert_eq!(col.len(), n_rows);
        let start = col_idx << log_n_rows;
        polynomial[start..start + n_rows].copy_from_slice(col);
    }
    polynomial
}

fn setup_fixed_table(
    columns: Vec<Vec<F>>,
    log_n_rows: usize,
    n_columns: usize,
    padded_n_columns: usize,
) -> (Sha256RnFixedTableProverSetup, Sha256RnFixedTableVerifierSetup) {
    let stacked_n_vars = log_n_rows + log2_strict_usize(padded_n_columns);
    let verifier = Sha256RnFixedTableVerifierSetup {
        log_n_rows,
        n_columns,
        padded_n_columns,
        stacked_n_vars,
    };
    (Sha256RnFixedTableProverSetup { columns }, verifier)
}

pub fn setup_sha256_rn_fixed_lookups(_whir_config: &WhirConfigBuilder) -> Sha256RnFixedLookupProverSetup {
    let big_sigma0_columns = Sha256RnFixedLookupColumns::generate_big_sigma0();
    let (big_sigma0_i0, big_sigma0_i0_verifier) = setup_fixed_table(
        big_sigma0_columns.i0,
        SHA256_RN_BIG_SIGMA0_I0_LOG_N_ROWS,
        SHA256_RN_BIG_SIGMA0_IO_N_COLUMNS,
        SHA256_RN_BIG_SIGMA0_IO_PADDED_N_COLUMNS,
    );
    let (big_sigma0_i1, big_sigma0_i1_verifier) = setup_fixed_table(
        big_sigma0_columns.i1,
        SHA256_RN_BIG_SIGMA0_I1_LOG_N_ROWS,
        SHA256_RN_BIG_SIGMA0_IO_N_COLUMNS,
        SHA256_RN_BIG_SIGMA0_IO_PADDED_N_COLUMNS,
    );
    let (big_sigma0_o2, big_sigma0_o2_verifier) = setup_fixed_table(
        big_sigma0_columns.o2,
        SHA256_RN_BIG_SIGMA0_O2_LOG_N_ROWS,
        SHA256_RN_BIG_SIGMA0_O2_N_COLUMNS,
        SHA256_RN_BIG_SIGMA0_O2_N_COLUMNS,
    );

    let big_sigma1_columns = Sha256RnFixedLookupColumns::generate_big_sigma1();
    let (big_sigma1_i0, big_sigma1_i0_verifier) = setup_fixed_table(
        big_sigma1_columns.i0,
        SHA256_RN_BIG_SIGMA1_I0_LOG_N_ROWS,
        SHA256_RN_BIG_SIGMA1_IO_N_COLUMNS,
        SHA256_RN_BIG_SIGMA1_IO_PADDED_N_COLUMNS,
    );
    let (big_sigma1_i1, big_sigma1_i1_verifier) = setup_fixed_table(
        big_sigma1_columns.i1,
        SHA256_RN_BIG_SIGMA1_I1_LOG_N_ROWS,
        SHA256_RN_BIG_SIGMA1_IO_N_COLUMNS,
        SHA256_RN_BIG_SIGMA1_IO_PADDED_N_COLUMNS,
    );
    let (big_sigma1_o2, big_sigma1_o2_verifier) = setup_fixed_table(
        big_sigma1_columns.o2,
        SHA256_RN_BIG_SIGMA1_O2_LOG_N_ROWS,
        SHA256_RN_BIG_SIGMA1_O2_N_COLUMNS,
        SHA256_RN_BIG_SIGMA1_O2_N_COLUMNS,
    );

    let fixed_tables = BTreeMap::from([
        (Sha256RnRelation::BigSigma1I0, big_sigma1_i0),
        (Sha256RnRelation::BigSigma1I1, big_sigma1_i1),
        (Sha256RnRelation::BigSigma1O2, big_sigma1_o2),
        (Sha256RnRelation::BigSigma0I0, big_sigma0_i0),
        (Sha256RnRelation::BigSigma0I1, big_sigma0_i1),
        (Sha256RnRelation::BigSigma0O2, big_sigma0_o2),
    ]);
    let verifier = Sha256RnFixedLookupVerifierSetup {
        fixed_tables: BTreeMap::from([
            (Sha256RnRelation::BigSigma1I0, big_sigma1_i0_verifier),
            (Sha256RnRelation::BigSigma1I1, big_sigma1_i1_verifier),
            (Sha256RnRelation::BigSigma1O2, big_sigma1_o2_verifier),
            (Sha256RnRelation::BigSigma0I0, big_sigma0_i0_verifier),
            (Sha256RnRelation::BigSigma0I1, big_sigma0_i1_verifier),
            (Sha256RnRelation::BigSigma0O2, big_sigma0_o2_verifier),
        ]),
    };

    Sha256RnFixedLookupProverSetup { fixed_tables, verifier }
}

pub fn sha256_rn_big_sigma0_i0_multiplicity_trace_layout() -> StackSectionDescriptor {
    StackSectionDescriptor {
        id: StackSectionId::Aux(SHA256_RN_BIG_SIGMA0_I0_MULT_SECTION),
        log_n_rows: SHA256_RN_BIG_SIGMA0_I0_LOG_N_ROWS,
        n_columns: 1,
    }
}

pub fn sha256_rn_big_sigma0_i1_multiplicity_trace_layout() -> StackSectionDescriptor {
    StackSectionDescriptor {
        id: StackSectionId::Aux(SHA256_RN_BIG_SIGMA0_I1_MULT_SECTION),
        log_n_rows: SHA256_RN_BIG_SIGMA0_I1_LOG_N_ROWS,
        n_columns: 1,
    }
}

pub fn sha256_rn_big_sigma0_o2_multiplicity_trace_layout() -> StackSectionDescriptor {
    StackSectionDescriptor {
        id: StackSectionId::Aux(SHA256_RN_BIG_SIGMA0_O2_MULT_SECTION),
        log_n_rows: SHA256_RN_BIG_SIGMA0_O2_LOG_N_ROWS,
        n_columns: 1,
    }
}

pub fn sha256_rn_big_sigma1_i0_multiplicity_trace_layout() -> StackSectionDescriptor {
    StackSectionDescriptor {
        id: StackSectionId::Aux(SHA256_RN_BIG_SIGMA1_I0_MULT_SECTION),
        log_n_rows: SHA256_RN_BIG_SIGMA1_I0_LOG_N_ROWS,
        n_columns: 1,
    }
}

pub fn sha256_rn_big_sigma1_i1_multiplicity_trace_layout() -> StackSectionDescriptor {
    StackSectionDescriptor {
        id: StackSectionId::Aux(SHA256_RN_BIG_SIGMA1_I1_MULT_SECTION),
        log_n_rows: SHA256_RN_BIG_SIGMA1_I1_LOG_N_ROWS,
        n_columns: 1,
    }
}

pub fn sha256_rn_big_sigma1_o2_multiplicity_trace_layout() -> StackSectionDescriptor {
    StackSectionDescriptor {
        id: StackSectionId::Aux(SHA256_RN_BIG_SIGMA1_O2_MULT_SECTION),
        log_n_rows: SHA256_RN_BIG_SIGMA1_O2_LOG_N_ROWS,
        n_columns: 1,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sha256RnRelation {
    BigSigma1I0,
    BigSigma1I1,
    BigSigma1O2,
    BigSigma0I0,
    BigSigma0I1,
    BigSigma0O2,
}

impl Sha256RnRelation {
    fn log_n_rows(self) -> usize {
        match self {
            Self::BigSigma1I0 => SHA256_RN_BIG_SIGMA1_I0_LOG_N_ROWS,
            Self::BigSigma1I1 => SHA256_RN_BIG_SIGMA1_I1_LOG_N_ROWS,
            Self::BigSigma1O2 => SHA256_RN_BIG_SIGMA1_O2_LOG_N_ROWS,
            Self::BigSigma0I0 => SHA256_RN_BIG_SIGMA0_I0_LOG_N_ROWS,
            Self::BigSigma0I1 => SHA256_RN_BIG_SIGMA0_I1_LOG_N_ROWS,
            Self::BigSigma0O2 => SHA256_RN_BIG_SIGMA0_O2_LOG_N_ROWS,
        }
    }

    fn domain_separator(self) -> F {
        F::from_usize(match self {
            Self::BigSigma1I0 => SHA256_RN_BIG_SIGMA1_I0_FIXED_LOOKUP_DOMAINSEP,
            Self::BigSigma1I1 => SHA256_RN_BIG_SIGMA1_I1_FIXED_LOOKUP_DOMAINSEP,
            Self::BigSigma1O2 => SHA256_RN_BIG_SIGMA1_O2_FIXED_LOOKUP_DOMAINSEP,
            Self::BigSigma0I0 => SHA256_RN_BIG_SIGMA0_I0_FIXED_LOOKUP_DOMAINSEP,
            Self::BigSigma0I1 => SHA256_RN_BIG_SIGMA0_I1_FIXED_LOOKUP_DOMAINSEP,
            Self::BigSigma0O2 => SHA256_RN_BIG_SIGMA0_O2_FIXED_LOOKUP_DOMAINSEP,
        })
    }

    fn multiplicity_index(self) -> usize {
        match self {
            Self::BigSigma1I0 => 0,
            Self::BigSigma1I1 => 1,
            Self::BigSigma1O2 => 2,
            Self::BigSigma0I0 => 3,
            Self::BigSigma0I1 => 4,
            Self::BigSigma0O2 => 5,
        }
    }

    fn n_fixed_columns(self) -> usize {
        match self {
            Self::BigSigma1I0 | Self::BigSigma1I1 => SHA256_RN_BIG_SIGMA1_IO_N_COLUMNS,
            Self::BigSigma1O2 => SHA256_RN_BIG_SIGMA1_O2_N_COLUMNS,
            Self::BigSigma0I0 | Self::BigSigma0I1 => SHA256_RN_BIG_SIGMA0_IO_N_COLUMNS,
            Self::BigSigma0O2 => SHA256_RN_BIG_SIGMA0_O2_N_COLUMNS,
        }
    }

    fn arity(self) -> usize {
        self.n_fixed_columns()
    }

    fn padded_n_columns(self) -> usize {
        match self {
            Self::BigSigma1I0 | Self::BigSigma1I1 => SHA256_RN_BIG_SIGMA1_IO_PADDED_N_COLUMNS,
            Self::BigSigma1O2 => SHA256_RN_BIG_SIGMA1_O2_N_COLUMNS,
            Self::BigSigma0I0 | Self::BigSigma0I1 => SHA256_RN_BIG_SIGMA0_IO_PADDED_N_COLUMNS,
            Self::BigSigma0O2 => SHA256_RN_BIG_SIGMA0_O2_N_COLUMNS,
        }
    }

    fn tie_breaker(self) -> usize {
        self.multiplicity_index()
    }

    fn virtual_start_and_arity(self) -> (usize, usize) {
        match self {
            Self::BigSigma1I0 => (
                SHA256_RN_VIRTUAL_BIG_SIGMA1_I0_START,
                SHA256_RN_VIRTUAL_BIG_SIGMA1_I0_ARITY,
            ),
            Self::BigSigma1I1 => (
                SHA256_RN_VIRTUAL_BIG_SIGMA1_I1_START,
                SHA256_RN_VIRTUAL_BIG_SIGMA1_I1_ARITY,
            ),
            Self::BigSigma1O2 => (
                SHA256_RN_VIRTUAL_BIG_SIGMA1_O2_START,
                SHA256_RN_VIRTUAL_BIG_SIGMA1_O2_ARITY,
            ),
            Self::BigSigma0I0 => (
                SHA256_RN_VIRTUAL_BIG_SIGMA0_I0_START,
                SHA256_RN_VIRTUAL_BIG_SIGMA0_I0_ARITY,
            ),
            Self::BigSigma0I1 => (
                SHA256_RN_VIRTUAL_BIG_SIGMA0_I1_START,
                SHA256_RN_VIRTUAL_BIG_SIGMA0_I1_ARITY,
            ),
            Self::BigSigma0O2 => (
                SHA256_RN_VIRTUAL_BIG_SIGMA0_O2_START,
                SHA256_RN_VIRTUAL_BIG_SIGMA0_O2_ARITY,
            ),
        }
    }
}

fn relations() -> [Sha256RnRelation; SHA256_RN_BIG_SIGMA_BATCH_N_AUX] {
    [
        Sha256RnRelation::BigSigma1I0,
        Sha256RnRelation::BigSigma1I1,
        Sha256RnRelation::BigSigma1O2,
        Sha256RnRelation::BigSigma0I0,
        Sha256RnRelation::BigSigma0I1,
        Sha256RnRelation::BigSigma0O2,
    ]
}

fn fixed_columns(setup: &Sha256RnFixedLookupProverSetup, relation: Sha256RnRelation) -> &[Vec<F>] {
    &setup.fixed_tables[&relation].columns
}

fn bit_from_scattered_mask(mask: u32, bit_position: usize, point: &[EF]) -> EF {
    debug_assert_eq!(point.len(), mask.count_ones() as usize);
    let bit = 1u32 << bit_position;
    if mask & bit == 0 {
        EF::ZERO
    } else {
        let row_bit_index = (mask & (bit - 1)).count_ones() as usize;
        point[point.len() - 1 - row_bit_index]
    }
}

fn xor2_mle(a: EF, b: EF) -> EF {
    a + b - EF::from_usize(2) * a * b
}

fn xor3_mle(a: EF, b: EF, c: EF) -> EF {
    xor2_mle(xor2_mle(a, b), c)
}

fn sigma_bit_mle(input_mask: u32, output_bit_position: usize, rotations: [usize; 3], point: &[EF]) -> EF {
    xor3_mle(
        bit_from_scattered_mask(input_mask, (output_bit_position + rotations[0]) % 32, point),
        bit_from_scattered_mask(input_mask, (output_bit_position + rotations[1]) % 32, point),
        bit_from_scattered_mask(input_mask, (output_bit_position + rotations[2]) % 32, point),
    )
}

fn projected_input_mle(input_mask: u32, column_mask: u32, shift: usize, point: &[EF]) -> EF {
    (0..32)
        .filter(|&bit| column_mask & (1u32 << bit) != 0)
        .map(|bit| EF::from_usize(1 << bit) * bit_from_scattered_mask(input_mask, shift + bit, point))
        .sum()
}

fn projected_sigma_mle(input_mask: u32, output_mask: u32, column_mask: u32, shift: usize, point: &[EF]) -> EF {
    (0..32)
        .filter(|&bit| column_mask & (1u32 << bit) != 0)
        .map(|bit| {
            EF::from_usize(1 << bit) * sigma_bit_mle(input_mask, shift + bit, sigma_rotations(output_mask), point)
        })
        .sum()
}

fn sigma_rotations(output_mask: u32) -> [usize; 3] {
    match output_mask {
        BigSigma0::O2 => [2, 13, 22],
        BigSigma1::O2 => [6, 11, 25],
        _ => unreachable!("unsupported sigma output mask"),
    }
}

fn pext_sigma_mle(input_mask: u32, output_mask: u32, point: &[EF]) -> EF {
    let mut out_bit = 0;
    let mut acc = EF::ZERO;
    for bit in 0..32 {
        if output_mask & (1u32 << bit) != 0 {
            acc += EF::from_usize(1 << out_bit) * sigma_bit_mle(input_mask, bit, sigma_rotations(output_mask), point);
            out_bit += 1;
        }
    }
    acc
}

fn scattered_index_mle(point: &[EF]) -> EF {
    (0..point.len())
        .map(|row_bit_index| EF::from_usize(1 << row_bit_index) * point[point.len() - 1 - row_bit_index])
        .sum()
}

fn o2_output_mle(o2_mask: u32, side_n_vars: usize, column_mask: u32, shift: usize, point: &[EF]) -> EF {
    debug_assert_eq!(point.len(), 2 * side_n_vars);
    let left_point = &point[..side_n_vars];
    let right_point = &point[side_n_vars..];
    (0..32)
        .filter(|&bit| column_mask & (1u32 << bit) != 0)
        .map(|bit| {
            let left = bit_from_scattered_mask(o2_mask, shift + bit, left_point);
            let right = bit_from_scattered_mask(o2_mask, shift + bit, right_point);
            EF::from_usize(1 << bit) * xor2_mle(left, right)
        })
        .sum()
}

fn eval_fixed_columns_closed_form(relation: Sha256RnRelation, point: &[EF]) -> Vec<EF> {
    match relation {
        Sha256RnRelation::BigSigma0I0 => vec![
            projected_input_mle(SHA256_RN_BIG_SIGMA0_I0, BigSigma0::I0_L, 0, point),
            projected_input_mle(SHA256_RN_BIG_SIGMA0_I0, BigSigma0::I0_H0, BITS_PER_LIMB, point),
            projected_input_mle(SHA256_RN_BIG_SIGMA0_I0, BigSigma0::I0_H1, 24, point),
            projected_sigma_mle(SHA256_RN_BIG_SIGMA0_I0, BigSigma0::O2, BigSigma0::O0_L, 0, point),
            projected_sigma_mle(
                SHA256_RN_BIG_SIGMA0_I0,
                BigSigma0::O2,
                BigSigma0::O0_H,
                BITS_PER_LIMB,
                point,
            ),
            pext_sigma_mle(SHA256_RN_BIG_SIGMA0_I0, BigSigma0::O2, point),
        ],
        Sha256RnRelation::BigSigma0I1 => vec![
            projected_input_mle(SHA256_RN_BIG_SIGMA0_I1, BigSigma0::I1_L0, 0, point),
            projected_input_mle(SHA256_RN_BIG_SIGMA0_I1, BigSigma0::I1_L1, 8, point),
            projected_input_mle(SHA256_RN_BIG_SIGMA0_I1, BigSigma0::I1_H, BITS_PER_LIMB, point),
            projected_sigma_mle(SHA256_RN_BIG_SIGMA0_I1, BigSigma0::O2, BigSigma0::O1_L, 0, point),
            projected_sigma_mle(
                SHA256_RN_BIG_SIGMA0_I1,
                BigSigma0::O2,
                BigSigma0::O1_H,
                BITS_PER_LIMB,
                point,
            ),
            pext_sigma_mle(SHA256_RN_BIG_SIGMA0_I1, BigSigma0::O2, point),
        ],
        Sha256RnRelation::BigSigma0O2 => {
            let side_n_vars = SHA256_RN_BIG_SIGMA0_O2_INPUT_LOG_N_ROWS;
            vec![
                scattered_index_mle(&point[..side_n_vars]),
                scattered_index_mle(&point[side_n_vars..]),
                o2_output_mle(BigSigma0::O2, side_n_vars, LIMB_MASK, 0, point),
                o2_output_mle(BigSigma0::O2, side_n_vars, LIMB_MASK, BITS_PER_LIMB, point),
            ]
        }
        Sha256RnRelation::BigSigma1I0 => vec![
            projected_input_mle(BigSigma1::I0, BigSigma1::I0_L, 0, point),
            projected_input_mle(BigSigma1::I0, BigSigma1::I0_H, BITS_PER_LIMB, point),
            projected_sigma_mle(BigSigma1::I0, BigSigma1::O2, BigSigma1::O0_L, 0, point),
            projected_sigma_mle(BigSigma1::I0, BigSigma1::O2, BigSigma1::O0_H, BITS_PER_LIMB, point),
            pext_sigma_mle(BigSigma1::I0, BigSigma1::O2, point),
        ],
        Sha256RnRelation::BigSigma1I1 => vec![
            projected_input_mle(BigSigma1::I1, BigSigma1::I1_L, 0, point),
            projected_input_mle(BigSigma1::I1, BigSigma1::I1_H, BITS_PER_LIMB, point),
            projected_sigma_mle(BigSigma1::I1, BigSigma1::O2, BigSigma1::O1_L, 0, point),
            projected_sigma_mle(BigSigma1::I1, BigSigma1::O2, BigSigma1::O1_H, BITS_PER_LIMB, point),
            pext_sigma_mle(BigSigma1::I1, BigSigma1::O2, point),
        ],
        Sha256RnRelation::BigSigma1O2 => {
            let side_n_vars = SHA256_RN_BIG_SIGMA1_O2_INPUT_LOG_N_ROWS;
            vec![
                scattered_index_mle(&point[..side_n_vars]),
                scattered_index_mle(&point[side_n_vars..]),
                o2_output_mle(BigSigma1::O2, side_n_vars, LIMB_MASK, 0, point),
                o2_output_mle(BigSigma1::O2, side_n_vars, LIMB_MASK, BITS_PER_LIMB, point),
            ]
        }
    }
}

fn tuple_from_trace(trace: &TableTrace, row: usize, relation: Sha256RnRelation, round: usize) -> Vec<F> {
    let mut tuple = vec![F::ZERO; relation.arity()];
    let (start, arity) = relation.virtual_start_and_arity();
    for (i, slot) in tuple.iter_mut().enumerate() {
        debug_assert!(i < arity);
        *slot = trace.virtual_columns[start + round * arity + i][row];
    }
    tuple
}

fn relation_index(relation: Sha256RnRelation, tuple: &[F]) -> usize {
    debug_assert_eq!(tuple.len(), relation.arity());
    let idx = match relation {
        Sha256RnRelation::BigSigma1I0 => {
            let low = tuple[0].to_usize() as u32;
            let high = tuple[1].to_usize() as u32;
            pext_u32(low + (high << BITS_PER_LIMB), BigSigma1::I0) as usize
        }
        Sha256RnRelation::BigSigma1I1 => {
            let low = tuple[0].to_usize() as u32;
            let high = tuple[1].to_usize() as u32;
            pext_u32(low + (high << BITS_PER_LIMB), BigSigma1::I1) as usize
        }
        Sha256RnRelation::BigSigma1O2 => {
            let left = tuple[0].to_usize();
            let right = tuple[1].to_usize();
            debug_assert!(left < (1 << SHA256_RN_BIG_SIGMA1_O2_INPUT_LOG_N_ROWS));
            debug_assert!(right < (1 << SHA256_RN_BIG_SIGMA1_O2_INPUT_LOG_N_ROWS));
            (left << SHA256_RN_BIG_SIGMA1_O2_INPUT_LOG_N_ROWS) + right
        }
        Sha256RnRelation::BigSigma0I0 => {
            let low = tuple[0].to_usize() as u32;
            let high_0 = tuple[1].to_usize() as u32;
            let high_1 = tuple[2].to_usize() as u32;
            pext_u32(
                low + (high_0 << BITS_PER_LIMB) + (high_1 << 24),
                SHA256_RN_BIG_SIGMA0_I0,
            ) as usize
        }
        Sha256RnRelation::BigSigma0I1 => {
            let low_0 = tuple[0].to_usize() as u32;
            let low_1 = tuple[1].to_usize() as u32;
            let high = tuple[2].to_usize() as u32;
            pext_u32(low_0 + (low_1 << 8) + (high << BITS_PER_LIMB), SHA256_RN_BIG_SIGMA0_I1) as usize
        }
        Sha256RnRelation::BigSigma0O2 => {
            let left = tuple[0].to_usize();
            let right = tuple[1].to_usize();
            debug_assert!(left < (1 << SHA256_RN_BIG_SIGMA0_O2_INPUT_LOG_N_ROWS));
            debug_assert!(right < (1 << SHA256_RN_BIG_SIGMA0_O2_INPUT_LOG_N_ROWS));
            (left << SHA256_RN_BIG_SIGMA0_O2_INPUT_LOG_N_ROWS) + right
        }
    };
    debug_assert!(idx < (1 << relation.log_n_rows()));
    idx
}

fn build_mult_trace(trace: &TableTrace, relation: Sha256RnRelation) -> MultiplicityTrace {
    let mut mult = F::zero_vec(1 << relation.log_n_rows());
    for row in 0..trace.columns[SHA256_RN_COL_FLAG].len() {
        if trace.columns[SHA256_RN_COL_FLAG][row].is_zero() {
            continue;
        }
        for round in 0..SHA256_RN_COMPRESS_ROUNDS {
            let tuple = tuple_from_trace(trace, row, relation, round);
            mult[relation_index(relation, &tuple)] += F::ONE;
        }
    }
    MultiplicityTrace {
        relation,
        log_n_rows: relation.log_n_rows(),
        column: mult,
    }
}

pub fn build_sha256_rn_big_sigma0_i0_mult_trace(trace: &TableTrace) -> MultiplicityTrace {
    build_mult_trace(trace, Sha256RnRelation::BigSigma0I0)
}

pub fn build_sha256_rn_big_sigma0_i1_mult_trace(trace: &TableTrace) -> MultiplicityTrace {
    build_mult_trace(trace, Sha256RnRelation::BigSigma0I1)
}

pub fn build_sha256_rn_big_sigma0_o2_mult_trace(trace: &TableTrace) -> MultiplicityTrace {
    build_mult_trace(trace, Sha256RnRelation::BigSigma0O2)
}

pub fn build_sha256_rn_big_sigma1_i0_mult_trace(trace: &TableTrace) -> MultiplicityTrace {
    build_mult_trace(trace, Sha256RnRelation::BigSigma1I0)
}

pub fn build_sha256_rn_big_sigma1_i1_mult_trace(trace: &TableTrace) -> MultiplicityTrace {
    build_mult_trace(trace, Sha256RnRelation::BigSigma1I1)
}

pub fn build_sha256_rn_big_sigma1_o2_mult_trace(trace: &TableTrace) -> MultiplicityTrace {
    build_mult_trace(trace, Sha256RnRelation::BigSigma1O2)
}

fn reconstruct_sha256_rn_compression_states(cols: &Sha256RnCols<EF>) -> [[EF; 16]; SHA256_RN_COMPRESS_ROUNDS] {
    let two_8 = EF::from_usize(1 << 8);
    let two_16 = EF::from_usize(1 << BITS_PER_LIMB);
    let mut states = [[EF::ZERO; 16]; SHA256_RN_COMPRESS_ROUNDS];
    let mut hash_buffer = [EF::ZERO; 16];
    for (word_idx, limbs) in cols.h_in.iter().enumerate() {
        hash_buffer[2 * word_idx] = limbs[0];
        hash_buffer[2 * word_idx + 1] = limbs[1];
    }

    for (round, state) in states.iter_mut().enumerate() {
        *state = hash_buffer;
        let c = &cols.compression[round];
        let sigma_1_low = c.sigma_1_o0_low + c.sigma_1_o1_low + c.sigma_1_o2_low;
        let sigma_1_high = c.sigma_1_o0_high + c.sigma_1_o1_high + c.sigma_1_o2_high;
        let ch_low = c.ch_left_i0_low + c.ch_left_i1_low + c.ch_right_i0_low + c.ch_right_i1_low;
        let ch_high = c.ch_left_i0_high + c.ch_left_i1_high + c.ch_right_i0_high + c.ch_right_i1_high;
        let sigma_0_low = c.sigma_0_o0_low + c.sigma_0_o1_low + c.sigma_0_o2_low;
        let sigma_0_high = c.sigma_0_o0_high + c.sigma_0_o1_high + c.sigma_0_o2_high;
        let maj_low = c.maj_i0_low + c.maj_i1_low_0 + c.maj_i1_low_1 * two_8;
        let maj_high = c.maj_i0_high_0 + c.maj_i0_high_1 * two_8 + c.maj_i1_high;
        let k_low = EF::from(F::from_u32(SHA256_RN_K[round] & LIMB_MASK));
        let k_high = EF::from(F::from_u32(SHA256_RN_K[round] >> BITS_PER_LIMB));
        let w_low = cols.w[round][0];
        let w_high = cols.w[round][1];

        let temp1_low = hash_buffer[14] + sigma_1_low + ch_low + k_low + w_low;
        let temp1_high = hash_buffer[15] + sigma_1_high + ch_high + k_high + w_high;
        let temp2_low = sigma_0_low + maj_low;
        let temp2_high = sigma_0_high + maj_high;

        let new_e_low = hash_buffer[6] + temp1_low - c.e_carry_low * two_16;
        let new_e_high = hash_buffer[7] + temp1_high + c.e_carry_low - c.e_carry_high * two_16;
        let new_a_low = temp1_low + temp2_low - c.a_carry_low * two_16;
        let new_a_high = temp1_high + temp2_high + c.a_carry_low - c.a_carry_high * two_16;

        hash_buffer = [
            new_a_low,
            new_a_high,
            hash_buffer[0],
            hash_buffer[1],
            hash_buffer[2],
            hash_buffer[3],
            hash_buffer[4],
            hash_buffer[5],
            new_e_low,
            new_e_high,
            hash_buffer[8],
            hash_buffer[9],
            hash_buffer[10],
            hash_buffer[11],
            hash_buffer[12],
            hash_buffer[13],
        ];
    }
    states
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LogupSection {
    Table(Sha256RnRelation),
    Request { relation: Sha256RnRelation, round: usize },
}

impl LogupSection {
    fn log_n_rows(self, log_n_rows: usize) -> usize {
        match self {
            Self::Table(relation) => relation.log_n_rows(),
            Self::Request { .. } => log_n_rows,
        }
    }

    fn order_key(self, log_n_rows: usize) -> (std::cmp::Reverse<usize>, usize) {
        let tie_breaker = match self {
            Self::Table(relation) => relation.tie_breaker(),
            Self::Request { relation, round } => 6 + round * 6 + relation.tie_breaker(),
        };
        (std::cmp::Reverse(self.log_n_rows(log_n_rows)), tie_breaker)
    }
}

fn logup_sections(log_n_rows: usize) -> Vec<LogupSection> {
    let relations = relations();
    let mut sections = relations.iter().copied().map(LogupSection::Table).collect::<Vec<_>>();
    for round in 0..SHA256_RN_COMPRESS_ROUNDS {
        for relation in relations {
            sections.push(LogupSection::Request { relation, round });
        }
    }
    sections.sort_by_key(|section| section.order_key(log_n_rows));
    sections
}

#[derive(Debug, Clone)]
pub struct Sha256RnFixedLookupStatements {
    pub rn_claim: (MultilinearPoint<EF>, BTreeMap<ColIndex, EF>),
    pub multiplicity_claims: Vec<(usize, (MultilinearPoint<EF>, BTreeMap<ColIndex, EF>))>,
}

#[allow(clippy::too_many_lines)]
pub fn prove_sha256_rn_fixed_lookup(
    prover_state: &mut impl FSProver<EF>,
    trace: &TableTrace,
    fixed_lookup_multiplicity_traces: &[MultiplicityTrace],
    setup: &Sha256RnFixedLookupProverSetup,
) -> Sha256RnFixedLookupStatements {
    let log_n_rows = trace.log_n_rows;
    let n_rows = 1 << log_n_rows;
    debug_assert_eq!(trace.columns[SHA256_RN_COL_FLAG].len(), n_rows);
    assert_eq!(fixed_lookup_multiplicity_traces.len(), SHA256_RN_BIG_SIGMA_BATCH_N_AUX);

    let sections = logup_sections(log_n_rows);
    let total_active_len = sections
        .iter()
        .map(|section| 1 << section.log_n_rows(log_n_rows))
        .sum::<usize>();
    let total_len = 1usize << log2_ceil_usize(total_active_len);
    let width = packing_width::<EF>();
    assert!(total_len.is_multiple_of(width));

    let c = prover_state.sample();
    let alphas = prover_state.sample_vec(log2_ceil_usize(SHA256_RN_BIG_SIGMA_BATCH_N_COLUMNS + 1));
    let alphas_eq_poly = eval_eq(&alphas);
    let c_packed = EFPacking::<EF>::from(c);
    let alphas_packed: Vec<EFPacking<EF>> = alphas_eq_poly.iter().map(|a| EFPacking::<EF>::from(*a)).collect();

    let pivot = sections
        .iter()
        .map(|section| section.log_n_rows(log_n_rows))
        .min()
        .unwrap()
        .min(ENDIANNESS_PIVOT_GKR);
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

    for section in &sections {
        match *section {
            LogupSection::Table(relation) => {
                let section_log_n_rows = section.log_n_rows(log_n_rows);
                let section_n_rows = 1 << section_log_n_rows;
                let mult = &fixed_lookup_multiplicity_traces[relation.multiplicity_index()].column;
                assert_eq!(mult.len(), section_n_rows);
                numerators[offset..offset + section_n_rows]
                    .chunks_exact_mut(chunk_size)
                    .enumerate()
                    .for_each(|(chunk, dst)| {
                        let src = &mult[chunk * chunk_size..][..chunk_size];
                        for (i, slot) in dst.iter_mut().enumerate() {
                            *slot = -src[i.reverse_bits() >> chunk_shift];
                        }
                    });

                let columns = fixed_columns(setup, relation);
                denominators[offset / width..][..section_n_rows / width]
                    .iter_mut()
                    .enumerate()
                    .for_each(|(p, slot)| {
                        let mut values = vec![PFPacking::<EF>::ZERO; relation.arity()];
                        for (col_idx, col) in columns.iter().take(relation.arity()).enumerate() {
                            values[col_idx] = PFPacking::<EF>::from_fn(|w| col[src_idx(p, w)]);
                        }
                        let table_contrib =
                            EFPacking::<EF>::from(*alphas_eq_poly.last().unwrap() * relation.domain_separator());
                        *slot = c_packed - finger_print_packed::<EF>(table_contrib, &values, &alphas_packed);
                    });
                offset += section_n_rows;
            }
            LogupSection::Request { relation, round } => {
                numerators[offset..offset + n_rows]
                    .chunks_exact_mut(chunk_size)
                    .enumerate()
                    .for_each(|(chunk, dst)| {
                        let src = &trace.columns[SHA256_RN_COL_FLAG][chunk * chunk_size..][..chunk_size];
                        for (i, slot) in dst.iter_mut().enumerate() {
                            *slot = src[i.reverse_bits() >> chunk_shift];
                        }
                    });
                denominators[offset / width..][..n_rows / width]
                    .iter_mut()
                    .enumerate()
                    .for_each(|(p, slot)| {
                        let mut values = vec![PFPacking::<EF>::ZERO; relation.arity()];
                        for (value_idx, value) in values.iter_mut().enumerate() {
                            *value = PFPacking::<EF>::from_fn(|w| {
                                tuple_from_trace(trace, src_idx(p, w), relation, round)[value_idx]
                            });
                        }
                        let table_contrib =
                            EFPacking::<EF>::from(*alphas_eq_poly.last().unwrap() * relation.domain_separator());
                        *slot = c_packed - finger_print_packed::<EF>(table_contrib, &values, &alphas_packed);
                    });
                offset += n_rows;
            }
        }
    }
    assert_eq!(offset, total_active_len);

    let (sum, gkr_point) = prove_gkr_quotient::<EF>(
        prover_state,
        PFPacking::<EF>::pack_slice(&numerators),
        &denominators,
        pivot,
    );
    assert_eq!(sum, EF::ZERO);

    let mut multiplicity_claims = Vec::with_capacity(SHA256_RN_BIG_SIGMA_BATCH_N_AUX);
    for relation in sections.iter().filter_map(|section| match section {
        LogupSection::Table(relation) => Some(*relation),
        LogupSection::Request { .. } => None,
    }) {
        let fixed_point = MultilinearPoint(from_end(&gkr_point.0, relation.log_n_rows()).to_vec());
        let multiplicity_idx = relation.multiplicity_index();
        let mult_eval = fixed_lookup_multiplicity_traces[multiplicity_idx]
            .column
            .evaluate(&fixed_point);
        prover_state.add_extension_scalar(mult_eval);
        multiplicity_claims.push((
            multiplicity_idx,
            (fixed_point.clone(), BTreeMap::from([(0, mult_eval)])),
        ));

        debug_assert_eq!(
            fixed_columns(setup, relation)
                .iter()
                .map(|col| col.evaluate(&fixed_point))
                .collect::<Vec<_>>(),
            eval_fixed_columns_closed_form(relation, &fixed_point.0),
            "{relation:?} closed-form fixed-column MLE does not match direct fixed-table MLE at prover GKR point"
        );
    }

    let point = MultilinearPoint(from_end(&gkr_point.0, log_n_rows).to_vec());
    let values_vec = trace
        .columns
        .iter()
        .take(NUM_SHA256_COMPRESS_RN_COLS)
        .map(|col| col.evaluate(&point))
        .collect::<Vec<_>>();
    prover_state.add_extension_scalars(&values_vec);
    let values = values_vec.iter().copied().enumerate().collect::<BTreeMap<_, _>>();

    Sha256RnFixedLookupStatements {
        rn_claim: (point, values),
        multiplicity_claims,
    }
}

#[allow(clippy::too_many_lines)]
pub fn verify_sha256_rn_fixed_lookup(
    verifier_state: &mut impl FSVerifier<EF>,
    log_n_rows: usize,
) -> ProofResult<Sha256RnFixedLookupStatements> {
    let sections = logup_sections(log_n_rows);
    let total_active_len = sections
        .iter()
        .map(|section| 1 << section.log_n_rows(log_n_rows))
        .sum::<usize>();
    let total_gkr_n_vars = log2_ceil_usize(total_active_len);

    let c = verifier_state.sample();
    let alphas = verifier_state.sample_vec(log2_ceil_usize(SHA256_RN_BIG_SIGMA_BATCH_N_COLUMNS + 1));
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

    let mut multiplicity_claims = Vec::with_capacity(SHA256_RN_BIG_SIGMA_BATCH_N_AUX);
    let mut table_mult_evals = [EF::ZERO; SHA256_RN_BIG_SIGMA_BATCH_N_AUX];
    let mut fixed_evals = relations()
        .into_iter()
        .map(|relation| vec![EF::ZERO; relation.arity()])
        .collect::<Vec<_>>();
    for relation in sections.iter().filter_map(|section| match section {
        LogupSection::Table(relation) => Some(*relation),
        LogupSection::Request { .. } => None,
    }) {
        let fixed_point = MultilinearPoint(from_end(&gkr_point.0, relation.log_n_rows()).to_vec());
        let multiplicity_idx = relation.multiplicity_index();
        let mult_eval = verifier_state.next_extension_scalar()?;
        table_mult_evals[multiplicity_idx] = mult_eval;
        fixed_evals[multiplicity_idx] = eval_fixed_columns_closed_form(relation, &fixed_point.0);
        multiplicity_claims.push((multiplicity_idx, (fixed_point, BTreeMap::from([(0, mult_eval)]))));
    }

    let rn_point = MultilinearPoint(from_end(&gkr_point.0, log_n_rows).to_vec());
    let rn_eval_vec = verifier_state.next_extension_scalars_vec(NUM_SHA256_COMPRESS_RN_COLS)?;
    let rn_cols: &Sha256CompressRnCols<EF> = rn_eval_vec.as_slice().borrow();
    let rn_states = reconstruct_sha256_rn_compression_states(&rn_cols.sha);
    let rn_values = rn_eval_vec.iter().copied().enumerate().collect::<BTreeMap<_, _>>();

    let mut retrieved_numerators_value = EF::ZERO;
    let mut retrieved_denominators_value = EF::ZERO;
    let mut offset = 0;
    for section in &sections {
        let log_n_rows = section.log_n_rows(log_n_rows);
        let n_rows = 1 << log_n_rows;
        let pref = pref_at(offset, log_n_rows);
        match *section {
            LogupSection::Table(relation) => {
                let multiplicity_idx = relation.multiplicity_index();
                retrieved_numerators_value -= pref * table_mult_evals[multiplicity_idx];
                retrieved_denominators_value += pref
                    * (c - finger_print(
                        relation.domain_separator(),
                        &fixed_evals[multiplicity_idx],
                        &alphas_eq_poly,
                    ));
            }
            LogupSection::Request { relation, round } => {
                let c_round = &rn_cols.sha.compression[round];
                let two_8 = EF::from_usize(1 << 8);
                let values = match relation {
                    Sha256RnRelation::BigSigma1I0 => vec![
                        c_round.e_i0_low,
                        c_round.e_i0_high,
                        c_round.sigma_1_o0_low,
                        c_round.sigma_1_o0_high,
                        c_round.sigma_1_o20_pext,
                    ],
                    Sha256RnRelation::BigSigma1I1 => vec![
                        rn_states[round][8] - c_round.e_i0_low,
                        rn_states[round][9] - c_round.e_i0_high,
                        c_round.sigma_1_o1_low,
                        c_round.sigma_1_o1_high,
                        c_round.sigma_1_o21_pext,
                    ],
                    Sha256RnRelation::BigSigma1O2 => vec![
                        c_round.sigma_1_o20_pext,
                        c_round.sigma_1_o21_pext,
                        c_round.sigma_1_o2_low,
                        c_round.sigma_1_o2_high,
                    ],
                    Sha256RnRelation::BigSigma0I0 => vec![
                        rn_states[round][0] - c_round.a_i1_low_0 - c_round.a_i1_low_1 * two_8,
                        c_round.a_i0_high_0,
                        c_round.a_i0_high_1,
                        c_round.sigma_0_o0_low,
                        c_round.sigma_0_o0_high,
                        c_round.sigma_0_o20_pext,
                    ],
                    Sha256RnRelation::BigSigma0I1 => vec![
                        c_round.a_i1_low_0,
                        c_round.a_i1_low_1,
                        rn_states[round][1] - c_round.a_i0_high_0 - c_round.a_i0_high_1 * two_8,
                        c_round.sigma_0_o1_low,
                        c_round.sigma_0_o1_high,
                        c_round.sigma_0_o21_pext,
                    ],
                    Sha256RnRelation::BigSigma0O2 => vec![
                        c_round.sigma_0_o20_pext,
                        c_round.sigma_0_o21_pext,
                        c_round.sigma_0_o2_low,
                        c_round.sigma_0_o2_high,
                    ],
                };
                retrieved_numerators_value += pref * rn_cols.flag;
                retrieved_denominators_value +=
                    pref * (c - finger_print(relation.domain_separator(), &values, &alphas_eq_poly));
            }
        }
        offset += n_rows;
    }

    retrieved_denominators_value += mle_of_zeros_then_ones(offset, &gkr_point.0);
    if retrieved_numerators_value != numerators_value || retrieved_denominators_value != denominators_value {
        return Err(ProofError::InvalidProof);
    }

    Ok(Sha256RnFixedLookupStatements {
        rn_claim: (rn_point, rn_values),
        multiplicity_claims,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::default_whir_config;
    use lean_vm::{
        SHA256_RN_COL_STATE_LIMBS_START, SHA256_RN_COL_W_START, SHA256_RN_K, SHA256_RN_SCHEDULE_EXTENSIONS,
        SHA256_RN_U32_LIMBS, Sha256RnCompressionRoundCols, Sha256RnSchedulingRoundCols, Table,
        generate_sha256_compress_rn_witness, sha256_compress_rn_trace_row,
    };
    use std::mem::size_of;

    fn one_row_trace(active: bool) -> TableTrace {
        let witness = generate_sha256_compress_rn_witness(lean_vm::SHA256_IV, lean_vm::SHA256_ZERO_BLOCK);
        let mut row = sha256_compress_rn_trace_row(
            F::from_bool(active),
            F::ZERO,
            F::ZERO,
            F::ZERO,
            witness.h_in,
            witness.block,
        );
        row[SHA256_RN_COL_FLAG] = F::from_bool(active);
        table_trace_from_row_and_virtual(row, witness.virtual_lookup_values)
    }

    fn table_trace_from_row_and_virtual(row: Vec<F>, virtual_values: Vec<F>) -> TableTrace {
        let columns = row.into_iter().map(|value| vec![value]).collect::<Vec<_>>();
        let virtual_columns = virtual_values.into_iter().map(|value| vec![value]).collect::<Vec<_>>();
        TableTrace {
            columns,
            virtual_columns,
            non_padded_n_rows: 1,
            log_n_rows: 0,
        }
    }

    fn rn_trace_from_row(row: Vec<F>, virtual_values: Vec<F>) -> BTreeMap<Table, TableTrace> {
        BTreeMap::from([(
            Table::sha256_compress_rn(),
            table_trace_from_row_and_virtual(row, virtual_values),
        )])
    }

    fn compression_start_and_width() -> (usize, usize) {
        let scheduling_start = SHA256_RN_COL_W_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_U32_LIMBS;
        let scheduling_round_width = size_of::<Sha256RnSchedulingRoundCols<u8>>();
        let compression_start = scheduling_start + SHA256_RN_SCHEDULE_EXTENSIONS * scheduling_round_width;
        let compression_round_width = size_of::<Sha256RnCompressionRoundCols<u8>>();
        (compression_start, compression_round_width)
    }

    #[test]
    fn big_sigma0_fixed_columns_match_indexing() {
        let columns = Sha256RnFixedLookupColumns::generate_big_sigma0();
        assert_eq!(columns.i0.len(), SHA256_RN_BIG_SIGMA0_IO_N_COLUMNS);
        assert_eq!(columns.i1.len(), SHA256_RN_BIG_SIGMA0_IO_N_COLUMNS);
        assert_eq!(columns.o2.len(), SHA256_RN_BIG_SIGMA0_O2_N_COLUMNS);
        assert!(columns.i0.iter().all(|col| col.len() == SHA256_RN_BIG_SIGMA0_I0_N_ROWS));
        assert!(columns.i1.iter().all(|col| col.len() == SHA256_RN_BIG_SIGMA0_I1_N_ROWS));
        assert!(columns.o2.iter().all(|col| col.len() == SHA256_RN_BIG_SIGMA0_O2_N_ROWS));

        let i0_row = 17;
        let i0_x = scatter_subset(i0_row, SHA256_RN_BIG_SIGMA0_I0);
        let i0_y = big_sigma0(i0_x);
        assert_eq!(columns.i0[0][i0_row], F::from_u32(i0_x & BigSigma0::I0_L));
        assert_eq!(
            columns.i0[1][i0_row],
            F::from_u32((i0_x >> BITS_PER_LIMB) & BigSigma0::I0_H0)
        );
        assert_eq!(columns.i0[2][i0_row], F::from_u32((i0_x >> 24) & BigSigma0::I0_H1));
        assert_eq!(columns.i0[3][i0_row], F::from_u32(i0_y & BigSigma0::O0_L));
        assert_eq!(
            columns.i0[4][i0_row],
            F::from_u32((i0_y >> BITS_PER_LIMB) & BigSigma0::O0_H)
        );
        assert_eq!(
            columns.i0[5][i0_row],
            F::from_u32(pext_u32(i0_y & BigSigma0::O2, BigSigma0::O2))
        );

        let i1_row = 23;
        let i1_x = scatter_subset(i1_row, SHA256_RN_BIG_SIGMA0_I1);
        let i1_y = big_sigma0(i1_x);
        assert_eq!(columns.i1[0][i1_row], F::from_u32(i1_x & BigSigma0::I1_L0));
        assert_eq!(columns.i1[1][i1_row], F::from_u32((i1_x >> 8) & BigSigma0::I1_L1));
        assert_eq!(
            columns.i1[2][i1_row],
            F::from_u32((i1_x >> BITS_PER_LIMB) & BigSigma0::I1_H)
        );
        assert_eq!(columns.i1[3][i1_row], F::from_u32(i1_y & BigSigma0::O1_L));
        assert_eq!(
            columns.i1[4][i1_row],
            F::from_u32((i1_y >> BITS_PER_LIMB) & BigSigma0::O1_H)
        );
        assert_eq!(
            columns.i1[5][i1_row],
            F::from_u32(pext_u32(i1_y & BigSigma0::O2, BigSigma0::O2))
        );

        let left_idx = 5;
        let right_idx = 9;
        let o2_row = (left_idx << SHA256_RN_BIG_SIGMA0_O2_INPUT_LOG_N_ROWS) + right_idx;
        let left = scatter_subset(left_idx, BigSigma0::O2);
        let right = scatter_subset(right_idx, BigSigma0::O2);
        let xor = left ^ right;
        assert_eq!(columns.o2[0][o2_row], F::from_usize(left_idx));
        assert_eq!(columns.o2[1][o2_row], F::from_usize(right_idx));
        assert_eq!(columns.o2[2][o2_row], F::from_u32(xor & LIMB_MASK));
        assert_eq!(columns.o2[3][o2_row], F::from_u32(xor >> BITS_PER_LIMB));
    }

    #[test]
    fn big_sigma0_closed_form_mle_matches_direct_mle() {
        let columns = Sha256RnFixedLookupColumns::generate_big_sigma0();
        let cases = [
            (Sha256RnRelation::BigSigma0I0, columns.i0.as_slice()),
            (Sha256RnRelation::BigSigma0I1, columns.i1.as_slice()),
            (Sha256RnRelation::BigSigma0O2, columns.o2.as_slice()),
        ];

        for (relation, columns) in cases {
            let point = (0..relation.log_n_rows())
                .map(|i| EF::from_usize(17 * i + 5))
                .collect::<Vec<_>>();
            let closed_form = eval_fixed_columns_closed_form(relation, &point);
            assert_eq!(closed_form.len(), columns.len());

            for (col_idx, (column, closed)) in columns.iter().zip(closed_form.iter()).enumerate() {
                let direct = column.evaluate(&MultilinearPoint(point.clone()));
                println!("{relation:?} col {col_idx}: direct={direct:?}, closed_form={closed:?}");
                assert_eq!(direct, *closed);
            }
        }
    }

    #[test]
    fn big_sigma1_closed_form_mle_matches_direct_mle() {
        let columns = Sha256RnFixedLookupColumns::generate_big_sigma1();
        let cases = [
            (Sha256RnRelation::BigSigma1I0, columns.i0.as_slice()),
            (Sha256RnRelation::BigSigma1I1, columns.i1.as_slice()),
            (Sha256RnRelation::BigSigma1O2, columns.o2.as_slice()),
        ];

        for (relation, columns) in cases {
            let point = (0..relation.log_n_rows())
                .map(|i| EF::from_usize(19 * i + 7))
                .collect::<Vec<_>>();
            let closed_form = eval_fixed_columns_closed_form(relation, &point);
            assert_eq!(closed_form.len(), columns.len());

            for (col_idx, (column, closed)) in columns.iter().zip(closed_form.iter()).enumerate() {
                let direct = column.evaluate(&MultilinearPoint(point.clone()));
                println!("{relation:?} col {col_idx}: direct={direct:?}, closed_form={closed:?}");
                assert_eq!(direct, *closed);
            }
        }
    }

    #[test]
    fn big_sigma1_fixed_columns_match_indexing() {
        let columns = Sha256RnFixedLookupColumns::generate_big_sigma1();
        assert_eq!(columns.i0.len(), SHA256_RN_BIG_SIGMA1_IO_N_COLUMNS);
        assert_eq!(columns.i1.len(), SHA256_RN_BIG_SIGMA1_IO_N_COLUMNS);
        assert_eq!(columns.o2.len(), SHA256_RN_BIG_SIGMA1_O2_N_COLUMNS);
        assert!(columns.i0.iter().all(|col| col.len() == SHA256_RN_BIG_SIGMA1_I0_N_ROWS));
        assert!(columns.i1.iter().all(|col| col.len() == SHA256_RN_BIG_SIGMA1_I1_N_ROWS));
        assert!(columns.o2.iter().all(|col| col.len() == SHA256_RN_BIG_SIGMA1_O2_N_ROWS));

        let i0_row = 17;
        let i0_x = scatter_subset(i0_row, BigSigma1::I0);
        let i0_y = big_sigma1(i0_x);
        assert_eq!(columns.i0[0][i0_row], F::from_u32(i0_x & BigSigma1::I0_L));
        assert_eq!(
            columns.i0[1][i0_row],
            F::from_u32((i0_x >> BITS_PER_LIMB) & BigSigma1::I0_H)
        );
        assert_eq!(columns.i0[2][i0_row], F::from_u32(i0_y & BigSigma1::O0_L));
        assert_eq!(
            columns.i0[3][i0_row],
            F::from_u32((i0_y >> BITS_PER_LIMB) & BigSigma1::O0_H)
        );
        assert_eq!(
            columns.i0[4][i0_row],
            F::from_u32(pext_u32(i0_y & BigSigma1::O2, BigSigma1::O2))
        );

        let i1_row = 23;
        let i1_x = scatter_subset(i1_row, BigSigma1::I1);
        let i1_y = big_sigma1(i1_x);
        assert_eq!(columns.i1[0][i1_row], F::from_u32(i1_x & BigSigma1::I1_L));
        assert_eq!(
            columns.i1[1][i1_row],
            F::from_u32((i1_x >> BITS_PER_LIMB) & BigSigma1::I1_H)
        );
        assert_eq!(columns.i1[2][i1_row], F::from_u32(i1_y & BigSigma1::O1_L));
        assert_eq!(
            columns.i1[3][i1_row],
            F::from_u32((i1_y >> BITS_PER_LIMB) & BigSigma1::O1_H)
        );
        assert_eq!(
            columns.i1[4][i1_row],
            F::from_u32(pext_u32(i1_y & BigSigma1::O2, BigSigma1::O2))
        );

        let left_idx = 5;
        let right_idx = 9;
        let o2_row = (left_idx << SHA256_RN_BIG_SIGMA1_O2_INPUT_LOG_N_ROWS) + right_idx;
        let left = scatter_subset(left_idx, BigSigma1::O2);
        let right = scatter_subset(right_idx, BigSigma1::O2);
        let xor = left ^ right;
        assert_eq!(columns.o2[0][o2_row], F::from_usize(left_idx));
        assert_eq!(columns.o2[1][o2_row], F::from_usize(right_idx));
        assert_eq!(columns.o2[2][o2_row], F::from_u32(xor & LIMB_MASK));
        assert_eq!(columns.o2[3][o2_row], F::from_u32(xor >> BITS_PER_LIMB));
    }

    #[test]
    fn sha256_rn_fixed_lookup_setup_is_deterministic() {
        let whir_config = default_whir_config(1);
        let setup_a = setup_sha256_rn_fixed_lookups(&whir_config);
        let setup_b = setup_sha256_rn_fixed_lookups(&whir_config);
        assert_eq!(setup_a.verifier, setup_b.verifier);
    }

    #[test]
    fn sha256_rn_big_sigma0_virtual_columns_have_expected_requests() {
        let trace = one_row_trace(true);
        assert_eq!(
            trace.virtual_columns.len(),
            lean_vm::NUM_SHA256_COMPRESS_RN_VIRTUAL_COLS
        );
    }

    #[test]
    fn sha256_rn_big_sigma0_multiplicity_one_row_has_64_requests() {
        let trace = one_row_trace(true);
        let i0 = build_sha256_rn_big_sigma0_i0_mult_trace(&trace);
        let i1 = build_sha256_rn_big_sigma0_i1_mult_trace(&trace);
        let o2 = build_sha256_rn_big_sigma0_o2_mult_trace(&trace);
        let total = |trace: &MultiplicityTrace| trace.column.iter().map(|x| x.to_usize()).sum::<usize>();
        assert_eq!(total(&i0), SHA256_RN_COMPRESS_ROUNDS);
        assert_eq!(total(&i1), SHA256_RN_COMPRESS_ROUNDS);
        assert_eq!(total(&o2), SHA256_RN_COMPRESS_ROUNDS);
    }

    #[test]
    fn sha256_rn_big_sigma0_multiplicity_inactive_row_is_zero() {
        let trace = one_row_trace(false);
        let i0 = build_sha256_rn_big_sigma0_i0_mult_trace(&trace);
        let i1 = build_sha256_rn_big_sigma0_i1_mult_trace(&trace);
        let o2 = build_sha256_rn_big_sigma0_o2_mult_trace(&trace);
        assert!(i0.column.iter().all(|x| *x == F::ZERO));
        assert!(i1.column.iter().all(|x| *x == F::ZERO));
        assert!(o2.column.iter().all(|x| *x == F::ZERO));
    }

    #[test]
    fn sha256_rn_big_sigma0_virtual_columns_use_rolling_a() {
        let h_in = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
        ];
        let block = [0u32; 16];
        let witness = generate_sha256_compress_rn_witness(h_in, block);
        let row = sha256_compress_rn_trace_row(F::ONE, F::ZERO, F::ZERO, F::ZERO, h_in, block);
        let traces = rn_trace_from_row(row, witness.virtual_lookup_values);
        let rn_trace = &traces[&Table::sha256_compress_rn()];
        let (compression_start, compression_width) = compression_start_and_width();
        let c0 = compression_start;
        let c1 = compression_start + compression_width;
        let col = |idx: usize| rn_trace.columns[idx][0];

        let two_8 = F::from_usize(1 << 8);
        let two_16 = F::from_usize(1 << BITS_PER_LIMB);
        let a_low_0 = col(SHA256_RN_COL_STATE_LIMBS_START);
        let a_high_0 = col(SHA256_RN_COL_STATE_LIMBS_START + 1);
        assert_eq!(
            tuple_from_trace(rn_trace, 0, Sha256RnRelation::BigSigma0I0, 0)[0],
            a_low_0 - col(c0 + 24) - col(c0 + 25) * two_8
        );
        assert_eq!(
            tuple_from_trace(rn_trace, 0, Sha256RnRelation::BigSigma0I1, 0)[2],
            a_high_0 - col(c0 + 22) - col(c0 + 23) * two_8
        );

        let h_low_0 = col(SHA256_RN_COL_STATE_LIMBS_START + 14);
        let h_high_0 = col(SHA256_RN_COL_STATE_LIMBS_START + 15);
        let sigma_1_low_0 = col(c0 + 2) + col(c0 + 5) + col(c0 + 8);
        let sigma_1_high_0 = col(c0 + 3) + col(c0 + 6) + col(c0 + 9);
        let ch_left_low_0 = col(c0 + 12) + col(c0 + 14);
        let ch_left_high_0 = col(c0 + 13) + col(c0 + 15);
        let ch_right_low_0 = col(c0 + 18) + col(c0 + 20);
        let ch_right_high_0 = col(c0 + 19) + col(c0 + 21);
        let temp1_low_0 = h_low_0
            + sigma_1_low_0
            + ch_left_low_0
            + ch_right_low_0
            + F::from_u32(SHA256_RN_K[0] & LIMB_MASK)
            + col(SHA256_RN_COL_W_START);
        let temp1_high_0 = h_high_0
            + sigma_1_high_0
            + ch_left_high_0
            + ch_right_high_0
            + F::from_u32(SHA256_RN_K[0] >> BITS_PER_LIMB)
            + col(SHA256_RN_COL_W_START + 1);
        let sigma_0_low_0 = col(c0 + 26) + col(c0 + 29) + col(c0 + 32);
        let sigma_0_high_0 = col(c0 + 27) + col(c0 + 30) + col(c0 + 33);
        let maj_low_0 = col(c0 + 42) + col(c0 + 45) + col(c0 + 46) * two_8;
        let maj_high_0 = col(c0 + 43) + col(c0 + 44) * two_8 + col(c0 + 47);
        let temp2_low_0 = sigma_0_low_0 + maj_low_0;
        let temp2_high_0 = sigma_0_high_0 + maj_high_0;
        let new_a_low_0 = temp1_low_0 + temp2_low_0 - col(c0 + 50) * two_16;
        let new_a_high_0 = temp1_high_0 + temp2_high_0 + col(c0 + 50) - col(c0 + 51) * two_16;

        assert_eq!(
            tuple_from_trace(rn_trace, 0, Sha256RnRelation::BigSigma0I0, 1)[0],
            new_a_low_0 - col(c1 + 24) - col(c1 + 25) * two_8
        );
        assert_eq!(
            tuple_from_trace(rn_trace, 0, Sha256RnRelation::BigSigma0I1, 1)[2],
            new_a_high_0 - col(c1 + 22) - col(c1 + 23) * two_8
        );
    }

    #[test]
    fn sha256_rn_big_sigma1_virtual_columns_have_expected_requests() {
        let trace = one_row_trace(true);
        assert_eq!(
            trace.virtual_columns.len(),
            lean_vm::NUM_SHA256_COMPRESS_RN_VIRTUAL_COLS
        );
    }

    #[test]
    fn sha256_rn_big_sigma1_multiplicity_one_row_has_64_requests() {
        let trace = one_row_trace(true);
        let i0 = build_sha256_rn_big_sigma1_i0_mult_trace(&trace);
        let i1 = build_sha256_rn_big_sigma1_i1_mult_trace(&trace);
        let o2 = build_sha256_rn_big_sigma1_o2_mult_trace(&trace);
        let total = |trace: &MultiplicityTrace| trace.column.iter().map(|x| x.to_usize()).sum::<usize>();
        assert_eq!(total(&i0), SHA256_RN_COMPRESS_ROUNDS);
        assert_eq!(total(&i1), SHA256_RN_COMPRESS_ROUNDS);
        assert_eq!(total(&o2), SHA256_RN_COMPRESS_ROUNDS);
    }

    #[test]
    fn sha256_rn_big_sigma1_multiplicity_inactive_row_is_zero() {
        let trace = one_row_trace(false);
        let i0 = build_sha256_rn_big_sigma1_i0_mult_trace(&trace);
        let i1 = build_sha256_rn_big_sigma1_i1_mult_trace(&trace);
        let o2 = build_sha256_rn_big_sigma1_o2_mult_trace(&trace);
        assert!(i0.column.iter().all(|x| *x == F::ZERO));
        assert!(i1.column.iter().all(|x| *x == F::ZERO));
        assert!(o2.column.iter().all(|x| *x == F::ZERO));
    }

    #[test]
    fn sha256_rn_big_sigma1_virtual_columns_use_rolling_e() {
        let h_in = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
        ];
        let block = [0u32; 16];
        let witness = generate_sha256_compress_rn_witness(h_in, block);
        let row = sha256_compress_rn_trace_row(F::ONE, F::ZERO, F::ZERO, F::ZERO, h_in, block);
        let traces = rn_trace_from_row(row, witness.virtual_lookup_values);
        let rn_trace = &traces[&Table::sha256_compress_rn()];
        let (compression_start, compression_width) = compression_start_and_width();
        let c0 = compression_start;
        let c1 = compression_start + compression_width;
        let col = |idx: usize| rn_trace.columns[idx][0];

        let e_low_0 = col(SHA256_RN_COL_STATE_LIMBS_START + 8);
        let e_high_0 = col(SHA256_RN_COL_STATE_LIMBS_START + 9);
        assert_eq!(
            tuple_from_trace(rn_trace, 0, Sha256RnRelation::BigSigma1I1, 0)[0],
            e_low_0 - col(c0)
        );
        assert_eq!(
            tuple_from_trace(rn_trace, 0, Sha256RnRelation::BigSigma1I1, 0)[1],
            e_high_0 - col(c0 + 1)
        );

        let two_16 = F::from_usize(1 << BITS_PER_LIMB);
        let d_low_0 = col(SHA256_RN_COL_STATE_LIMBS_START + 6);
        let d_high_0 = col(SHA256_RN_COL_STATE_LIMBS_START + 7);
        let h_low_0 = col(SHA256_RN_COL_STATE_LIMBS_START + 14);
        let h_high_0 = col(SHA256_RN_COL_STATE_LIMBS_START + 15);
        let sigma_1_low_0 = col(c0 + 2) + col(c0 + 5) + col(c0 + 8);
        let sigma_1_high_0 = col(c0 + 3) + col(c0 + 6) + col(c0 + 9);
        let ch_left_low_0 = col(c0 + 12) + col(c0 + 14);
        let ch_left_high_0 = col(c0 + 13) + col(c0 + 15);
        let ch_right_low_0 = col(c0 + 18) + col(c0 + 20);
        let ch_right_high_0 = col(c0 + 19) + col(c0 + 21);
        let temp1_low_0 = h_low_0
            + sigma_1_low_0
            + ch_left_low_0
            + ch_right_low_0
            + F::from_u32(SHA256_RN_K[0] & LIMB_MASK)
            + col(SHA256_RN_COL_W_START);
        let temp1_high_0 = h_high_0
            + sigma_1_high_0
            + ch_left_high_0
            + ch_right_high_0
            + F::from_u32(SHA256_RN_K[0] >> BITS_PER_LIMB)
            + col(SHA256_RN_COL_W_START + 1);
        let new_e_low_0 = d_low_0 + temp1_low_0 - col(c0 + 48) * two_16;
        let new_e_high_0 = d_high_0 + temp1_high_0 + col(c0 + 48) - col(c0 + 49) * two_16;

        assert_eq!(
            tuple_from_trace(rn_trace, 0, Sha256RnRelation::BigSigma1I1, 1)[0],
            new_e_low_0 - col(c1)
        );
        assert_eq!(
            tuple_from_trace(rn_trace, 0, Sha256RnRelation::BigSigma1I1, 1)[1],
            new_e_high_0 - col(c1 + 1)
        );
    }
}
