use std::collections::BTreeMap;

use crate::sha256_rn_fixed_lookups::{
    Sha256RnFixedLookupProverParams, build_sha256_rn_fixed_lookup_multiplicity_traces, prove_sha256_rn_fixed_lookup,
    sha256_rn_fixed_lookup_transcript_scalars,
};
use crate::*;
use backend::merkle::Sha256Digest;
use lean_vm::*;

use serde::{Deserialize, Serialize};
use sub_protocols::*;
use tracing::info_span;
use utils::ansi::Colorize;
use utils::{build_prover_state, build_prover_state_sha2, from_end};

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound(
    serialize = "Proof<F, Digest>: Serialize",
    deserialize = "Proof<F, Digest>: Deserialize<'de>"
))]
pub struct ExecutionProof<Digest = [F; DIGEST_ELEMS]> {
    pub proof: Proof<F, Digest>,
    // benchmark / debug purpose
    #[serde(skip, default)]
    pub metadata: Option<ExecutionMetadata>,
}

trait ExecutionProverBackend<P>
where
    P: FSProver<EF>,
{
    type InnerWitness;

    fn stack_polynomials_and_commit_legacy(
        prover_state: &mut P,
        whir_config: &WhirConfigBuilder,
        memory: &[F],
        memory_acc: &[F],
        bytecode_acc: &[F],
        traces: &BTreeMap<Table, TableTrace>,
    ) -> StackedPcsWitness<Self::InnerWitness>;

    fn stack_polynomials_and_commit(
        prover_state: &mut P,
        whir_config: &WhirConfigBuilder,
        memory: &[F],
        memory_acc: &[F],
        bytecode_acc: &[F],
        traces: &BTreeMap<Table, TableTrace>,
        aux_traces: &[AuxTrace],
    ) -> StackedPcsWitnessWithLayout<Self::InnerWitness>;

    fn prove_whir(
        whir_config: &WhirConfig<EF>,
        prover_state: &mut P,
        statements: Vec<SparseStatement<EF>>,
        witness: Self::InnerWitness,
        polynomial: &MleRef<'_, EF>,
    );
}

struct PoseidonExecutionBackend;

impl<P> ExecutionProverBackend<P> for PoseidonExecutionBackend
where
    P: FSProver<EF, Digest = [F; DIGEST_ELEMS]>,
{
    type InnerWitness = Witness<EF>;

    fn stack_polynomials_and_commit_legacy(
        prover_state: &mut P,
        whir_config: &WhirConfigBuilder,
        memory: &[F],
        memory_acc: &[F],
        bytecode_acc: &[F],
        traces: &BTreeMap<Table, TableTrace>,
    ) -> StackedPcsWitness<Self::InnerWitness> {
        stack_polynomials_and_commit(prover_state, whir_config, memory, memory_acc, bytecode_acc, traces)
    }

    fn stack_polynomials_and_commit(
        prover_state: &mut P,
        whir_config: &WhirConfigBuilder,
        memory: &[F],
        memory_acc: &[F],
        bytecode_acc: &[F],
        traces: &BTreeMap<Table, TableTrace>,
        aux_traces: &[AuxTrace],
    ) -> StackedPcsWitnessWithLayout<Self::InnerWitness> {
        stack_polynomials_and_commit_with_aux(
            prover_state,
            whir_config,
            memory,
            memory_acc,
            bytecode_acc,
            traces,
            aux_traces,
        )
    }

    fn prove_whir(
        whir_config: &WhirConfig<EF>,
        prover_state: &mut P,
        statements: Vec<SparseStatement<EF>>,
        witness: Self::InnerWitness,
        polynomial: &MleRef<'_, EF>,
    ) {
        whir_config.prove(prover_state, statements, witness, polynomial);
    }
}

struct Sha2ExecutionBackend;

impl<P> ExecutionProverBackend<P> for Sha2ExecutionBackend
where
    P: FSProver<EF, Digest = Sha256Digest>,
{
    type InnerWitness = Witness2<EF>;

    fn stack_polynomials_and_commit_legacy(
        prover_state: &mut P,
        whir_config: &WhirConfigBuilder,
        memory: &[F],
        memory_acc: &[F],
        bytecode_acc: &[F],
        traces: &BTreeMap<Table, TableTrace>,
    ) -> StackedPcsWitness<Self::InnerWitness> {
        stack_polynomials_and_commit_sha2(prover_state, whir_config, memory, memory_acc, bytecode_acc, traces)
    }

    fn stack_polynomials_and_commit(
        prover_state: &mut P,
        whir_config: &WhirConfigBuilder,
        memory: &[F],
        memory_acc: &[F],
        bytecode_acc: &[F],
        traces: &BTreeMap<Table, TableTrace>,
        aux_traces: &[AuxTrace],
    ) -> StackedPcsWitnessWithLayout<Self::InnerWitness> {
        stack_polynomials_and_commit_sha2_with_aux(
            prover_state,
            whir_config,
            memory,
            memory_acc,
            bytecode_acc,
            traces,
            aux_traces,
        )
    }

    fn prove_whir(
        whir_config: &WhirConfig<EF>,
        prover_state: &mut P,
        statements: Vec<SparseStatement<EF>>,
        witness: Self::InnerWitness,
        polynomial: &MleRef<'_, EF>,
    ) {
        whir_config.prove2(prover_state, statements, witness, polynomial);
    }
}

pub fn prove_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
) -> Result<ExecutionProof, ProverError> {
    prove_execution_with::<_, PoseidonExecutionBackend, _>(
        bytecode,
        public_input,
        witness,
        whir_config,
        vm_profiler,
        build_prover_state(),
        |prover_state| prover_state.into_proof(),
        None,
    )
}

pub fn prove_execution_sha2(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
) -> Result<ExecutionProof<Sha256Digest>, ProverError> {
    prove_execution_with::<_, Sha2ExecutionBackend, _>(
        bytecode,
        public_input,
        witness,
        whir_config,
        vm_profiler,
        build_prover_state_sha2(),
        |prover_state| prover_state.into_proof(),
        None,
    )
}

pub fn prove_execution_with_sha256_rn_fixed_lookups(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
    fixed_lookups: &Sha256RnFixedLookupProverParams,
) -> Result<ExecutionProof, ProverError> {
    prove_execution_with::<_, PoseidonExecutionBackend, _>(
        bytecode,
        public_input,
        witness,
        whir_config,
        vm_profiler,
        build_prover_state(),
        |prover_state| prover_state.into_proof(),
        Some(fixed_lookups),
    )
}

pub fn prove_execution_sha2_with_sha256_rn_fixed_lookups(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
    fixed_lookups: &Sha256RnFixedLookupProverParams,
) -> Result<ExecutionProof<Sha256Digest>, ProverError> {
    prove_execution_with::<_, Sha2ExecutionBackend, _>(
        bytecode,
        public_input,
        witness,
        whir_config,
        vm_profiler,
        build_prover_state_sha2(),
        |prover_state| prover_state.into_proof(),
        Some(fixed_lookups),
    )
}

fn prove_execution_with<P, B, IntoProof>(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
    mut prover_state: P,
    into_proof: IntoProof,
    sha256_rn_fixed_lookups: Option<&Sha256RnFixedLookupProverParams>,
) -> Result<ExecutionProof<P::Digest>, ProverError>
where
    P: FSProver<EF>,
    B: ExecutionProverBackend<P>,
    IntoProof: FnOnce(P) -> Proof<F, P::Digest>,
{
    check_rate(whir_config.starting_log_inv_rate)
        .map_err(|err| panic!("{err}"))
        .unwrap();
    let ExecutionTrace {
        traces,
        public_memory_size,
        mut memory, // padded with zeros to next power of two
        metadata,
    } = info_span!("Witness generation").in_scope(|| -> Result<_, ProverError> {
        let execution_result = info_span!("Executing bytecode")
            .in_scope(|| try_execute_bytecode(bytecode, public_input, witness, vm_profiler))?;
        Ok(info_span!("Building execution trace").in_scope(|| get_execution_trace(bytecode, execution_result)))
    })?;

    // Memory must be at least MIN_LOG_MEMORY_SIZE and at least bytecode size
    // (required by the stacked polynomial ordering)
    let min_memory_size = (1 << MIN_LOG_MEMORY_SIZE).max(1 << bytecode.log_size());
    if memory.len() < min_memory_size {
        memory.resize(min_memory_size, F::ZERO);
    }
    prover_state.observe_scalars(public_input);
    let bytecode_hash_with_domain_sep = poseidon16_compress_pair(&bytecode.hash, &SNARK_DOMAIN_SEP);
    prover_state.observe_scalars(&bytecode_hash_with_domain_sep);
    if let Some(fixed_lookups) = sha256_rn_fixed_lookups {
        prover_state.observe_scalars(&sha256_rn_fixed_lookup_transcript_scalars(
            fixed_lookups.verifier_transcript_version(),
        ));
    }
    let execution_metadata_scalars = [
        vec![
            whir_config.starting_log_inv_rate,
            log2_strict_usize(memory.len()),
            public_input.len(),
        ],
        traces.values().map(|t| t.log_n_rows).collect::<Vec<_>>(),
    ]
    .concat()
    .into_iter()
    .map(F::from_usize)
    .collect::<Vec<_>>();
    prover_state.add_base_scalars(&execution_metadata_scalars);
    for (table, table_trace) in &traces {
        let log_n_rows = table_trace.log_n_rows;
        assert!(log_n_rows >= MIN_LOG_N_ROWS_PER_TABLE, "missing padding");
        let log_limit = max_log_n_rows_per_table(table);
        if log_n_rows > log_limit {
            return Err(TooBigTableError {
                table_name: table.name(),
                log_n_rows,
                log_limit,
            }
            .into());
        }
    }

    let mut table_log = String::new();
    for (table, trace) in &traces {
        table_log.push_str(&format!(
            "{}: 2^{} * (1 + {:.2}) rows | ",
            table.name(),
            trace.log_n_rows - 1,
            (trace.non_padded_n_rows as f64) / (1 << (trace.log_n_rows - 1)) as f64 - 1.0
        ));
    }
    table_log = table_log.trim_end_matches(" | ").to_string();
    tracing::info!("Trace tables sizes: {}", table_log.magenta());

    // TODO parrallelize
    let mut memory_acc = F::zero_vec(memory.len());
    info_span!("Building memory access count").in_scope(|| {
        for (table, trace) in &traces {
            for lookup in table.lookups() {
                for i in &trace.columns[lookup.index] {
                    for j in 0..lookup.values.len() {
                        memory_acc[i.to_usize() + j] += F::ONE;
                    }
                }
            }
        }
    });

    // // TODO parrallelize
    let mut bytecode_acc = F::zero_vec(bytecode.padded_size());
    info_span!("Building bytecode access count").in_scope(|| {
        for pc in traces[&Table::execution()].columns[COL_PC].iter() {
            bytecode_acc[pc.to_usize()] += F::ONE;
        }
    });

    let multiplicity_traces = sha256_rn_fixed_lookups
        .map(|_| build_sha256_rn_fixed_lookup_multiplicity_traces(&traces[&Table::sha256_compress_rn()]))
        .unwrap_or_default();
    let aux_traces = multiplicity_traces
        .iter()
        .cloned()
        .map(|trace| trace.into_aux_trace())
        .collect::<Vec<_>>();

    enum PcsWitness<InnerWitness> {
        Legacy(StackedPcsWitness<InnerWitness>),
        Aux(StackedPcsWitnessWithLayout<InnerWitness>),
    }

    // 1st Commitment
    let stacked_pcs_witness = if sha256_rn_fixed_lookups.is_some() {
        PcsWitness::Aux(B::stack_polynomials_and_commit(
            &mut prover_state,
            whir_config,
            &memory,
            &memory_acc,
            &bytecode_acc,
            &traces,
            &aux_traces,
        ))
    } else {
        PcsWitness::Legacy(B::stack_polynomials_and_commit_legacy(
            &mut prover_state,
            whir_config,
            &memory,
            &memory_acc,
            &bytecode_acc,
            &traces,
        ))
    };

    // logup (GKR)
    let logup_c = prover_state.sample();
    let logup_alphas = prover_state.sample_vec(log2_ceil_usize(max_bus_width_including_domainsep()));
    let logup_alphas_eq_poly = eval_eq(&logup_alphas);

    let logup_statements = prove_generic_logup(
        &mut prover_state,
        logup_c,
        &logup_alphas_eq_poly,
        &memory,
        &memory_acc,
        &bytecode.instructions_multilinear,
        &bytecode_acc,
        &traces,
    );
    let gkr_point = &logup_statements.gkr_point;
    let mut committed_statements: CommittedStatements = Default::default();
    for table in ALL_TABLES {
        let log_n_rows = traces[&table].log_n_rows;
        committed_statements.insert(
            table,
            vec![(
                MultilinearPoint(from_end(gkr_point, log_n_rows).to_vec()),
                logup_statements.columns_values[&table].clone(),
                BTreeMap::new(),
            )],
        );
    }
    let mut aux_committed_statements: AuxCommittedStatements = vec![Vec::new(); aux_traces.len()];

    let bus_beta = prover_state.sample();
    let air_alpha = prover_state.sample();
    let air_alpha_powers: Vec<EF> = air_alpha.powers().collect_n(max_air_constraints() + 1);
    let air_eta: EF = prover_state.sample();

    let tables_log_heights: BTreeMap<Table, VarCount> =
        traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let tables_sorted = sort_tables_by_height(&tables_log_heights);

    let column_refs: Vec<Vec<&[F]>> = tables_sorted
        .iter()
        .map(|(table, _)| {
            traces[table].columns[..table.n_columns()]
                .iter()
                .map(Vec::as_slice)
                .collect()
        })
        .collect();
    let _span = info_span!("Computing shifted columns for AIR sumcheck").entered();
    let shifted_rows: Vec<Vec<Vec<F>>> = tables_sorted
        .par_iter()
        .zip(&column_refs)
        .map(|((table, _), cols)| compute_shifted_columns(&table.down_column_indexes(), cols))
        .collect();
    std::mem::drop(_span);
    let mut sessions = Vec::with_capacity(tables_sorted.len());
    for (idx, (table, log_n_rows)) in tables_sorted.iter().enumerate() {
        let bus_numerator_value = logup_statements.bus_numerators_values[table];
        let bus_denominator_value = logup_statements.bus_denominators_values[table];
        let bus_final_value = bus_numerator_value
            * match table.bus().direction {
                BusDirection::Pull => EF::NEG_ONE,
                BusDirection::Push => EF::ONE,
            }
            + bus_beta * (bus_denominator_value - logup_c);

        let eq_suffix = from_end(gkr_point, *log_n_rows).to_vec();

        let extra_data = ExtraDataForBuses::new(logup_alphas_eq_poly.clone(), bus_beta, air_alpha_powers.clone());

        let mut up_down: Vec<&[PF<EF>]> = column_refs[idx].to_vec();
        up_down.extend(shifted_rows[idx].iter().map(Vec::as_slice));
        let packed = MleGroupRef::<EF>::Base(up_down).pack();

        let non_padded = traces[table].non_padded_n_rows;

        macro_rules! make_session {
            ($t:expr) => {{
                let session = AirSumcheckSession::new(packed, eq_suffix, bus_final_value, *$t, extra_data, non_padded);
                Box::new(session) as Box<dyn OuterSumcheckSession<EF> + '_>
            }};
        }
        sessions.push(delegate_to_inner!(table => make_session));
    }

    let sumcheck_air_point = info_span!("batched AIR sumcheck")
        .in_scope(|| prove_batched_air_sumcheck(&mut prover_state, &mut sessions, air_eta));

    for (idx, (table, _)) in tables_sorted.iter().enumerate() {
        let col_evals = sessions[idx].final_column_evals();
        prover_state.add_extension_scalars(&col_evals);

        let natural_ordering_point =
            natural_ordering_point_for_session(&sumcheck_air_point.0, traces[table].log_n_rows);
        macro_rules! split {
            ($t:expr) => {{ columns_evals_up_and_down($t, &col_evals, &natural_ordering_point) }};
        }
        let claim = delegate_to_inner!(table => split);
        committed_statements.get_mut(table).unwrap().push(claim);
    }

    if sha256_rn_fixed_lookups.is_some() {
        let fixed_lookup_statements = prove_sha256_rn_fixed_lookup(
            &mut prover_state,
            &traces[&Table::sha256_compress_rn()],
            &multiplicity_traces,
        );
        committed_statements
            .get_mut(&Table::sha256_compress_rn())
            .unwrap()
            .push((
                fixed_lookup_statements.rn_claim.0,
                fixed_lookup_statements.rn_claim.1,
                BTreeMap::new(),
            ));
        for (multiplicity_idx, multiplicity_claim) in fixed_lookup_statements.multiplicity_claims {
            aux_committed_statements[multiplicity_idx].push(multiplicity_claim);
        }
    }

    let public_memory_random_point = MultilinearPoint(prover_state.sample_vec(log2_strict_usize(public_memory_size)));
    let public_memory_eval = (&memory[..public_memory_size]).evaluate(&public_memory_random_point);
    match stacked_pcs_witness {
        PcsWitness::Legacy(stacked_pcs_witness) => {
            let previous_statements = vec![
                SparseStatement::new(
                    stacked_pcs_witness.stacked_n_vars,
                    logup_statements.memory_and_acc_point,
                    vec![
                        SparseValue::new(0, logup_statements.value_memory),
                        SparseValue::new(1, logup_statements.value_memory_acc),
                    ],
                ),
                SparseStatement::new(
                    stacked_pcs_witness.stacked_n_vars,
                    public_memory_random_point,
                    vec![SparseValue::new(0, public_memory_eval)],
                ),
                SparseStatement::new(
                    stacked_pcs_witness.stacked_n_vars,
                    logup_statements.bytecode_and_acc_point,
                    vec![SparseValue::new(
                        (2 * memory.len()) >> bytecode.log_size(),
                        logup_statements.value_bytecode_acc,
                    )],
                ),
            ];
            let global_statements_base = stacked_pcs_global_statements(
                stacked_pcs_witness.stacked_n_vars,
                log2_strict_usize(memory.len()),
                bytecode.log_size(),
                previous_statements,
                &tables_log_heights,
                &committed_statements,
            );

            B::prove_whir(
                &WhirConfig::new(whir_config, stacked_pcs_witness.global_polynomial.by_ref().n_vars()),
                &mut prover_state,
                global_statements_base,
                stacked_pcs_witness.inner_witness,
                &stacked_pcs_witness.global_polynomial.by_ref(),
            );
        }
        PcsWitness::Aux(stacked_pcs_witness) => {
            let stack_layout = &stacked_pcs_witness.layout;
            let mut previous_statements = vec![
                SparseStatement::new(
                    stack_layout.stacked_n_vars,
                    logup_statements.memory_and_acc_point,
                    vec![
                        SparseValue::new(
                            stack_layout.sparse_selector(StackSectionId::Memory, 0),
                            logup_statements.value_memory,
                        ),
                        SparseValue::new(
                            stack_layout.sparse_selector(StackSectionId::Memory, 1),
                            logup_statements.value_memory_acc,
                        ),
                    ],
                ),
                SparseStatement::new(
                    stack_layout.stacked_n_vars,
                    public_memory_random_point,
                    vec![SparseValue::new(
                        stack_layout.sparse_selector_at_point_len(
                            StackSectionId::Memory,
                            0,
                            log2_strict_usize(public_memory_size),
                        ),
                        public_memory_eval,
                    )],
                ),
                SparseStatement::new(
                    stack_layout.stacked_n_vars,
                    logup_statements.bytecode_and_acc_point,
                    vec![SparseValue::new(
                        stack_layout.sparse_selector(StackSectionId::BytecodeAcc, 0),
                        logup_statements.value_bytecode_acc,
                    )],
                ),
            ];
            let exec_n_vars = tables_log_heights[&Table::execution()];
            previous_statements.push(SparseStatement::unique_value(
                stack_layout.stacked_n_vars,
                stack_layout.absolute_index(StackSectionId::VmTable(Table::execution()), COL_PC, 0),
                EF::from_usize(STARTING_PC),
            ));
            previous_statements.push(SparseStatement::unique_value(
                stack_layout.stacked_n_vars,
                stack_layout.absolute_index(
                    StackSectionId::VmTable(Table::execution()),
                    COL_PC,
                    (1 << exec_n_vars) - 1,
                ),
                EF::from_usize(ENDING_PC),
            ));

            let mut per_section: BTreeMap<StackSectionId, Vec<_>> = BTreeMap::new();
            for (table, statements) in &committed_statements {
                per_section.insert(StackSectionId::VmTable(*table), statements.clone());
            }
            for (trace, statements) in aux_traces.iter().zip(aux_committed_statements.iter()) {
                per_section.insert(
                    trace.id,
                    statements
                        .iter()
                        .map(|(point, eq_values)| (point.clone(), eq_values.clone(), BTreeMap::new()))
                        .collect(),
                );
            }

            let global_statements_base =
                stacked_pcs_global_statements_from_layout(stack_layout, previous_statements, per_section);

            B::prove_whir(
                &WhirConfig::new(whir_config, stacked_pcs_witness.global_polynomial.by_ref().n_vars()),
                &mut prover_state,
                global_statements_base,
                stacked_pcs_witness.inner_witness,
                &stacked_pcs_witness.global_polynomial.by_ref(),
            );
        }
    }

    tracing::info!("total pow_grinding time: {} ms", pow_grinding_time().as_millis());
    reset_pow_grinding_time();

    Ok(ExecutionProof {
        proof: into_proof(prover_state),
        metadata: Some(metadata),
    })
}
