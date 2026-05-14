use std::collections::BTreeMap;

use crate::sha256_rn_fixed_lookups::{
    Sha256RnFixedLookupProverParams, build_sha256_rn_fixed_lookup_multiplicity_traces, prove_sha256_rn_fixed_lookup,
    sha256_rn_fixed_lookup_transcript_scalars,
};
use crate::*;
use lean_vm::*;

use sub_protocols::*;
use tracing::info_span;
use utils::ansi::Colorize;
use utils::{build_prover_state, from_end};
#[derive(Debug)]
pub struct ExecutionProof {
    pub proof: Proof<F>,
    // benchmark / debug purpose
    pub metadata: ExecutionMetadata,
}

pub fn prove_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
) -> ExecutionProof {
    prove_execution_inner(bytecode, public_input, witness, whir_config, vm_profiler, None)
}

pub fn prove_execution_with_sha256_rn_fixed_lookups(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
    fixed_lookups: &Sha256RnFixedLookupProverParams,
) -> ExecutionProof {
    prove_execution_inner(
        bytecode,
        public_input,
        witness,
        whir_config,
        vm_profiler,
        Some(fixed_lookups),
    )
}

fn prove_execution_inner(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
    sha256_rn_fixed_lookups: Option<&Sha256RnFixedLookupProverParams>,
) -> ExecutionProof {
    let prove_total_time = std::time::Instant::now();
    check_rate(whir_config.starting_log_inv_rate)
        .map_err(|err| panic!("{err}"))
        .unwrap();
    let time = std::time::Instant::now();
    let ExecutionTrace {
        traces,
        public_memory_size,
        mut memory, // padded with zeros to next power of two
        metadata,
    } = info_span!("Witness generation").in_scope(|| {
        let execution_result = info_span!("Executing bytecode")
            .in_scope(|| execute_bytecode(bytecode, public_input, witness, vm_profiler));
        info_span!("Building execution trace").in_scope(|| get_execution_trace(bytecode, execution_result))
    });
    println!("PROVE PHASE witness+trace: {:.3} s", time.elapsed().as_secs_f32());

    let time = std::time::Instant::now();
    // Memory must be at least MIN_LOG_MEMORY_SIZE and at least bytecode size.
    // Generic logup still keeps the current memory/bytecode sizing assumptions;
    // aux traces are independent stack sections and do not force memory padding.
    let min_memory_size = (1 << MIN_LOG_MEMORY_SIZE).max(1 << bytecode.log_size());
    if memory.len() < min_memory_size {
        memory.resize(min_memory_size, F::ZERO);
    }
    let mut prover_state = build_prover_state();
    prover_state.observe_scalars(public_input);
    prover_state.observe_scalars(&poseidon16_compress_pair(&bytecode.hash, &SNARK_DOMAIN_SEP));
    if let Some(fixed_lookups) = sha256_rn_fixed_lookups {
        prover_state.observe_scalars(&sha256_rn_fixed_lookup_transcript_scalars(
            fixed_lookups.transcript_version,
        ));
    }
    prover_state.add_base_scalars(
        &[
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
        .collect::<Vec<_>>(),
    );

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
    println!("PROVE PHASE transcript+metadata: {:.3} s", time.elapsed().as_secs_f32());

    // TODO parrallelize
    let time = std::time::Instant::now();
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
    println!("PROVE PHASE memory access count: {:.3} s", time.elapsed().as_secs_f32());

    // // TODO parrallelize
    let time = std::time::Instant::now();
    let mut bytecode_acc = F::zero_vec(bytecode.padded_size());
    info_span!("Building bytecode access count").in_scope(|| {
        for pc in traces[&Table::execution()].columns[COL_PC].iter() {
            bytecode_acc[pc.to_usize()] += F::ONE;
        }
    });
    println!(
        "PROVE PHASE bytecode access count: {:.3} s",
        time.elapsed().as_secs_f32()
    );

    let time = std::time::Instant::now();
    let multiplicity_traces = sha256_rn_fixed_lookups
        .map(|_| {
            let trace = &traces[&Table::sha256_compress_rn()];
            build_sha256_rn_fixed_lookup_multiplicity_traces(trace)
        })
        .unwrap_or_default();
    let aux_traces = multiplicity_traces
        .iter()
        .cloned()
        .map(|trace| trace.into_aux_trace())
        .collect::<Vec<_>>();
    if sha256_rn_fixed_lookups.is_some() {
        println!(
            "PROVE PHASE SHA256 RN multiplicity traces: {:.3} s",
            time.elapsed().as_secs_f32()
        );
    }

    // 1st Commitment
    let time = std::time::Instant::now();
    let stacked_pcs_witness = stack_polynomials_and_commit(
        &mut prover_state,
        whir_config,
        &memory,
        &memory_acc,
        &bytecode_acc,
        &traces,
        &aux_traces,
    );
    println!("PROVE PHASE stacked PCS commit: {:.3} s", time.elapsed().as_secs_f32());
    println!(
        "PROVE PHASE stacked PCS vars: {}, actual_data_len: {}",
        stacked_pcs_witness.layout.stacked_n_vars, stacked_pcs_witness.layout.actual_data_len
    );

    // logup (GKR)
    let time = std::time::Instant::now();
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
    println!("PROVE PHASE generic logup: {:.3} s", time.elapsed().as_secs_f32());
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

    let time = std::time::Instant::now();
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
    println!("PROVE PHASE shifted columns: {:.3} s", time.elapsed().as_secs_f32());
    let time = std::time::Instant::now();
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
    println!("PROVE PHASE AIR session setup: {:.3} s", time.elapsed().as_secs_f32());

    let time = std::time::Instant::now();
    let sumcheck_air_point = info_span!("batched AIR sumcheck")
        .in_scope(|| prove_batched_air_sumcheck(&mut prover_state, &mut sessions, air_eta));
    println!(
        "PROVE PHASE batched AIR sumcheck: {:.3} s",
        time.elapsed().as_secs_f32()
    );

    let time = std::time::Instant::now();
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
    println!("PROVE PHASE AIR final openings: {:.3} s", time.elapsed().as_secs_f32());

    let time = std::time::Instant::now();
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
    if sha256_rn_fixed_lookups.is_some() {
        println!(
            "PROVE PHASE SHA256 RN fixed lookup total: {:.3} s",
            time.elapsed().as_secs_f32()
        );
    }

    let time = std::time::Instant::now();
    let public_memory_random_point = MultilinearPoint(prover_state.sample_vec(log2_strict_usize(public_memory_size)));
    let public_memory_eval = (&memory[..public_memory_size]).evaluate(&public_memory_random_point);
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
    let exec_id = StackSectionId::VmTable(Table::execution());
    let exec_n_vars = tables_log_heights[&Table::execution()];
    previous_statements.push(SparseStatement::unique_value(
        stack_layout.stacked_n_vars,
        stack_layout.absolute_index(exec_id, COL_PC, 0),
        EF::from_usize(STARTING_PC),
    ));
    previous_statements.push(SparseStatement::unique_value(
        stack_layout.stacked_n_vars,
        stack_layout.absolute_index(exec_id, COL_PC, (1 << exec_n_vars) - 1),
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

    let global_statements_base = stacked_pcs_global_statements(stack_layout, previous_statements, per_section);
    println!("PROVE PHASE PCS statements: {:.3} s", time.elapsed().as_secs_f32());

    let time = std::time::Instant::now();
    WhirConfig::new(whir_config, stacked_pcs_witness.global_polynomial.by_ref().n_vars()).prove(
        &mut prover_state,
        global_statements_base,
        stacked_pcs_witness.inner_witness,
        &stacked_pcs_witness.global_polynomial.by_ref(),
    );
    println!("PROVE PHASE WHIR prove: {:.3} s", time.elapsed().as_secs_f32());
    println!(
        "PROVE PHASE total inner: {:.3} s",
        prove_total_time.elapsed().as_secs_f32()
    );

    ExecutionProof {
        proof: prover_state.into_proof(),
        metadata,
    }
}
