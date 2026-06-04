use backend::merkle::Sha256Digest;
use backend::*;
use lean_vm::{
    ALL_TABLES, COL_PC, CommittedStatements, ENDING_PC, MIN_LOG_MEMORY_SIZE, MIN_LOG_N_ROWS_PER_TABLE,
    N_INSTRUCTION_COLUMNS, STARTING_PC, sort_tables_by_height,
};
use lean_vm::{ColIndex, EF, F, Table, TableT, TableTrace};
use std::{collections::BTreeMap, fmt};
use tracing::instrument;
use utils::VarCount;
use utils::ansi::Colorize;

/*
Stacking of various (multilinear) polynomials into a single -big- (multilinear) polynomial, which is committed via WHIR.
[------------------------------ Memory ------------------------------]
[------------------------ Memory Accumulator ------------------------]
[------ Bytecode Accumulator -----]                             (padded to bas as least as large as the execution table)
[-------- Execution Col 0 --------]
[-------- Execution Col 1 --------]
...
[-------- Execution Col 19 -------]
[Dot-Product Col 0]
[Dot-Product Col 1]
...
[Dot-Product Col n]
[Poseidon-16 Col 0]
[Poseidon-16 Col 1]
...
[Poseidon-16 Col m]

(The order between Dot-Product and Poseidon-16 varies based on which table has more rows, but they are always after the execution table)
*/

#[derive(Debug)]
pub struct StackedPcsWitness<InnerWitness> {
    pub stacked_n_vars: VarCount,
    pub inner_witness: InnerWitness,
    pub global_polynomial: MleOwned<EF>,
}

#[derive(Debug)]
pub struct StackedPcsWitnessWithLayout<InnerWitness> {
    pub stacked_n_vars: VarCount,
    pub inner_witness: InnerWitness,
    pub global_polynomial: MleOwned<EF>,
    pub layout: StackLayout,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum StackSectionId {
    Memory,
    BytecodeAcc,
    VmTable(Table),
    Aux(&'static str),
}

impl fmt::Display for StackSectionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Memory => write!(f, "memory"),
            Self::BytecodeAcc => write!(f, "bytecode_acc"),
            Self::VmTable(table) => write!(f, "{}", table.name()),
            Self::Aux(label) => write!(f, "{label}"),
        }
    }
}

struct StackSectionData<'a> {
    id: StackSectionId,
    log_n_rows: VarCount,
    columns: Vec<&'a [F]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackLayout {
    pub stacked_n_vars: VarCount,
    pub actual_data_len: usize,
    pub sections: Vec<StackSectionLayout>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackSectionLayout {
    pub id: StackSectionId,
    pub log_n_rows: VarCount,
    pub n_columns: usize,
    pub offset: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackSectionDescriptor {
    pub id: StackSectionId,
    pub log_n_rows: VarCount,
    pub n_columns: usize,
}

#[derive(Debug, Clone)]
pub struct AuxTrace {
    pub id: StackSectionId,
    pub log_n_rows: VarCount,
    pub columns: Vec<Vec<F>>,
}

impl AuxTrace {
    pub fn layout(&self) -> StackSectionDescriptor {
        StackSectionDescriptor {
            id: self.id,
            log_n_rows: self.log_n_rows,
            n_columns: self.columns.len(),
        }
    }
}

pub type AuxCommittedStatements = Vec<Vec<(MultilinearPoint<EF>, BTreeMap<ColIndex, EF>)>>;

impl StackLayout {
    pub fn section(&self, id: StackSectionId) -> &StackSectionLayout {
        self.sections
            .iter()
            .find(|section| section.id == id)
            .unwrap_or_else(|| panic!("missing stack section: {id:?}"))
    }

    pub fn sparse_selector(&self, id: StackSectionId, col_index: usize) -> usize {
        let section = self.section(id);
        assert!(col_index < section.n_columns);
        assert_eq!(section.offset % (1 << section.log_n_rows), 0);
        (section.offset >> section.log_n_rows) + col_index
    }

    pub fn sparse_selector_at_point_len(&self, id: StackSectionId, col_index: usize, point_n_vars: usize) -> usize {
        let section = self.section(id);
        assert!(col_index < section.n_columns);
        assert!(point_n_vars <= section.log_n_rows);
        let column_offset = section.offset + (col_index << section.log_n_rows);
        assert_eq!(column_offset % (1 << point_n_vars), 0);
        column_offset >> point_n_vars
    }

    pub fn absolute_index(&self, id: StackSectionId, col_index: usize, row_index: usize) -> usize {
        let section = self.section(id);
        assert!(col_index < section.n_columns);
        assert!(row_index < 1 << section.log_n_rows);
        section.offset + (col_index << section.log_n_rows) + row_index
    }

    pub fn display(&self) -> String {
        let sections = self
            .sections
            .iter()
            .map(|section| {
                let size = section.n_columns << section.log_n_rows;
                format!(
                    "{}: rows=2^{}, cols={}, size={}, offset={}",
                    section.id, section.log_n_rows, section.n_columns, size, section.offset
                )
            })
            .collect::<Vec<_>>()
            .join(" | ");
        format!("stacked PCS layout: {sections}")
    }
}

pub fn stacked_pcs_global_statements_from_layout(
    layout: &StackLayout,
    previous_statements: Vec<SparseStatement<EF>>,
    per_section: BTreeMap<StackSectionId, Vec<(MultilinearPoint<EF>, BTreeMap<ColIndex, EF>, BTreeMap<ColIndex, EF>)>>,
) -> Vec<SparseStatement<EF>> {
    let mut out = previous_statements;
    for section in &layout.sections {
        let Some(statements) = per_section.get(&section.id) else {
            continue;
        };
        for (point, eq_values, next_values) in statements {
            if !next_values.is_empty() {
                out.push(SparseStatement::new_next(
                    layout.stacked_n_vars,
                    point.clone(),
                    next_values
                        .iter()
                        .map(|(&col_index, &value)| {
                            SparseValue::new(layout.sparse_selector(section.id, col_index), value)
                        })
                        .collect(),
                ));
            }
            out.push(SparseStatement::new(
                layout.stacked_n_vars,
                point.clone(),
                eq_values
                    .iter()
                    .map(|(&col_index, &value)| SparseValue::new(layout.sparse_selector(section.id, col_index), value))
                    .collect(),
            ));
        }
    }
    out
}

pub fn stacked_pcs_global_statements(
    stacked_n_vars: VarCount,
    memory_n_vars: VarCount,
    bytecode_n_vars: VarCount,
    previous_statements: Vec<SparseStatement<EF>>,
    tables_heights: &BTreeMap<Table, VarCount>,
    committed_statements: &CommittedStatements,
) -> Vec<SparseStatement<EF>> {
    assert_eq!(tables_heights.len(), committed_statements.len());

    let tables_heights_sorted = sort_tables_by_height(tables_heights);

    let mut global_statements = previous_statements;
    let mut offset = 2 << memory_n_vars; // memory + memory_acc

    let max_table_n_vars = tables_heights_sorted[0].1;
    offset += 1 << bytecode_n_vars.max(max_table_n_vars); // bytecode acc

    for (table, n_vars) in tables_heights_sorted {
        if table.is_execution_table() {
            // Important: ensure both initial and final PC conditions are correct
            global_statements.push(SparseStatement::unique_value(
                stacked_n_vars,
                offset + (COL_PC << n_vars),
                EF::from_usize(STARTING_PC),
            ));
            global_statements.push(SparseStatement::unique_value(
                stacked_n_vars,
                offset + ((COL_PC + 1) << n_vars) - 1,
                EF::from_usize(ENDING_PC),
            ));
        }
        for (point, eq_values, next_values) in &committed_statements[&table] {
            if !next_values.is_empty() {
                global_statements.push(SparseStatement::new_next(
                    stacked_n_vars,
                    point.clone(),
                    next_values
                        .iter()
                        .map(|(&col_index, &value)| SparseValue::new((offset >> n_vars) + col_index, value))
                        .collect(),
                ));
            }
            global_statements.push(SparseStatement::new(
                stacked_n_vars,
                point.clone(),
                eq_values
                    .iter()
                    .map(|(&col_index, &value)| SparseValue::new((offset >> n_vars) + col_index, value))
                    .collect(),
            ));
        }
        offset += table.n_columns() << n_vars;
    }
    global_statements
}

#[instrument(skip_all)]
pub fn stack_polynomials_and_commit(
    prover_state: &mut impl FSProver<EF, Digest = [F; DIGEST_ELEMS]>,
    whir_config_builder: &WhirConfigBuilder,
    memory: &[F],
    memory_acc: &[F],
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
) -> StackedPcsWitness<Witness<EF>> {
    stack_polynomials_and_commit_with(
        whir_config_builder,
        memory,
        memory_acc,
        bytecode_acc,
        traces,
        |whir_config, global_polynomial, offset| whir_config.commit(prover_state, global_polynomial, offset),
    )
}

#[instrument(skip_all)]
pub fn stack_polynomials_and_commit_sha2(
    prover_state: &mut impl FSProver<EF, Digest = Sha256Digest>,
    whir_config_builder: &WhirConfigBuilder,
    memory: &[F],
    memory_acc: &[F],
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
) -> StackedPcsWitness<Witness2<EF>> {
    stack_polynomials_and_commit_with(
        whir_config_builder,
        memory,
        memory_acc,
        bytecode_acc,
        traces,
        |whir_config, global_polynomial, offset| whir_config.commit2(prover_state, global_polynomial, offset),
    )
}

#[instrument(skip_all)]
pub fn stack_polynomials_and_commit_with_aux(
    prover_state: &mut impl FSProver<EF, Digest = [F; DIGEST_ELEMS]>,
    whir_config_builder: &WhirConfigBuilder,
    memory: &[F],
    memory_acc: &[F],
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
    aux_traces: &[AuxTrace],
) -> StackedPcsWitnessWithLayout<Witness<EF>> {
    stack_polynomials_and_commit_with_aux_inner(
        whir_config_builder,
        memory,
        memory_acc,
        bytecode_acc,
        traces,
        aux_traces,
        |whir_config, global_polynomial, offset| whir_config.commit(prover_state, global_polynomial, offset),
    )
}

#[instrument(skip_all)]
pub fn stack_polynomials_and_commit_sha2_with_aux(
    prover_state: &mut impl FSProver<EF, Digest = Sha256Digest>,
    whir_config_builder: &WhirConfigBuilder,
    memory: &[F],
    memory_acc: &[F],
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
    aux_traces: &[AuxTrace],
) -> StackedPcsWitnessWithLayout<Witness2<EF>> {
    stack_polynomials_and_commit_with_aux_inner(
        whir_config_builder,
        memory,
        memory_acc,
        bytecode_acc,
        traces,
        aux_traces,
        |whir_config, global_polynomial, offset| whir_config.commit2(prover_state, global_polynomial, offset),
    )
}

fn stack_polynomials_and_commit_with<InnerWitness>(
    whir_config_builder: &WhirConfigBuilder,
    memory: &[F],
    memory_acc: &[F],
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
    commit: impl FnOnce(&WhirConfig<EF>, &MleOwned<EF>, usize) -> InnerWitness,
) -> StackedPcsWitness<InnerWitness> {
    assert_eq!(memory.len(), memory_acc.len());
    let tables_heights = traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let tables_heights_sorted = sort_tables_by_height(&tables_heights);
    assert!(log2_strict_usize(memory.len()) >= tables_heights[&Table::execution()]); // memory must be at least as large as the number of cycles (TODO add some padding when this is not the case)
    assert!(tables_heights[&Table::execution()] >= tables_heights_sorted[0].1); // execution table must be the largest table (TODO add some padding when this is not the case)

    let stacked_n_vars = compute_stacked_n_vars(
        log2_strict_usize(memory.len()),
        log2_strict_usize(bytecode_acc.len()),
        &tables_heights_sorted.iter().cloned().collect(),
    );
    let mut global_polynomial = F::zero_vec(1 << stacked_n_vars); // TODO avoid cloning all witness data
    global_polynomial[..memory.len()].copy_from_slice(memory);
    let mut offset = memory.len();
    global_polynomial[offset..][..memory_acc.len()].copy_from_slice(memory_acc);
    offset += memory_acc.len();

    global_polynomial[offset..][..bytecode_acc.len()].copy_from_slice(bytecode_acc);
    let largest_table_height = 1 << tables_heights_sorted[0].1;
    offset += largest_table_height.max(bytecode_acc.len()); // we may pad bytecode_acc to match largest table height

    for (table, log_n_rows) in &tables_heights_sorted {
        let n_rows = 1 << *log_n_rows;
        for col_index in 0..table.n_columns() {
            let col = &traces[table].columns[col_index];
            global_polynomial[offset..][..n_rows].copy_from_slice(&col[..n_rows]);
            offset += n_rows;
        }
    }
    assert_eq!(log2_ceil_usize(offset), stacked_n_vars);
    tracing::info!(
        "{}",
        format!(
            "stacked PCS data: {} = 2^{} * (1 + {:.2})",
            offset,
            stacked_n_vars - 1,
            (offset as f64) / (1 << (stacked_n_vars - 1)) as f64 - 1.0
        )
        .green()
    );

    let global_polynomial = MleOwned::Base(global_polynomial);

    let whir_config = WhirConfig::new(whir_config_builder, stacked_n_vars);
    let inner_witness = commit(&whir_config, &global_polynomial, offset);
    StackedPcsWitness {
        stacked_n_vars,
        inner_witness,
        global_polynomial,
    }
}

fn stack_polynomials_and_commit_with_aux_inner<InnerWitness>(
    whir_config_builder: &WhirConfigBuilder,
    memory: &[F],
    memory_acc: &[F],
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
    aux_traces: &[AuxTrace],
    commit: impl FnOnce(&WhirConfig<EF>, &MleOwned<EF>, usize) -> InnerWitness,
) -> StackedPcsWitnessWithLayout<InnerWitness> {
    assert_eq!(memory.len(), memory_acc.len());
    assert_eq!(1 << log2_strict_usize(memory.len()), memory.len());
    assert_eq!(1 << log2_strict_usize(bytecode_acc.len()), bytecode_acc.len());

    let sections = stack_sections(memory, memory_acc, bytecode_acc, traces, aux_traces);
    let (layout, global_polynomial) = stack_section_polynomials(&sections);
    // tracing::info!("{}", layout.display().green());
    tracing::info!(
        "{}",
        format!(
            "stacked PCS data: {} = 2^{} * (1 + {:.2})",
            layout.actual_data_len,
            layout.stacked_n_vars - 1,
            (layout.actual_data_len as f64) / (1 << (layout.stacked_n_vars - 1)) as f64 - 1.0
        )
        .green()
    );

    let global_polynomial = MleOwned::Base(global_polynomial);

    let whir_config = WhirConfig::new(whir_config_builder, layout.stacked_n_vars);
    let inner_witness = commit(&whir_config, &global_polynomial, layout.actual_data_len);
    StackedPcsWitnessWithLayout {
        stacked_n_vars: layout.stacked_n_vars,
        inner_witness,
        global_polynomial,
        layout,
    }
}

pub fn stacked_pcs_parse_commitment(
    whir_config_builder: &WhirConfigBuilder,
    verifier_state: &mut impl FSVerifier<EF, Digest = [F; DIGEST_ELEMS]>,
    log_memory: usize,
    log_bytecode: usize,
    tables_heights: &BTreeMap<Table, VarCount>,
) -> Result<ParsedCommitment<F, EF>, ProofError> {
    stacked_pcs_parse_commitment_generic(
        whir_config_builder,
        verifier_state,
        log_memory,
        log_bytecode,
        tables_heights,
    )
}

pub fn stacked_pcs_parse_commitment_sha2(
    whir_config_builder: &WhirConfigBuilder,
    verifier_state: &mut impl FSVerifier<EF, Digest = Sha256Digest>,
    log_memory: usize,
    log_bytecode: usize,
    tables_heights: &BTreeMap<Table, VarCount>,
) -> Result<ParsedCommitment<F, EF, Sha256Digest>, ProofError> {
    stacked_pcs_parse_commitment_generic(
        whir_config_builder,
        verifier_state,
        log_memory,
        log_bytecode,
        tables_heights,
    )
}

pub fn stacked_pcs_parse_commitment_generic<Digest: Clone>(
    whir_config_builder: &WhirConfigBuilder,
    verifier_state: &mut impl FSVerifier<EF, Digest = Digest>,
    log_memory: usize,
    log_bytecode: usize,
    tables_heights: &BTreeMap<Table, VarCount>,
) -> Result<ParsedCommitment<F, EF, Digest>, ProofError> {
    if log_memory < tables_heights[&Table::execution()]
        || tables_heights[&Table::execution()] < tables_heights.values().copied().max().unwrap()
    {
        // memory must be at least as large as the number of cycles
        // execution table must be the largest table
        return Err(ProofError::InvalidProof);
    }

    let stacked_n_vars = compute_stacked_n_vars(log_memory, log_bytecode, tables_heights);
    if stacked_n_vars
        > F::TWO_ADICITY + whir_config_builder.folding_factor.at_round(0) - whir_config_builder.starting_log_inv_rate
    {
        return Err(ProofError::InvalidProof);
    }
    WhirConfig::new(whir_config_builder, stacked_n_vars).parse_commitment_generic(verifier_state)
}

pub fn stacked_pcs_parse_commitment_from_n_vars_generic<Digest: Clone>(
    whir_config_builder: &WhirConfigBuilder,
    verifier_state: &mut impl FSVerifier<EF, Digest = Digest>,
    stacked_n_vars: VarCount,
) -> Result<ParsedCommitment<F, EF, Digest>, ProofError> {
    if stacked_n_vars
        > F::TWO_ADICITY + whir_config_builder.folding_factor.at_round(0) - whir_config_builder.starting_log_inv_rate
    {
        return Err(ProofError::InvalidProof);
    }
    WhirConfig::new(whir_config_builder, stacked_n_vars).parse_commitment_generic(verifier_state)
}

fn compute_stacked_n_vars(
    log_memory: usize,
    log_bytecode: usize,
    tables_log_heights: &BTreeMap<Table, VarCount>,
) -> VarCount {
    let max_table_log_n_rows = tables_log_heights.values().copied().max().unwrap();
    let total_len = (2 << log_memory)
        + (1 << log_bytecode.max(max_table_log_n_rows))
        + tables_log_heights
            .iter()
            .map(|(table, log_n_rows)| table.n_columns() << log_n_rows)
            .sum::<usize>();
    log2_ceil_usize(total_len)
}

pub fn compute_stack_layout(
    log_memory: usize,
    log_bytecode: usize,
    tables_log_heights: &BTreeMap<Table, VarCount>,
    aux_layouts: &[StackSectionDescriptor],
) -> StackLayout {
    assert!(
        aux_layouts
            .iter()
            .all(|layout| matches!(layout.id, StackSectionId::Aux(_)))
    );
    let mut sections = vec![
        StackSectionLayout {
            id: StackSectionId::Memory,
            log_n_rows: log_memory,
            n_columns: 2,
            offset: 0,
        },
        StackSectionLayout {
            id: StackSectionId::BytecodeAcc,
            log_n_rows: log_bytecode,
            n_columns: 1,
            offset: 0,
        },
    ];
    sections.extend(
        tables_log_heights
            .iter()
            .map(|(&table, &log_n_rows)| StackSectionLayout {
                id: StackSectionId::VmTable(table),
                log_n_rows,
                n_columns: table.n_columns(),
                offset: 0,
            }),
    );
    sections.extend(aux_layouts.iter().map(|layout| StackSectionLayout {
        id: layout.id,
        log_n_rows: layout.log_n_rows,
        n_columns: layout.n_columns,
        offset: 0,
    }));
    finalize_stack_layout(sections)
}

fn finalize_stack_layout(mut sections: Vec<StackSectionLayout>) -> StackLayout {
    sections.sort_by_key(|section| (std::cmp::Reverse(section.log_n_rows), section.id));

    let mut offset = 0usize;
    for section in &mut sections {
        debug_assert_eq!(offset % (1usize << section.log_n_rows), 0);
        section.offset = offset;
        offset += section.n_columns << section.log_n_rows;
    }
    StackLayout {
        stacked_n_vars: log2_ceil_usize(offset),
        actual_data_len: offset,
        sections,
    }
}

fn stack_sections<'a>(
    memory: &'a [F],
    memory_acc: &'a [F],
    bytecode_acc: &'a [F],
    traces: &'a BTreeMap<Table, TableTrace>,
    aux_traces: &'a [AuxTrace],
) -> Vec<StackSectionData<'a>> {
    assert!(
        aux_traces
            .iter()
            .all(|trace| matches!(trace.id, StackSectionId::Aux(_)))
    );
    let mut sections = vec![
        StackSectionData {
            id: StackSectionId::Memory,
            log_n_rows: log2_strict_usize(memory.len()),
            columns: vec![memory, memory_acc],
        },
        StackSectionData {
            id: StackSectionId::BytecodeAcc,
            log_n_rows: log2_strict_usize(bytecode_acc.len()),
            columns: vec![bytecode_acc],
        },
    ];
    sections.extend(traces.iter().map(|(&table, trace)| StackSectionData {
        id: StackSectionId::VmTable(table),
        log_n_rows: trace.log_n_rows,
        columns: trace.columns[..table.n_columns()].iter().map(Vec::as_slice).collect(),
    }));
    sections.extend(aux_traces.iter().map(|trace| StackSectionData {
        id: trace.id,
        log_n_rows: trace.log_n_rows,
        columns: trace.columns.iter().map(Vec::as_slice).collect(),
    }));
    sections
}

fn stack_section_polynomials(sections: &[StackSectionData<'_>]) -> (StackLayout, Vec<F>) {
    let section_layouts = sections
        .iter()
        .map(|section| StackSectionLayout {
            id: section.id,
            log_n_rows: section.log_n_rows,
            n_columns: section.columns.len(),
            offset: 0,
        })
        .collect::<Vec<_>>();
    let layout = finalize_stack_layout(section_layouts);

    let mut global_polynomial = F::zero_vec(1 << layout.stacked_n_vars);
    for section_layout in &layout.sections {
        let section = sections.iter().find(|section| section.id == section_layout.id).unwrap();
        let n_rows = 1 << section_layout.log_n_rows;
        assert_eq!(section.columns.len(), section_layout.n_columns);
        for (col_index, col) in section.columns.iter().enumerate() {
            assert_eq!(col.len(), n_rows);
            let start = section_layout.offset + (col_index << section_layout.log_n_rows);
            global_polynomial[start..start + n_rows].copy_from_slice(col);
        }
    }

    (layout, global_polynomial)
}

pub fn min_stacked_n_vars(log_bytecode: usize) -> usize {
    let mut min_tables_log_heights = BTreeMap::new();
    for table in ALL_TABLES {
        min_tables_log_heights.insert(table, MIN_LOG_N_ROWS_PER_TABLE);
    }
    compute_stacked_n_vars(MIN_LOG_MEMORY_SIZE, log_bytecode, &min_tables_log_heights)
}

pub fn total_whir_statements() -> usize {
    total_whir_statements_with_aux(&[])
}

pub fn total_whir_statements_with_aux(aux_layouts: &[StackSectionDescriptor]) -> usize {
    assert!(
        aux_layouts
            .iter()
            .all(|layout| matches!(layout.id, StackSectionId::Aux(_)))
    );
    6 // memory + memory_acc + public_memory + bytecode_acc + pc_start + pc_end
     + ALL_TABLES
        .iter()
        .map(|table| {
            // AIR
            table.n_columns()
            + table.n_down_columns()
            // Lookups into memory
            + table.lookups().iter().map(|lookup| 1 + lookup.values.len()).sum::<usize>()
        })
        .sum::<usize>()
        // bytecode lookup
        + 1 // PC
        + N_INSTRUCTION_COLUMNS
        + aux_layouts.iter().map(|layout| layout.n_columns).sum::<usize>()
}
