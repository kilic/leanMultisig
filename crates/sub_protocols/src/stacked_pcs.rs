use backend::*;
use lean_vm::{ALL_TABLES, MIN_LOG_MEMORY_SIZE, MIN_LOG_N_ROWS_PER_TABLE, N_INSTRUCTION_COLUMNS};
use lean_vm::{ColIndex, EF, F, Table, TableT, TableTrace};
use std::{collections::BTreeMap, fmt};
use tracing::instrument;
use utils::VarCount;
use utils::ansi::Colorize;

/*
Stacking of various multilinear polynomials into a single global polynomial, committed via WHIR.
Sections are tightly packed by column and sorted by descending row height. This preserves the sparse
opening invariant that each section offset is divisible by its row height.
*/

#[derive(Debug)]
pub struct StackedPcsWitness {
    pub stacked_n_vars: VarCount,
    pub inner_witness: Witness<EF>,
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
        assert!(section.offset.is_multiple_of(1 << section.log_n_rows));
        (section.offset >> section.log_n_rows) + col_index
    }

    pub fn sparse_selector_at_point_len(&self, id: StackSectionId, col_index: usize, point_n_vars: usize) -> usize {
        let section = self.section(id);
        assert!(col_index < section.n_columns);
        assert!(point_n_vars <= section.log_n_rows);
        let column_offset = section.offset + (col_index << section.log_n_rows);
        assert!(column_offset.is_multiple_of(1 << point_n_vars));
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

pub fn stacked_pcs_global_statements(
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

#[instrument(skip_all)]
pub fn stack_polynomials_and_commit(
    prover_state: &mut impl FSProver<EF>,
    whir_config_builder: &WhirConfigBuilder,
    memory: &[F],
    memory_acc: &[F],
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
    aux_traces: &[AuxTrace],
) -> StackedPcsWitness {
    assert_eq!(memory.len(), memory_acc.len());
    assert_eq!(1 << log2_strict_usize(memory.len()), memory.len());
    assert_eq!(1 << log2_strict_usize(bytecode_acc.len()), bytecode_acc.len());

    let sections = stack_sections(memory, memory_acc, bytecode_acc, traces, aux_traces);
    let (layout, global_polynomial) = stack_section_polynomials(&sections);
    tracing::info!("{}", layout.display().green());
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

    let inner_witness = WhirConfig::new(whir_config_builder, layout.stacked_n_vars)
        .commit_with_ood(prover_state, &global_polynomial, layout.actual_data_len)
        .0;
    StackedPcsWitness {
        stacked_n_vars: layout.stacked_n_vars,
        inner_witness,
        global_polynomial,
        layout,
    }
}

pub fn stacked_pcs_parse_commitment(
    whir_config_builder: &WhirConfigBuilder,
    verifier_state: &mut impl FSVerifier<EF>,
    stacked_n_vars: VarCount,
) -> Result<ParsedCommitment<F, EF>, ProofError> {
    if stacked_n_vars
        > F::TWO_ADICITY + whir_config_builder.folding_factor.at_round(0) - whir_config_builder.starting_log_inv_rate
    {
        return Err(ProofError::InvalidProof);
    }
    WhirConfig::new(whir_config_builder, stacked_n_vars).parse_commitment(verifier_state)
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
        debug_assert!(offset.is_multiple_of(1usize << section.log_n_rows));
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
    compute_stack_layout(MIN_LOG_MEMORY_SIZE, log_bytecode, &min_tables_log_heights, &[]).stacked_n_vars
}

pub fn total_whir_statements(aux_layouts: &[StackSectionDescriptor]) -> usize {
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

#[cfg(test)]
mod tests {
    use super::*;

    fn range_col(start: usize, len: usize) -> Vec<F> {
        (start..start + len).map(F::from_usize).collect()
    }

    #[test]
    fn stack_layout_sorts_sections_by_height_and_preserves_alignment() {
        let mut table_heights = BTreeMap::new();
        table_heights.insert(Table::execution(), 8);
        table_heights.insert(Table::poseidon16(), 10);
        table_heights.insert(Table::extension_op(), 7);
        let aux_layouts = [StackSectionDescriptor {
            id: StackSectionId::Aux("test_aux"),
            log_n_rows: 9,
            n_columns: 1,
        }];

        let layout = compute_stack_layout(6, 5, &table_heights, &aux_layouts);
        let heights = layout
            .sections
            .iter()
            .map(|section| section.log_n_rows)
            .collect::<Vec<_>>();
        assert!(heights.windows(2).all(|pair| pair[0] >= pair[1]));
        for section in &layout.sections {
            assert!(section.offset.is_multiple_of(1 << section.log_n_rows));
        }
    }

    #[test]
    fn stacked_sections_sparse_selectors_open_expected_columns() {
        let memory = range_col(0, 8);
        let memory_acc = range_col(100, 8);
        let bytecode_acc = range_col(200, 4);
        let aux = range_col(300, 16);
        let sections = vec![
            StackSectionData {
                id: StackSectionId::Memory,
                log_n_rows: 3,
                columns: vec![&memory, &memory_acc],
            },
            StackSectionData {
                id: StackSectionId::BytecodeAcc,
                log_n_rows: 2,
                columns: vec![&bytecode_acc],
            },
            StackSectionData {
                id: StackSectionId::Aux("test_aux"),
                log_n_rows: 4,
                columns: vec![&aux],
            },
        ];

        let (layout, global) = stack_section_polynomials(&sections);
        let zero_point_4 = MultilinearPoint(vec![EF::ZERO; 4]);
        let zero_point_3 = MultilinearPoint(vec![EF::ZERO; 3]);
        let zero_point_2 = MultilinearPoint(vec![EF::ZERO; 2]);

        assert_eq!(
            global.evaluate_sparse(
                layout.sparse_selector(StackSectionId::Aux("test_aux"), 0),
                &zero_point_4
            ),
            EF::from(aux[0])
        );
        assert_eq!(
            global.evaluate_sparse(layout.sparse_selector(StackSectionId::Memory, 0), &zero_point_3),
            EF::from(memory[0])
        );
        assert_eq!(
            global.evaluate_sparse(layout.sparse_selector(StackSectionId::Memory, 1), &zero_point_3),
            EF::from(memory_acc[0])
        );
        assert_eq!(
            global.evaluate_sparse(layout.sparse_selector(StackSectionId::BytecodeAcc, 0), &zero_point_2,),
            EF::from(bytecode_acc[0])
        );
    }
}
