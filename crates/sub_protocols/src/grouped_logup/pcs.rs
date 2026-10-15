use super::*;
use crate::{natural_ordering_point_for_session, stacked_pcs_global_statements};

/// Final claims contain no public address evaluation. Bytecode uses one
/// fingerprinted instruction evaluation and one multiplicity per selector.
#[derive(Debug, Clone)]
pub struct GroupedFinalClaims {
    pub sections: Vec<Vec<EF>>,
}

pub fn grouped_section_claim_count(section: &GroupedSectionLayout) -> usize {
    let source = match section.source {
        GroupedSource::Table(table) => table.n_columns() + table.n_shift_columns(),
        _ => 2 * section.group_widths[0],
    };
    source + section.group_widths.len() * DIMENSION
}

impl GroupedFinalClaims {
    pub fn from_column_evals(
        layout: &GroupedLayout,
        columns: &[Vec<EF>],
        beta_eq: &[EF],
    ) -> Result<Self, GroupedWitnessError> {
        if columns.len() != layout.sections.len() || beta_eq.len() != 1 << LOG_MAX_BUS_WIDTH {
            return Err(GroupedWitnessError::LayoutMismatch);
        }
        let mut sections = Vec::new();
        for (section, evals) in layout.sections.iter().zip(columns) {
            let air = GroupedAir {
                layout: section.clone(),
                kind: GroupedAirKind::Constraints,
            };
            if evals.len() != air.n_columns() + air.n_shift_columns() {
                return Err(GroupedWitnessError::LayoutMismatch);
            }
            let values = match section.source {
                GroupedSource::Table(_) => evals.clone(),
                GroupedSource::Memory => evals[..air.source_columns() - 1]
                    .iter()
                    .chain(&evals[air.source_columns()..])
                    .copied()
                    .collect(),
                GroupedSource::Bytecode => {
                    let mut values = Vec::new();
                    for selector in 0..section.group_widths[0] {
                        let offset = selector * (N_INSTRUCTION_COLUMNS + 1);
                        values.push((0..N_INSTRUCTION_COLUMNS).map(|i| beta_eq[i] * evals[offset + i]).sum());
                        values.push(evals[offset + N_INSTRUCTION_COLUMNS]);
                    }
                    values.extend_from_slice(&evals[air.source_columns()..]);
                    values
                }
            };
            assert_eq!(values.len(), grouped_section_claim_count(section));
            sections.push(values);
        }
        Ok(Self { sections })
    }

    pub fn observe_prover(&self, prover: &mut impl FSProver<EF>) {
        for values in &self.sections {
            prover.add_extension_scalars(values);
        }
    }

    pub fn read_verifier(layout: &GroupedLayout, verifier: &mut impl FSVerifier<EF>) -> ProofResult<Self> {
        Ok(Self {
            sections: layout
                .sections
                .iter()
                .map(|s| verifier.next_extension_scalars_vec(grouped_section_claim_count(s)))
                .collect::<ProofResult<_>>()?,
        })
    }

    fn expanded(&self, layout: &GroupedLayout, point: &[EF]) -> Result<Vec<Vec<EF>>, GroupedWitnessError> {
        if self.sections.len() != layout.sections.len() {
            return Err(GroupedWitnessError::LayoutMismatch);
        }
        let mut all = Vec::new();
        for (section, values) in layout.sections.iter().zip(&self.sections) {
            if values.len() != grouped_section_claim_count(section) || point.len() < section.log_n_rows {
                return Err(GroupedWitnessError::LayoutMismatch);
            }
            let air = GroupedAir {
                layout: section.clone(),
                kind: GroupedAirKind::Constraints,
            };
            let mut expanded = vec![EF::ZERO; air.n_columns() + air.n_shift_columns()];
            match section.source {
                GroupedSource::Table(_) => expanded.copy_from_slice(values),
                GroupedSource::Memory => {
                    let count = air.source_columns() - 1;
                    expanded[..count].copy_from_slice(&values[..count]);
                    expanded[air.source_columns()..].copy_from_slice(&values[count..]);
                }
                GroupedSource::Bytecode => {
                    for selector in 0..section.group_widths[0] {
                        let offset = selector * (N_INSTRUCTION_COLUMNS + 1);
                        expanded[offset] = values[2 * selector];
                        expanded[offset + N_INSTRUCTION_COLUMNS] = values[2 * selector + 1];
                    }
                    expanded[air.source_columns()..].copy_from_slice(&values[2 * section.group_widths[0]..]);
                }
            }
            if !matches!(section.source, GroupedSource::Table(_)) {
                expanded[air.source_columns() - 1] =
                    mle_of_01234567_etc(&natural_ordering_point_for_session(point, section.log_n_rows));
            }
            all.push(expanded);
        }
        Ok(all)
    }

    pub fn evaluate(
        &self,
        layout: &GroupedLayout,
        gamma: EF,
        beta_eq: &[EF],
        eq_point: &[EF],
        alpha: EF,
        balance_weight: EF,
        sumcheck_point: &[EF],
    ) -> Result<EF, GroupedWitnessError> {
        let expanded = self.expanded(layout, sumcheck_point)?;
        super::air::grouped_final_evaluation_inner(
            layout,
            &expanded,
            gamma,
            beta_eq,
            eq_point,
            alpha,
            balance_weight,
            sumcheck_point,
            true,
        )
    }
}

#[derive(Debug, Clone)]
pub struct GroupedPcsLayout {
    pub primary_n_vars: usize,
    pub fixed_n_vars: usize,
    pub helper_n_vars: usize,
    pub memory_log: usize,
    pub bytecode_log: usize,
    /// Base-field offset of this execution's instruction table in the trusted fixed polynomial.
    pub fixed_bytecode_offset: usize,
    pub ending_pc: usize,
}

/// Build the three ordered opening groups. Public memory and carried program
/// claims are supplied by the enclosing execution protocol.
pub fn grouped_pcs_statements(
    layout: &GroupedLayout,
    claims: &GroupedFinalClaims,
    sumcheck_point: &[EF],
    lookup_beta: &[EF],
    pcs: &GroupedPcsLayout,
    mut primary: Vec<SparseStatement<EF>>,
    mut fixed: Vec<SparseStatement<EF>>,
) -> Result<[Vec<SparseStatement<EF>>; 3], GroupedWitnessError> {
    if lookup_beta.len() != LOG_MAX_BUS_WIDTH
        || pcs.memory_log > 30
        || pcs.bytecode_log > 27
        || pcs.primary_n_vars > 31
        || pcs.fixed_n_vars > 31
        || pcs.helper_n_vars > 31
        || layout.sections.iter().any(|s| s.log_n_rows > 30)
    {
        return Err(GroupedWitnessError::LayoutMismatch);
    }
    let mut heights = BTreeMap::new();
    for section in &layout.sections {
        if let GroupedSource::Table(table) = section.source {
            heights.insert(table, section.log_n_rows);
        }
    }
    if heights.len() != ALL_TABLES.len()
        || *layout != GroupedLayout::new(pcs.memory_log, pcs.bytecode_log, &heights)
        || pcs.memory_log < *heights.values().max().unwrap()
        || pcs.fixed_bytecode_offset % (1 << (pcs.bytecode_log + LOG_MAX_BUS_WIDTH)) != 0
        || pcs
            .fixed_bytecode_offset
            .checked_add(1 << (pcs.bytecode_log + LOG_MAX_BUS_WIDTH))
            .is_none_or(|end| end > 1 << pcs.fixed_n_vars)
    {
        return Err(GroupedWitnessError::LayoutMismatch);
    }
    let source_len = (2 << pcs.memory_log)
        + (1 << pcs.bytecode_log.max(*heights.values().max().unwrap()))
        + heights.iter().map(|(t, &h)| t.n_columns() << h).sum::<usize>();
    if source_len > 1 << pcs.primary_n_vars || layout.helper_base_fields > 1 << pcs.helper_n_vars {
        return Err(GroupedWitnessError::LayoutMismatch);
    }
    let expanded = claims.expanded(layout, sumcheck_point)?;
    let mut table_claims = CommittedStatements::new();
    for ((section, values), evals) in layout.sections.iter().zip(&claims.sections).zip(&expanded) {
        let h = section.log_n_rows;
        let point = MultilinearPoint(natural_ordering_point_for_session(sumcheck_point, h));
        match section.source {
            GroupedSource::Memory => {
                let mut opens = Vec::new();
                for selector in 0..section.group_widths[0] {
                    opens.push(SparseValue::new(selector, values[2 * selector]));
                    opens.push(SparseValue::new(
                        (1 << (pcs.memory_log - h)) + selector,
                        values[2 * selector + 1],
                    ));
                }
                primary.push(SparseStatement::new(pcs.primary_n_vars, point, opens));
            }
            GroupedSource::Bytecode => {
                let selector_start = (2 << pcs.memory_log) >> h;
                primary.push(SparseStatement::new(
                    pcs.primary_n_vars,
                    point.clone(),
                    (0..section.group_widths[0])
                        .map(|selector| SparseValue::new(selector_start + selector, values[2 * selector + 1]))
                        .collect(),
                ));
                let fixed_point = MultilinearPoint([point.0, lookup_beta.to_vec()].concat());
                let fixed_selector_start = pcs.fixed_bytecode_offset >> fixed_point.len();
                fixed.push(SparseStatement::new(
                    pcs.fixed_n_vars,
                    fixed_point,
                    (0..section.group_widths[0])
                        .map(|selector| SparseValue::new(fixed_selector_start + selector, values[2 * selector]))
                        .collect(),
                ));
            }
            GroupedSource::Table(table) => {
                let air = GroupedAir {
                    layout: section.clone(),
                    kind: GroupedAirKind::Constraints,
                };
                let flat = (0..table.n_columns()).map(|i| (i, evals[i])).collect();
                let shifted = (0..table.n_shift_columns())
                    .map(|i| (i, evals[air.n_columns() + i]))
                    .collect();
                table_claims.insert(table, vec![(point, flat, shifted)]);
            }
        }
    }
    primary = stacked_pcs_global_statements(
        pcs.primary_n_vars,
        pcs.memory_log,
        pcs.bytecode_log,
        pcs.ending_pc,
        primary,
        &heights,
        &table_claims,
    );
    let helper = grouped_helper_statements(layout, &expanded, sumcheck_point, pcs.helper_n_vars)?;
    Ok([primary, fixed, helper])
}
