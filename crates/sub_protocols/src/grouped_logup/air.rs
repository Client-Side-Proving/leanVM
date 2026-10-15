use super::*;
use crate::{AirSumcheckSession, OuterSumcheckSession, compute_shifted_columns, reorder_columns_for_air};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GroupedAirKind {
    Constraints,
    Balance,
}

#[derive(Debug, Clone)]
pub struct GroupedAir {
    pub layout: GroupedSectionLayout,
    pub kind: GroupedAirKind,
}

impl GroupedAir {
    pub fn source_columns(&self) -> usize {
        match self.layout.source {
            GroupedSource::Table(table) => table.n_columns(),
            GroupedSource::Memory => 2 * self.layout.group_widths[0] + 1,
            GroupedSource::Bytecode => (N_INSTRUCTION_COLUMNS + 1) * self.layout.group_widths[0] + 1,
        }
    }

    pub fn extra_data(gamma: EF, beta_eq: &[EF], alpha_powers: Vec<EF>) -> ExtraDataForBuses<EF> {
        assert_eq!(beta_eq.len(), 1 << LOG_MAX_BUS_WIDTH);
        let mut constants = beta_eq.to_vec();
        constants.push(gamma);
        constants.extend((0..DIMENSION).map(|i| <EF as BasedVectorSpace<F>>::ith_basis_element(i).unwrap()));
        ExtraDataForBuses::new(&constants, alpha_powers)
    }

    /// Prover columns in natural row order. Memory/bytecode rows contain an
    /// explicit low address column; its final value must be checked against the
    /// public address polynomial. Bytecode columns are kept expanded here.
    pub fn columns(&self, inputs: &GroupedInputs<'_>, helpers: &GroupedSectionWitness) -> Vec<ArenaVec<F>> {
        assert_eq!(self.layout, helpers.layout);
        let height = 1 << self.layout.log_n_rows;
        let mut columns = match self.layout.source {
            GroupedSource::Table(table) => inputs.traces[&table].columns[..table.n_columns()].to_vec(),
            GroupedSource::Memory => (0..self.layout.group_widths[0])
                .flat_map(|selector| {
                    let range = selector * height..(selector + 1) * height;
                    [
                        ArenaVec::from_iter(inputs.memory[range.clone()].iter().copied()),
                        ArenaVec::from_iter(inputs.memory_acc[range].iter().copied()),
                    ]
                })
                .collect(),
            GroupedSource::Bytecode => (0..self.layout.group_widths[0])
                .flat_map(|selector| {
                    let mut result = (0..N_INSTRUCTION_COLUMNS)
                        .map(|column| {
                            ArenaVec::from_iter((0..height).map(|row| {
                                inputs.bytecode[((selector << self.layout.log_n_rows) + row)
                                    * N_INSTRUCTION_COLUMNS.next_power_of_two()
                                    + column]
                            }))
                        })
                        .collect::<Vec<_>>();
                    result.push(ArenaVec::from_iter(
                        inputs.bytecode_acc[selector * height..(selector + 1) * height]
                            .iter()
                            .copied(),
                    ));
                    result
                })
                .collect(),
        };
        if !matches!(self.layout.source, GroupedSource::Table(_)) {
            columns.push(ArenaVec::from_iter((0..height).map(F::from_usize)));
        }
        for inverses in &helpers.inverses {
            for basis in 0..DIMENSION {
                columns.push(ArenaVec::from_iter(
                    inverses.iter().map(|value| value.as_basis_coefficients_slice()[basis]),
                ));
            }
        }
        if let GroupedSource::Table(table) = self.layout.source {
            let shifted = compute_shifted_columns(
                table.n_shift_columns(),
                &columns.iter().map(|c| c.as_slice()).collect::<Vec<_>>(),
            );
            columns.extend(shifted);
        }
        assert_eq!(columns.len(), self.n_columns() + self.n_shift_columns());
        columns
    }
}

struct OriginalAirView<'a, AB> {
    inner: &'a mut AB,
    n_columns: usize,
}

impl<AB: AirBuilder> AirBuilder for OriginalAirView<'_, AB> {
    type F = AB::F;
    type IF = AB::IF;
    type EF = AB::EF;
    fn flat(&self) -> &[Self::IF] {
        &self.inner.flat()[..self.n_columns]
    }
    fn shift(&self) -> &[Self::IF] {
        self.inner.shift()
    }
    fn assert_zero(&mut self, x: Self::IF) {
        self.inner.assert_zero(x);
    }
    fn assert_zero_ef(&mut self, x: Self::EF) {
        self.inner.assert_zero_ef(x);
    }
}

impl Air for GroupedAir {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns(&self) -> usize {
        self.source_columns() + self.layout.group_widths.len() * DIMENSION
    }
    fn n_shift_columns(&self) -> usize {
        match self.layout.source {
            GroupedSource::Table(table) => table.n_shift_columns(),
            _ => 0,
        }
    }
    fn n_constraints(&self) -> usize {
        if self.kind == GroupedAirKind::Balance {
            return 1;
        }
        let original = match self.layout.source {
            GroupedSource::Table(table) => table.n_constraints() - 2,
            _ => 0,
        };
        original + self.layout.group_widths.len()
    }
    fn degree_air(&self) -> usize {
        let width = self.layout.group_widths[0];
        match (self.kind, self.layout.source) {
            (GroupedAirKind::Constraints, GroupedSource::Table(Table::Execution(_))) => 7,
            (GroupedAirKind::Constraints, GroupedSource::Table(Table::ExtensionOp(_))) => 9,
            (GroupedAirKind::Constraints, GroupedSource::Table(Table::Poseidon16(_))) => 10,
            (GroupedAirKind::Balance, GroupedSource::Table(Table::Execution(_))) => 7,
            (GroupedAirKind::Balance, GroupedSource::Table(Table::ExtensionOp(_))) => 10,
            (GroupedAirKind::Balance, GroupedSource::Table(Table::Poseidon16(_))) => 9,
            _ => width + 1,
        }
    }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra: &Self::ExtraData) {
        if self.kind == GroupedAirKind::Constraints {
            if let GroupedSource::Table(table) = self.layout.source {
                let mut view = OriginalAirView {
                    inner: builder,
                    n_columns: table.n_columns(),
                };
                match table {
                    Table::Execution(_) => ExecutionTable::<false>.eval(&mut view, extra),
                    Table::ExtensionOp(_) => ExtensionOpPrecompile::<false>.eval(&mut view, extra),
                    Table::Poseidon16(_) => Poseidon16Precompile::<false>.eval(&mut view, extra),
                }
            }
        }
        let constants = extra.transmute_bus_data::<AB::EF>();
        let n_beta = 1 << LOG_MAX_BUS_WIDTH;
        let beta = &constants[..n_beta];
        let gamma = constants[n_beta];
        let basis = &constants[n_beta + 1..];
        let flat = builder.flat().iter().map(|&x| AB::EF::ZERO + x).collect::<Vec<_>>();
        let fractions = match self.layout.source {
            GroupedSource::Table(table) => table_fractions(
                table,
                &table.bus_interactions(),
                &flat[..table.n_columns()],
                gamma,
                beta,
            ),
            source => {
                let row = flat[self.source_columns() - 1];
                (0..self.layout.group_widths[0])
                    .map(|selector| {
                        let address = row + AB::EF::from_usize(selector << self.layout.log_n_rows);
                        let (numerator, fingerprint) = if source == GroupedSource::Memory {
                            (
                                -flat[2 * selector + 1],
                                beta[0] * address
                                    + beta[1] * flat[2 * selector]
                                    + beta[n_beta - 1] * AB::EF::from_usize(LOGUP_MEMORY_DOMAINSEP),
                            )
                        } else {
                            let offset = selector * (N_INSTRUCTION_COLUMNS + 1);
                            let mut fingerprint = beta[N_INSTRUCTION_COLUMNS] * address
                                + beta[n_beta - 1] * AB::EF::from_usize(LOGUP_BYTECODE_DOMAINSEP);
                            for i in 0..N_INSTRUCTION_COLUMNS {
                                fingerprint += beta[i] * flat[offset + i];
                            }
                            (-flat[offset + N_INSTRUCTION_COLUMNS], fingerprint)
                        };
                        Fraction {
                            numerator,
                            denominator: gamma - fingerprint,
                        }
                    })
                    .collect()
            }
        };
        let mut balance = AB::EF::ZERO;
        for (group, fractions) in fractions.chunks(GROUP_WIDTH).enumerate() {
            let fraction = combine_fractions(fractions);
            let inverse = (0..DIMENSION)
                .map(|k| basis[k] * flat[self.source_columns() + group * DIMENSION + k])
                .sum::<AB::EF>();
            if self.kind == GroupedAirKind::Constraints {
                builder.assert_zero_ef(inverse * fraction.denominator - AB::EF::ONE);
            } else {
                balance += inverse * fraction.numerator;
            }
        }
        if self.kind == GroupedAirKind::Balance {
            builder.assert_zero_ef(balance);
        }
    }
}

/// Build native sessions for equality-weighted constraints and the unweighted
/// balance. The latter uses eq(1/2, x) = 2^-h with a compensating 2^h weight.
/// The caller must bind all source/helper polynomials before sampling weights.
pub fn grouped_sessions(
    inputs: &GroupedInputs<'_>,
    witness: &GroupedWitness,
    gamma: EF,
    beta_eq: &[EF],
    eq_point: &[EF],
    alpha: EF,
    balance_weight: EF,
) -> Vec<Box<dyn OuterSumcheckSession<EF>>> {
    let max_log = witness.layout.sections.iter().map(|s| s.log_n_rows).max().unwrap();
    assert_eq!(eq_point.len(), max_log);
    let mut sessions: Vec<Box<dyn OuterSumcheckSession<EF>>> = Vec::new();
    let mut alpha_power = EF::ONE;
    for section in &witness.sections {
        let h = section.layout.log_n_rows;
        for kind in [GroupedAirKind::Constraints, GroupedAirKind::Balance] {
            let air = GroupedAir {
                layout: section.layout.clone(),
                kind,
            };
            let (weights, eq, sum) = if kind == GroupedAirKind::Constraints {
                let weights = (0..air.n_constraints())
                    .map(|_| {
                        let a = alpha_power;
                        alpha_power *= alpha;
                        a
                    })
                    .collect();
                (weights, eq_point[max_log - h..].to_vec(), EF::ZERO)
            } else {
                (
                    vec![balance_weight * EF::from_usize(1 << h)],
                    vec![EF::ONE.halve(); h],
                    balance_weight * section.balance,
                )
            };
            let mut columns = air.columns(inputs, section);
            reorder_columns_for_air(&mut columns);
            let extra = GroupedAir::extra_data(gamma, beta_eq, weights);
            sessions.push(Box::new(AirSumcheckSession::new_owned_reordered(
                columns,
                eq,
                sum,
                air,
                extra,
                1 << h,
            )));
        }
    }
    sessions
}

/// Evaluate the terminal sumcheck relation from column claims. The caller must
/// authenticate these claims with a PCS; this function only checks algebra.
pub fn grouped_final_evaluation(
    layout: &GroupedLayout,
    column_evals: &[Vec<EF>],
    gamma: EF,
    beta_eq: &[EF],
    eq_point: &[EF],
    alpha: EF,
    balance_weight: EF,
    sumcheck_point: &[EF],
) -> Result<EF, GroupedWitnessError> {
    grouped_final_evaluation_inner(
        layout,
        column_evals,
        gamma,
        beta_eq,
        eq_point,
        alpha,
        balance_weight,
        sumcheck_point,
        false,
    )
}

pub(super) fn grouped_final_evaluation_inner(
    layout: &GroupedLayout,
    column_evals: &[Vec<EF>],
    gamma: EF,
    beta_eq: &[EF],
    eq_point: &[EF],
    alpha: EF,
    balance_weight: EF,
    sumcheck_point: &[EF],
    compact_bytecode: bool,
) -> Result<EF, GroupedWitnessError> {
    let max_log = layout.sections.iter().map(|s| s.log_n_rows).max().unwrap();
    if eq_point.len() != max_log || sumcheck_point.len() != max_log || column_evals.len() != layout.sections.len() {
        return Err(GroupedWitnessError::LayoutMismatch);
    }
    let mut alpha_power = EF::ONE;
    let mut total = EF::ZERO;
    for (section, evals) in layout.sections.iter().zip(column_evals) {
        // In the compact representation, slot zero of each bytecode row
        // contains its already fingerprinted instruction evaluation.
        let mut section_beta = beta_eq.to_vec();
        if compact_bytecode && section.source == GroupedSource::Bytecode {
            section_beta[..N_INSTRUCTION_COLUMNS].fill(EF::ZERO);
            section_beta[0] = EF::ONE;
        }
        let air = GroupedAir {
            layout: section.clone(),
            kind: GroupedAirKind::Constraints,
        };
        let h = section.log_n_rows;
        if evals.len() != air.n_columns() + air.n_shift_columns() {
            return Err(GroupedWitnessError::LayoutMismatch);
        }
        let point = crate::natural_ordering_point_for_session(sumcheck_point, h);
        if !matches!(section.source, GroupedSource::Table(_))
            && evals[air.source_columns() - 1] != mle_of_01234567_etc(&point)
        {
            return Err(GroupedWitnessError::LayoutMismatch);
        }
        let padding = sumcheck_point[..max_log - h].iter().copied().product::<EF>();
        let weights = (0..air.n_constraints())
            .map(|_| {
                let a = alpha_power;
                alpha_power *= alpha;
                a
            })
            .collect();
        let extra = GroupedAir::extra_data(gamma, &section_beta, weights);
        let constraint = air.eval_extension(evals, &extra);
        let eq = MultilinearPoint(eq_point[max_log - h..].to_vec()).eq_poly_outside(&MultilinearPoint(point));
        let balance_air = GroupedAir {
            kind: GroupedAirKind::Balance,
            ..air
        };
        let extra = GroupedAir::extra_data(gamma, &section_beta, vec![balance_weight]);
        total += padding * (eq * constraint + balance_air.eval_extension(evals, &extra));
    }
    Ok(total)
}

/// Sparse PCS claims for all five base-field coordinates of every helper.
pub fn grouped_helper_statements(
    layout: &GroupedLayout,
    column_evals: &[Vec<EF>],
    sumcheck_point: &[EF],
    helper_n_vars: usize,
) -> Result<Vec<SparseStatement<EF>>, GroupedWitnessError> {
    if layout.sections.len() != column_evals.len() || layout.helper_base_fields > 1 << helper_n_vars {
        return Err(GroupedWitnessError::LayoutMismatch);
    }
    let mut statements = Vec::new();
    for (section, evals) in layout.sections.iter().zip(column_evals) {
        let air = GroupedAir {
            layout: section.clone(),
            kind: GroupedAirKind::Constraints,
        };
        if sumcheck_point.len() < section.log_n_rows || evals.len() != air.n_columns() + air.n_shift_columns() {
            return Err(GroupedWitnessError::LayoutMismatch);
        }
        let selector_start = section.helper_offset >> section.log_n_rows;
        statements.push(SparseStatement::new(
            helper_n_vars,
            MultilinearPoint(crate::natural_ordering_point_for_session(
                sumcheck_point,
                section.log_n_rows,
            )),
            (0..section.group_widths.len() * DIMENSION)
                .map(|i| SparseValue::new(selector_start + i, evals[air.source_columns() + i]))
                .collect(),
        ));
    }
    Ok(statements)
}
