//! Experimental grouped LogUp witness and polynomial relations.
//!
//! This module does not yet define a proof mode or a Fiat-Shamir transcript.
use backend::*;
use lean_vm::*;
use std::collections::BTreeMap;

mod air;
pub use air::*;
mod pcs;
pub use pcs::*;

pub const GROUP_WIDTH: usize = 8;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum GroupedSource {
    Memory,
    Bytecode,
    Table(Table),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroupedSectionLayout {
    pub source: GroupedSource,
    pub log_n_rows: usize,
    pub group_widths: Vec<usize>,
    /// Base-field offset in the helper polynomial. Groups precede basis coordinates.
    pub helper_offset: usize,
}

impl GroupedSectionLayout {
    pub fn n_helpers(&self) -> usize {
        self.group_widths.len() << self.log_n_rows
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GroupedLayout {
    pub sections: Vec<GroupedSectionLayout>,
    pub helper_base_fields: usize,
}

impl GroupedLayout {
    pub fn new(memory_log: usize, bytecode_log: usize, table_heights: &BTreeMap<Table, usize>) -> Self {
        let mut sections = Vec::new();
        for (source, log) in [
            (GroupedSource::Memory, memory_log),
            (GroupedSource::Bytecode, bytecode_log),
        ] {
            let selector_log = log.min(3);
            sections.push(GroupedSectionLayout {
                source,
                log_n_rows: log - selector_log,
                group_widths: vec![1 << selector_log],
                helper_offset: 0,
            });
        }
        for (&table, &log_n_rows) in table_heights {
            let n_buses = table.bus_interactions().len();
            sections.push(GroupedSectionLayout {
                source: GroupedSource::Table(table),
                log_n_rows,
                group_widths: (0..n_buses)
                    .step_by(GROUP_WIDTH)
                    .map(|i| GROUP_WIDTH.min(n_buses - i))
                    .collect(),
                helper_offset: 0,
            });
        }
        sections.sort_by_key(|section| (std::cmp::Reverse(section.log_n_rows), section.source));
        let mut offset = 0;
        for section in &mut sections {
            assert_eq!(offset % (1 << section.log_n_rows), 0);
            section.helper_offset = offset;
            offset += section.n_helpers() * DIMENSION;
        }
        Self {
            sections,
            helper_base_fields: offset,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Fraction<R> {
    pub numerator: R,
    pub denominator: R,
}

/// Homogeneous addition of fractions, without division or a nonzero assumption.
pub fn combine_fractions<R: PrimeCharacteristicRing + Copy>(fractions: &[Fraction<R>]) -> Fraction<R> {
    assert!(!fractions.is_empty() && fractions.len() <= GROUP_WIDTH);
    fractions.iter().fold(
        Fraction {
            numerator: R::ZERO,
            denominator: R::ONE,
        },
        |acc, fraction| Fraction {
            numerator: acc.numerator * fraction.denominator + fraction.numerator * acc.denominator,
            denominator: acc.denominator * fraction.denominator,
        },
    )
}

pub fn table_fractions<R: PrimeCharacteristicRing + Copy>(
    table: Table,
    buses: &[BusInteraction],
    committed_columns: &[R],
    gamma: R,
    beta_eq: &[R],
) -> Vec<Fraction<R>> {
    let columns = reconstruct_bus_columns(table, committed_columns);
    buses
        .iter()
        .map(|bus| {
            let multiplicity = match bus.multiplicity {
                BusMultiplicity::One => R::ONE,
                BusMultiplicity::Column(index) => columns[index],
            };
            let numerator = match bus.direction {
                BusDirection::Push => multiplicity,
                BusDirection::Pull => -multiplicity,
            };
            let mut fingerprint = *beta_eq.last().unwrap() * resolve_bus_data(bus.domainsep, &columns);
            assert!(beta_eq.len() > bus.data.len());
            for (&weight, &entry) in beta_eq.iter().zip(&bus.data) {
                fingerprint += weight * resolve_bus_data(entry, &columns);
            }
            Fraction {
                numerator,
                denominator: gamma - fingerprint,
            }
        })
        .collect()
}

#[derive(Debug, Clone, Copy)]
pub struct GroupedInputs<'a> {
    pub memory: &'a [F],
    pub memory_acc: &'a [F],
    pub bytecode: &'a [F],
    pub bytecode_acc: &'a [F],
    pub traces: &'a BTreeMap<Table, TableTrace>,
}

impl GroupedInputs<'_> {
    pub fn layout(&self) -> GroupedLayout {
        assert!(self.memory.len().is_power_of_two());
        assert_eq!(self.memory.len(), self.memory_acc.len());
        assert!(self.bytecode_acc.len().is_power_of_two());
        assert_eq!(
            self.bytecode.len(),
            self.bytecode_acc.len() * N_INSTRUCTION_COLUMNS.next_power_of_two()
        );
        GroupedLayout::new(
            log2_strict_usize(self.memory.len()),
            log2_strict_usize(self.bytecode_acc.len()),
            &self
                .traces
                .iter()
                .map(|(&table, trace)| (table, trace.log_n_rows))
                .collect(),
        )
    }

    pub fn row_fractions(
        &self,
        section: &GroupedSectionLayout,
        row: usize,
        gamma: EF,
        beta_eq: &[EF],
    ) -> Vec<Fraction<EF>> {
        assert!(row < 1 << section.log_n_rows);
        match section.source {
            GroupedSource::Memory => (0..section.group_widths[0])
                .map(|selector| {
                    let address = (selector << section.log_n_rows) + row;
                    Fraction {
                        numerator: -EF::from(self.memory_acc[address]),
                        denominator: gamma
                            - finger_print(
                                EF::from_usize(LOGUP_MEMORY_DOMAINSEP),
                                &[EF::from_usize(address), EF::from(self.memory[address])],
                                beta_eq,
                            ),
                    }
                })
                .collect(),
            GroupedSource::Bytecode => (0..section.group_widths[0])
                .map(|selector| {
                    let address = (selector << section.log_n_rows) + row;
                    let mut data: Vec<EF> = self.bytecode[address * N_INSTRUCTION_COLUMNS.next_power_of_two()..]
                        [..N_INSTRUCTION_COLUMNS]
                        .iter()
                        .copied()
                        .map(EF::from)
                        .collect();
                    data.push(EF::from_usize(address));
                    Fraction {
                        numerator: -EF::from(self.bytecode_acc[address]),
                        denominator: gamma - finger_print(EF::from_usize(LOGUP_BYTECODE_DOMAINSEP), &data, beta_eq),
                    }
                })
                .collect(),
            GroupedSource::Table(table) => {
                let flat = self.traces[&table].columns[..table.n_columns()]
                    .iter()
                    .map(|column| EF::from(column[row]))
                    .collect::<Vec<_>>();
                table_fractions(table, &table.bus_interactions(), &flat, gamma, beta_eq)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct GroupedSectionWitness {
    pub layout: GroupedSectionLayout,
    /// Group-major inverse products in natural Boolean row order.
    pub inverses: Vec<Vec<EF>>,
    pub balance: EF,
}

#[derive(Debug, Clone)]
pub struct GroupedWitness {
    pub layout: GroupedLayout,
    pub sections: Vec<GroupedSectionWitness>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GroupedWitnessError {
    ZeroDenominator {
        source: GroupedSource,
        group: usize,
        row: usize,
    },
    LayoutMismatch,
    InvalidInverse {
        source: GroupedSource,
        group: usize,
        row: usize,
    },
    UnbalancedLookup,
}

/// Montgomery batch inversion; callers have already rejected zero products.
fn invert_nonzero(values: &mut [EF]) {
    let mut prefixes = Vec::with_capacity(values.len());
    let mut product = EF::ONE;
    for &value in values.iter() {
        prefixes.push(product);
        product *= value;
    }
    let mut inverse = product.inverse();
    for (value, prefix) in values.iter_mut().zip(prefixes).rev() {
        let original = *value;
        *value = inverse * prefix;
        inverse *= original;
    }
}

impl GroupedWitness {
    pub fn build(inputs: &GroupedInputs<'_>, gamma: EF, beta_eq: &[EF]) -> Result<Self, GroupedWitnessError> {
        let layout = inputs.layout();
        let mut sections = Vec::new();
        for section in &layout.sections {
            let height = 1 << section.log_n_rows;
            let mut products = vec![vec![EF::ZERO; height]; section.group_widths.len()];
            let mut numerators = products.clone();
            for row in 0..height {
                let fractions = inputs.row_fractions(section, row, gamma, beta_eq);
                for (group, fractions) in fractions.chunks(GROUP_WIDTH).enumerate() {
                    let combined = combine_fractions(fractions);
                    if combined.denominator.is_zero() {
                        return Err(GroupedWitnessError::ZeroDenominator {
                            source: section.source,
                            group,
                            row,
                        });
                    }
                    products[group][row] = combined.denominator;
                    numerators[group][row] = combined.numerator;
                }
            }
            for products in &mut products {
                invert_nonzero(products);
            }
            let balance = products
                .iter()
                .flatten()
                .zip(numerators.iter().flatten())
                .map(|(&u, &n)| u * n)
                .sum();
            sections.push(GroupedSectionWitness {
                layout: section.clone(),
                inverses: products,
                balance,
            });
        }
        if sections.iter().map(|section| section.balance).sum::<EF>() != EF::ZERO {
            return Err(GroupedWitnessError::UnbalancedLookup);
        }
        Ok(Self { layout, sections })
    }

    pub fn base_field_polynomial(&self) -> Vec<F> {
        let mut polynomial = vec![F::ZERO; self.layout.helper_base_fields.next_power_of_two()];
        for section in &self.sections {
            let height = 1 << section.layout.log_n_rows;
            for (group, column) in section.inverses.iter().enumerate() {
                for (row, value) in column.iter().enumerate() {
                    for (basis, &coordinate) in value.as_basis_coefficients_slice().iter().enumerate() {
                        polynomial[section.layout.helper_offset + (group * DIMENSION + basis) * height + row] =
                            coordinate;
                    }
                }
            }
        }
        polynomial
    }

    /// Direct Boolean oracle for tests. This is not a succinct verifier.
    pub fn check_rows(&self, inputs: &GroupedInputs<'_>, gamma: EF, beta_eq: &[EF]) -> Result<(), GroupedWitnessError> {
        if self.layout != inputs.layout() || self.sections.len() != self.layout.sections.len() {
            return Err(GroupedWitnessError::LayoutMismatch);
        }
        let mut balance = EF::ZERO;
        for (expected, section) in self.layout.sections.iter().zip(&self.sections) {
            if expected != &section.layout
                || section.inverses.len() != expected.group_widths.len()
                || section
                    .inverses
                    .iter()
                    .any(|column| column.len() != 1 << expected.log_n_rows)
            {
                return Err(GroupedWitnessError::LayoutMismatch);
            }
            for row in 0..1 << expected.log_n_rows {
                let fractions = inputs.row_fractions(expected, row, gamma, beta_eq);
                for (group, fractions) in fractions.chunks(GROUP_WIDTH).enumerate() {
                    let fraction = combine_fractions(fractions);
                    let inverse = section.inverses[group][row];
                    if inverse * fraction.denominator != EF::ONE {
                        return Err(GroupedWitnessError::InvalidInverse {
                            source: expected.source,
                            group,
                            row,
                        });
                    }
                    balance += inverse * fraction.numerator;
                }
            }
        }
        if balance != EF::ZERO {
            return Err(GroupedWitnessError::UnbalancedLookup);
        }
        Ok(())
    }
}
