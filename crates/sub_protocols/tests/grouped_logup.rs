use backend::*;
use lean_compiler::{ProgramSource, compile_program};
use lean_prover::get_execution_trace;
use lean_vm::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use std::collections::BTreeMap;
use sub_protocols::grouped_logup::*;
use sub_protocols::{natural_ordering_point_for_session, prove_batched_air_sumcheck, stack_polynomials};

const PROGRAM: &str = r#"
def main():
    scratch = Array(256)
    for i in unroll(0, 64):
        scratch[i] = i + 1
    poseidon16_compress_half(scratch, scratch + 8, scratch + 64)
    poseidon16_compress_quarter(scratch, scratch + 8, scratch + 80)
    poseidon16_permute(scratch, scratch + 8, scratch + 96)
    poseidon16_permute_half(scratch, scratch + 8, scratch + 112)
    poseidon16_compress_half_hardcoded_left(scratch + 4, scratch + 8, scratch + 128, 0)
    poseidon16_permute_half_hardcoded_left(scratch + 4, scratch + 8, scratch + 144, 0)
    add_be(scratch, scratch + 8, scratch + 160, 2)
    add_ee(scratch, scratch + 16, scratch + 168, 2)
    dot_product_be(scratch, scratch + 8, scratch + 176, 2)
    dot_product_ee(scratch, scratch + 16, scratch + 184, 2)
    poly_eq_be(scratch, scratch + 8, scratch + 192, 2)
    poly_eq_ee(scratch, scratch + 16, scratch + 200, 2)
    return
"#;

fn with_real_trace(f: impl FnOnce(GroupedInputs<'_>)) {
    let bytecode = compile_program(&ProgramSource::Raw(PROGRAM.to_string()));
    let witness = ExecutionWitness::default();
    let executed = execute_bytecode(&bytecode, &[F::ZERO; PUBLIC_INPUT_LEN], &witness, false);
    let mut trace = get_execution_trace(&bytecode, executed, &witness.min_table_log_n_rows);
    trace
        .memory
        .resize(trace.memory.len().max(bytecode.padded_size()), F::ZERO);
    let mut memory_acc = vec![F::ZERO; trace.memory.len()];
    let mut bytecode_acc = vec![F::ZERO; bytecode.padded_size()];
    for (&table, rows) in &trace.traces {
        assert!(rows.non_padded_n_rows > 0);
        for group in memory_lookup_groups(&table.bus_interactions()) {
            for base in &rows.columns[group.idx_col] {
                for cell in &mut memory_acc[base.to_usize()..][..group.value_cols.len()] {
                    *cell += F::ONE;
                }
            }
        }
    }
    for pc in &trace.traces[&Table::execution()].columns[EXEC_COL_PC] {
        bytecode_acc[pc.to_usize()] += F::ONE;
    }
    f(GroupedInputs {
        memory: &trace.memory,
        memory_acc: &memory_acc,
        bytecode: bytecode.instructions_multilinear(),
        bytecode_acc: &bytecode_acc,
        traces: &trace.traces,
    });
}

fn challenges(seed: u64) -> (EF, Vec<EF>) {
    let mut rng = StdRng::seed_from_u64(seed);
    let beta = MultilinearPoint((0..LOG_MAX_BUS_WIDTH).map(|_| rng.random::<EF>()).collect());
    (rng.random(), eval_eq(&beta.0).to_vec())
}

#[test]
fn grouped_root_layout_preserves_alignment_and_capacity() {
    let heights = BTreeMap::from([
        (Table::execution(), 17),
        (Table::extension_op(), 15),
        (Table::poseidon16(), 13),
    ]);
    let layout = GroupedLayout::new(19, 17, &heights);
    assert_eq!(layout.helper_base_fields, 1_597_440);
    assert_eq!(layout.helper_base_fields.next_power_of_two(), 1 << 21);
    assert_eq!(layout.sections.iter().map(|s| s.group_widths.len()).sum::<usize>(), 10);
    assert_eq!(
        layout.sections.iter().map(|s| s.log_n_rows).collect::<Vec<_>>(),
        [17, 16, 15, 14, 13]
    );
    for section in &layout.sections {
        assert_eq!(section.helper_offset % (1 << section.log_n_rows), 0);
    }
    for memory_log in 0..4 {
        let small = GroupedLayout::new(memory_log, 0, &BTreeMap::new());
        assert_eq!(
            small
                .sections
                .iter()
                .find(|s| s.source == GroupedSource::Memory)
                .unwrap()
                .group_widths,
            [1 << memory_log]
        );
    }
}

#[test]
fn grouped_helpers_match_real_native_bus_fractions_and_coordinates() {
    with_real_trace(|inputs| {
        for seed in [8, 29, 103] {
            let (gamma, beta) = challenges(seed);
            let witness = GroupedWitness::build(&inputs, gamma, &beta).unwrap();
            witness.check_rows(&inputs, gamma, &beta).unwrap();
            let polynomial = witness.base_field_polynomial();
            for section in &witness.sections {
                let height = 1 << section.layout.log_n_rows;
                for (group, inverses) in section.inverses.iter().enumerate() {
                    for (row, &inverse) in inverses.iter().enumerate() {
                        let coordinates = (0..DIMENSION)
                            .map(|basis| {
                                polynomial[section.layout.helper_offset + (group * DIMENSION + basis) * height + row]
                            })
                            .collect::<Vec<_>>();
                        assert_eq!(EF::from_basis_coefficients_slice(&coordinates), Some(inverse));
                    }
                }
                // Independent rational sum, using one inversion per individual bus.
                let mut expected = EF::ZERO;
                for row in 0..height {
                    for fraction in inputs.row_fractions(&section.layout, row, gamma, &beta) {
                        expected += fraction.numerator / fraction.denominator;
                    }
                }
                assert_eq!(section.balance, expected);
            }
            assert!(
                polynomial[witness.layout.helper_base_fields..]
                    .iter()
                    .all(|x| x.is_zero())
            );
            // Compare every native temporary column, including active and padding rows.
            for (&table, trace) in inputs.traces {
                for row in 0..1 << trace.log_n_rows {
                    let flat = trace.columns[..table.n_columns()]
                        .iter()
                        .map(|c| c[row])
                        .collect::<Vec<_>>();
                    let reconstructed = reconstruct_bus_columns(table, &flat);
                    for (column, expected) in trace.columns.iter().zip(reconstructed) {
                        assert_eq!(column[row], expected);
                    }
                    // Fingerprints use native stored virtual columns as a separate oracle.
                    let columns = trace.columns.iter().map(|c| EF::from(c[row])).collect::<Vec<_>>();
                    let buses = table.bus_interactions();
                    let fractions = table_fractions(
                        table,
                        &buses,
                        &flat.into_iter().map(EF::from).collect::<Vec<_>>(),
                        gamma,
                        &beta,
                    );
                    for (bus, fraction) in buses.iter().zip(fractions) {
                        let data = bus
                            .data
                            .iter()
                            .map(|&entry| resolve_bus_data(entry, &columns))
                            .collect::<Vec<_>>();
                        assert_eq!(
                            fraction.denominator,
                            gamma - finger_print(resolve_bus_data(bus.domainsep, &columns), &data, &beta)
                        );
                        let magnitude = match bus.multiplicity {
                            BusMultiplicity::One => EF::ONE,
                            BusMultiplicity::Column(c) => columns[c],
                        };
                        assert_eq!(fraction.numerator, magnitude * EF::from(bus.direction.to_field_flag()));
                    }
                }
            }
        }
    });
}

#[test]
fn grouped_helpers_reject_invalid_inverse_balance_source_and_layout() {
    with_real_trace(|inputs| {
        let (gamma, beta) = challenges(103);
        let witness = GroupedWitness::build(&inputs, gamma, &beta).unwrap();
        for section in 0..witness.sections.len() {
            for group in 0..witness.sections[section].inverses.len() {
                let mut changed = witness.clone();
                changed.sections[section].inverses[group][0] += EF::ONE;
                assert!(matches!(
                    changed.check_rows(&inputs, gamma, &beta),
                    Err(GroupedWitnessError::InvalidInverse { .. })
                ));
            }
        }
        let section = witness
            .sections
            .iter()
            .position(|s| s.layout.source == GroupedSource::Table(Table::execution()))
            .unwrap();
        let layout = &witness.sections[section].layout;
        let n0 = combine_fractions(&inputs.row_fractions(layout, 0, gamma, &beta)).numerator;
        let n1 = combine_fractions(&inputs.row_fractions(layout, 1, gamma, &beta)).numerator;
        assert!(!n1.is_zero());
        let mut changed = witness.clone();
        changed.sections[section].inverses[0][0] += EF::ONE;
        changed.sections[section].inverses[0][1] -= n0 / n1;
        assert_eq!(
            n0 + (changed.sections[section].inverses[0][1] - witness.sections[section].inverses[0][1]) * n1,
            EF::ZERO
        );
        assert!(matches!(
            changed.check_rows(&inputs, gamma, &beta),
            Err(GroupedWitnessError::InvalidInverse { .. })
        ));

        let mut changed_acc = inputs.bytecode_acc.to_vec();
        changed_acc[0] += F::ONE;
        let unbalanced = GroupedInputs {
            bytecode_acc: &changed_acc,
            ..inputs
        };
        assert!(matches!(
            witness.check_rows(&unbalanced, gamma, &beta),
            Err(GroupedWitnessError::UnbalancedLookup)
        ));
        assert!(matches!(
            GroupedWitness::build(&unbalanced, gamma, &beta),
            Err(GroupedWitnessError::UnbalancedLookup)
        ));

        let mut changed = witness.clone();
        changed.sections[0].inverses[0].pop();
        assert_eq!(
            changed.check_rows(&inputs, gamma, &beta),
            Err(GroupedWitnessError::LayoutMismatch)
        );
        let mut changed = witness.clone();
        changed.layout.sections[0].helper_offset += 1;
        assert_eq!(
            changed.check_rows(&inputs, gamma, &beta),
            Err(GroupedWitnessError::LayoutMismatch)
        );
        let zero_gamma = finger_print(
            EF::from_usize(LOGUP_MEMORY_DOMAINSEP),
            &[EF::ZERO, EF::from(inputs.memory[0])],
            &beta,
        );
        assert!(matches!(
            GroupedWitness::build(&inputs, zero_gamma, &beta),
            Err(GroupedWitnessError::ZeroDenominator { .. })
        ));
    });
}

struct DeclaredBus {
    flat: Vec<EF>,
    shift: Vec<EF>,
    declared: Vec<EF>,
}
impl AirBuilder for DeclaredBus {
    type F = F;
    type IF = EF;
    type EF = EF;
    fn flat(&self) -> &[EF] {
        &self.flat
    }
    fn shift(&self) -> &[EF] {
        &self.shift
    }
    fn assert_zero(&mut self, _: EF) {}
    fn assert_zero_ef(&mut self, _: EF) {}
    fn declare_values(&mut self, values: &[EF]) {
        self.declared.extend(values);
    }
}

#[test]
fn grouped_virtual_expressions_match_native_air_away_from_boolean_cube() {
    let mut rng = StdRng::seed_from_u64(823);
    for table in ALL_TABLES {
        for _ in 0..40 {
            let mut builder = DeclaredBus {
                flat: (0..table.n_columns()).map(|_| rng.random()).collect(),
                shift: (0..table.n_shift_columns()).map(|_| rng.random()).collect(),
                declared: Vec::new(),
            };
            let extra = ExtraDataForBuses::default();
            match table {
                Table::Execution(_) => ExecutionTable::<false>.eval(&mut builder, &extra),
                Table::ExtensionOp(_) => ExtensionOpPrecompile::<false>.eval(&mut builder, &extra),
                Table::Poseidon16(_) => Poseidon16Precompile::<false>.eval(&mut builder, &extra),
            }
            assert_eq!(builder.declared.len(), 5);
            let columns = reconstruct_bus_columns(table, &builder.flat);
            let bus = table.bus_interactions().remove(0);
            let BusMultiplicity::Column(index) = bus.multiplicity else {
                panic!("expected virtual multiplicity")
            };
            assert_eq!(columns[index], builder.declared[0]);
            assert_eq!(resolve_bus_data(bus.domainsep, &columns), builder.declared[4]);
            for (entry, expected) in bus.data.into_iter().zip(&builder.declared[1..4]) {
                assert_eq!(resolve_bus_data(entry, &columns), *expected);
            }
        }
    }
}

#[test]
fn grouped_native_keccak_sumcheck_matches_direct_column_oracle_and_rejects_messages() {
    with_real_trace(|inputs| {
        // This test binds complete Boolean columns as an oracle. It exercises
        // native transcript/sumcheck encoding, without claiming a succinct PCS.
        let mut binding = b"leanvm-grouped-sumcheck-oracle-test-v1"
            .iter()
            .map(|&b| F::from_u8(b))
            .collect::<Vec<_>>();
        for column in [inputs.memory, inputs.memory_acc, inputs.bytecode, inputs.bytecode_acc] {
            binding.push(F::from_usize(column.len()));
            binding.extend(column);
        }
        for (&table, trace) in inputs.traces {
            binding.extend([F::from_usize(table.index()), F::from_usize(trace.log_n_rows)]);
            for column in &trace.columns[..table.n_columns()] {
                binding.extend(column.iter().copied());
            }
        }
        let permutation = get_poseidon16().clone();
        let capacity = [F::ZERO; 8];
        let mut prover =
            ProverState::<EF, _>::new_with_hash_profile(permutation.clone(), capacity, ProofHashProfile::Keccak240);
        prover.observe_scalars(&binding);
        let gamma = prover.sample();
        prover.duplex();
        let beta = eval_eq(&prover.sample_vec(LOG_MAX_BUS_WIDTH)).to_vec();
        let witness = GroupedWitness::build(&inputs, gamma, &beta).unwrap();
        let helper_poly = witness.base_field_polynomial();
        prover.observe_scalars(&helper_poly);
        prover.duplex();
        let h = witness.layout.sections.iter().map(|s| s.log_n_rows).max().unwrap();
        let eq = prover.sample_vec(h);
        let alpha = prover.sample();
        let balance_weight = prover.sample();
        let mut sessions = grouped_sessions(&inputs, &witness, gamma, &beta, &eq, alpha, balance_weight);
        assert_eq!(sessions.iter().map(|s| s.bare_degree() + 1).max(), Some(11));
        assert_eq!(sessions.iter().map(|s| s.sum()).sum::<EF>(), EF::ZERO);
        let point = prove_batched_air_sumcheck(&mut prover, &mut sessions);
        let mut column_evals = Vec::new();
        for (section, pair) in witness.sections.iter().zip(sessions.chunks(2)) {
            let evals = pair[0].final_column_evals();
            assert_eq!(evals, pair[1].final_column_evals());
            let air = GroupedAir {
                layout: section.layout.clone(),
                kind: GroupedAirKind::Constraints,
            };
            let natural = MultilinearPoint(natural_ordering_point_for_session(&point.0, section.layout.log_n_rows));
            let columns = air.columns(&inputs, section);
            for (column, value) in columns.iter().zip(&evals) {
                assert_eq!(column.as_slice().evaluate(&natural), *value);
            }
            column_evals.push(evals);
        }
        let expected = grouped_final_evaluation(
            &witness.layout,
            &column_evals,
            gamma,
            &beta,
            &eq,
            alpha,
            balance_weight,
            &point.0,
        )
        .unwrap();
        let prover_final_challenges = prover.sample_vec(8);
        let proof = prover.into_proof();
        let verify = |proof: Proof<F>| -> bool {
            let Ok(mut verifier) = VerifierState::<EF, _>::new_with_hash_profile(
                proof,
                permutation.clone(),
                capacity,
                ProofHashProfile::Keccak240,
            ) else {
                return false;
            };
            verifier.observe_scalars(&binding);
            assert_eq!(verifier.sample(), gamma);
            verifier.duplex();
            assert_eq!(eval_eq(&verifier.sample_vec(LOG_MAX_BUS_WIDTH)).as_slice(), beta);
            verifier.observe_scalars(&helper_poly);
            verifier.duplex();
            assert_eq!(verifier.sample_vec(h), eq);
            assert_eq!(verifier.sample(), alpha);
            assert_eq!(verifier.sample(), balance_weight);
            let Ok(evaluation) = sumcheck_verify(&mut verifier, h, 11, EF::ZERO, None) else {
                return false;
            };
            if verifier.check_fully_consumed().is_err() {
                return false;
            }
            let mut claimed_columns = Vec::new();
            for section in &witness.sections {
                let air = GroupedAir {
                    layout: section.layout.clone(),
                    kind: GroupedAirKind::Constraints,
                };
                let natural = MultilinearPoint(natural_ordering_point_for_session(
                    &evaluation.point.0,
                    section.layout.log_n_rows,
                ));
                claimed_columns.push(
                    air.columns(&inputs, section)
                        .iter()
                        .map(|column| column.as_slice().evaluate(&natural))
                        .collect(),
                );
            }
            let final_value = grouped_final_evaluation(
                &witness.layout,
                &claimed_columns,
                gamma,
                &beta,
                &eq,
                alpha,
                balance_weight,
                &evaluation.point.0,
            )
            .unwrap();
            if final_value != evaluation.value {
                return false;
            }
            assert_eq!(evaluation.point, point);
            assert_eq!(evaluation.value, expected);
            assert_eq!(verifier.sample_vec(8), prover_final_challenges);
            true
        };
        assert!(verify(proof.clone()));
        let encoded = serde_json::to_value(&proof).unwrap();
        let n_scalars = encoded["transcript"].as_array().unwrap().len();
        for i in 0..n_scalars {
            let mut changed = encoded.clone();
            let value = changed["transcript"][i].as_u64().unwrap();
            changed["transcript"][i] = serde_json::json!((value + 1) % F::ORDER_U64);
            assert!(
                !verify(serde_json::from_value(changed).unwrap()),
                "accepted transcript mutation at {i}"
            );
        }
        let mut truncated = encoded.clone();
        truncated["transcript"].as_array_mut().unwrap().pop();
        assert!(!verify(serde_json::from_value(truncated).unwrap()));
        let mut extra = encoded;
        extra["transcript"].as_array_mut().unwrap().push(serde_json::json!(0));
        assert!(!verify(serde_json::from_value(extra).unwrap()));
        for section in 0..column_evals.len() {
            let air = GroupedAir {
                layout: witness.sections[section].layout.clone(),
                kind: GroupedAirKind::Constraints,
            };
            let mut changed = column_evals.clone();
            changed[section][air.source_columns()] += EF::ONE;
            assert_ne!(
                grouped_final_evaluation(
                    &witness.layout,
                    &changed,
                    gamma,
                    &beta,
                    &eq,
                    alpha,
                    balance_weight,
                    &point.0
                )
                .unwrap(),
                expected
            );
        }
        println!(
            "grouped native sumcheck: {h} rounds, degree 11, {n_scalars} transcript base fields; all scalar mutations rejected"
        );
    });
}

#[test]
fn grouped_native_sumcheck_authenticates_helper_claims_with_keccak_whir() {
    with_real_trace(|inputs| {
        // Source and fixed-program data are supplied to this test verifier in
        // full. Only the grouped helper claims use a succinct PCS here.
        let mut binding = b"leanvm-grouped-helper-pcs-test-v1"
            .iter()
            .map(|&b| F::from_u8(b))
            .collect::<Vec<_>>();
        for column in [inputs.memory, inputs.memory_acc, inputs.bytecode, inputs.bytecode_acc] {
            binding.push(F::from_usize(column.len()));
            binding.extend(column);
        }
        for (&table, trace) in inputs.traces {
            binding.extend([F::from_usize(table.index()), F::from_usize(trace.log_n_rows)]);
            for column in &trace.columns[..table.n_columns()] {
                binding.extend(column.iter().copied());
            }
        }
        let layout = inputs.layout();
        let helper_n_vars = log2_ceil_usize(layout.helper_base_fields);
        let config = WhirConfig::<EF>::new(
            &WhirConfigBuilder {
                security_level: 100,
                max_num_variables_to_send_coeffs: 3,
                pow_bits: 12,
                folding_factor: FoldingFactor::new(4, 3),
                soundness_type: SecurityAssumption::JohnsonBound,
                starting_log_inv_rate: 4,
                rs_domain_initial_reduction_factor: 3,
            },
            helper_n_vars,
        );
        let permutation = get_poseidon16().clone();
        let capacity = [F::ZERO; 8];
        let mut prover =
            ProverState::<EF, _>::new_with_hash_profile(permutation.clone(), capacity, ProofHashProfile::Keccak240);
        prover.observe_scalars(&binding);
        let gamma = prover.sample();
        prover.duplex();
        let beta = eval_eq(&prover.sample_vec(LOG_MAX_BUS_WIDTH)).to_vec();
        let witness = GroupedWitness::build(&inputs, gamma, &beta).unwrap();
        let helper_poly = MleOwned::<EF>::Base(ArenaVec::from_iter(witness.base_field_polynomial()));
        let helper_commitment = config.commit(&mut prover, &helper_poly, layout.helper_base_fields);
        prover.duplex();
        let h = layout.sections.iter().map(|s| s.log_n_rows).max().unwrap();
        let eq = prover.sample_vec(h);
        let alpha = prover.sample();
        let balance_weight = prover.sample();
        let mut sessions = grouped_sessions(&inputs, &witness, gamma, &beta, &eq, alpha, balance_weight);
        let point = prove_batched_air_sumcheck(&mut prover, &mut sessions);
        let mut column_evals = Vec::new();
        for pair in sessions.chunks(2) {
            let evals = pair[0].final_column_evals();
            assert_eq!(evals, pair[1].final_column_evals());
            prover.add_extension_scalars(&evals);
            column_evals.push(evals);
        }
        let statements = grouped_helper_statements(&layout, &column_evals, &point.0, helper_n_vars).unwrap();
        assert_eq!(statements.iter().map(|s| s.values.len()).sum::<usize>(), 50);
        config.prove(&mut prover, statements, helper_commitment, &helper_poly.by_ref());
        let final_challenges = prover.sample_vec(8);
        let proof = prover.into_proof();
        let verify = |proof: Proof<F>, change_selector: bool, change_claim: bool, change_binding: bool| -> bool {
            let Ok(mut verifier) = VerifierState::<EF, _>::new_with_hash_profile(
                proof,
                permutation.clone(),
                capacity,
                ProofHashProfile::Keccak240,
            ) else {
                return false;
            };
            let mut candidate_binding = binding.clone();
            if change_binding {
                candidate_binding[0] += F::ONE;
            }
            verifier.observe_scalars(&candidate_binding);
            let gamma = verifier.sample();
            verifier.duplex();
            let beta = eval_eq(&verifier.sample_vec(LOG_MAX_BUS_WIDTH)).to_vec();
            let Ok(commitment) = config.parse_commitment::<F>(&mut verifier) else {
                return false;
            };
            verifier.duplex();
            let eq = verifier.sample_vec(h);
            let alpha = verifier.sample();
            let balance_weight = verifier.sample();
            let Ok(evaluation) = sumcheck_verify(&mut verifier, h, 11, EF::ZERO, None) else {
                return false;
            };
            let mut claims = Vec::new();
            for section in &witness.sections {
                let air = GroupedAir {
                    layout: section.layout.clone(),
                    kind: GroupedAirKind::Constraints,
                };
                let Ok(evals) = verifier.next_extension_scalars_vec(air.n_columns() + air.n_shift_columns()) else {
                    return false;
                };
                let natural = MultilinearPoint(natural_ordering_point_for_session(
                    &evaluation.point.0,
                    section.layout.log_n_rows,
                ));
                let columns = air.columns(&inputs, section);
                // Authenticate only source/shift columns directly; helper
                // claims below must be authenticated by WHIR.
                for index in (0..air.source_columns()).chain(air.n_columns()..columns.len()) {
                    if evals[index] != columns[index].as_slice().evaluate(&natural) {
                        return false;
                    }
                }
                claims.push(evals);
            }
            let Ok(final_value) = grouped_final_evaluation(
                &layout,
                &claims,
                gamma,
                &beta,
                &eq,
                alpha,
                balance_weight,
                &evaluation.point.0,
            ) else {
                return false;
            };
            if final_value != evaluation.value {
                return false;
            }
            let mut statements =
                grouped_helper_statements(&layout, &claims, &evaluation.point.0, helper_n_vars).unwrap();
            if change_selector {
                statements[0].values[0].selector += 1;
            }
            if change_claim {
                statements[0].values[0].value += EF::ONE;
            }
            if config.verify(&mut verifier, &commitment, statements).is_err() {
                return false;
            }
            if verifier.check_fully_consumed().is_err() {
                return false;
            }
            assert_eq!(verifier.sample_vec(8), final_challenges);
            true
        };
        assert!(verify(proof.clone(), false, false, false));
        assert!(!verify(proof.clone(), true, false, false));
        assert!(!verify(proof.clone(), false, true, false));
        assert!(!verify(proof.clone(), false, false, true));
        let mut encoded = serde_json::to_value(&proof).unwrap();
        let first = encoded["transcript"][0].as_u64().unwrap();
        encoded["transcript"][0] = serde_json::json!(first ^ 1);
        assert!(!verify(serde_json::from_value(encoded).unwrap(), false, false, false));
        println!(
            "grouped helper PCS: 2^{helper_n_vars}, 50 helper claims, {} proof base fields; honest proof accepted and 4 negative cases rejected",
            proof.proof_size_fe()
        );
    });
}

#[test]
fn grouped_execution_authenticates_compact_claims_through_three_keccak_commitments() {
    with_real_trace(|inputs| {
        let bytecode = compile_program(&ProgramSource::Raw(PROGRAM.to_string()));
        let layout = inputs.layout();
        let primary = stack_polynomials(inputs.memory, inputs.memory_acc, inputs.bytecode_acc, inputs.traces);
        let n_vars = primary.stacked_n_vars;
        let fixed_offset = inputs.bytecode.len();
        assert!(2 * fixed_offset <= 1 << n_vars);
        let mut fixed_values = vec![F::ZERO; 1 << n_vars];
        for (i, value) in fixed_values[..fixed_offset].iter_mut().enumerate() {
            *value = F::from_usize(i + 17);
        }
        fixed_values[fixed_offset..2 * fixed_offset].copy_from_slice(inputs.bytecode);
        let fixed = MleOwned::<EF>::Base(ArenaVec::from_iter(fixed_values));
        let config = WhirConfig::<EF>::new(
            &WhirConfigBuilder {
                security_level: 100,
                max_num_variables_to_send_coeffs: 3,
                pow_bits: 12,
                folding_factor: FoldingFactor::new(4, 3),
                soundness_type: SecurityAssumption::JohnsonBound,
                starting_log_inv_rate: 4,
                rs_domain_initial_reduction_factor: 3,
            },
            n_vars,
        );
        let pcs = GroupedPcsLayout {
            primary_n_vars: n_vars,
            fixed_n_vars: n_vars,
            helper_n_vars: n_vars,
            memory_log: log2_strict_usize(inputs.memory.len()),
            bytecode_log: bytecode.log_size(),
            fixed_bytecode_offset: fixed_offset,
            ending_pc: bytecode.ending_pc(),
        };
        let (fixed_data, trusted_fixed_root) =
            config.build_commitment_data_with_hash_profile(&fixed, 2 * fixed_offset, ProofHashProfile::Keccak240);
        let mut binding = b"leanvm-grouped-execution-three-commitments-test-v1"
            .iter()
            .map(|&b| F::from_u8(b))
            .collect::<Vec<_>>();
        binding.extend(
            [
                n_vars,
                pcs.memory_log,
                pcs.bytecode_log,
                fixed_offset,
                pcs.ending_pc,
                100,
                12,
                4,
                3,
                4,
                3,
                3,
                6,
            ]
            .map(F::from_usize),
        );
        for section in &layout.sections {
            binding.extend([section.log_n_rows, section.helper_offset, section.group_widths.len()].map(F::from_usize));
            binding.extend(section.group_widths.iter().copied().map(F::from_usize));
        }
        let public = vec![F::ZERO; PUBLIC_INPUT_LEN];
        let h = layout.sections.iter().map(|s| s.log_n_rows).max().unwrap();
        let permutation = get_poseidon16().clone();
        let capacity = [F::ZERO; 8];
        let mut prover =
            ProverState::<EF, _>::new_with_hash_profile(permutation.clone(), capacity, ProofHashProfile::Keccak240);
        prover.observe_scalars(&binding);
        prover.observe_scalars(&public);
        let primary_witness =
            config.commit_without_ood(&mut prover, &primary.global_polynomial, primary.actual_data_len);
        prover.add_base_scalars(&trusted_fixed_root);
        let fixed_witness = Witness {
            prover_data: fixed_data,
            ood_points: Vec::new(),
            ood_answers: Vec::new(),
        };
        let gamma = prover.sample();
        prover.duplex();
        let lookup_beta = prover.sample_vec(LOG_MAX_BUS_WIDTH);
        let beta = eval_eq(&lookup_beta).to_vec();
        let witness = GroupedWitness::build(&inputs, gamma, &beta).unwrap();
        let mut helper_values = witness.base_field_polynomial();
        helper_values.resize(1 << n_vars, F::ZERO);
        let helper = MleOwned::<EF>::Base(ArenaVec::from_iter(helper_values));
        let helper_witness = config.commit_without_ood(&mut prover, &helper, layout.helper_base_fields);
        prover.duplex();
        let eq = prover.sample_vec(h);
        let alpha = prover.sample();
        let balance_weight = prover.sample();
        let mut sessions = grouped_sessions(&inputs, &witness, gamma, &beta, &eq, alpha, balance_weight);
        let point = prove_batched_air_sumcheck(&mut prover, &mut sessions);
        let column_evals = sessions
            .chunks(2)
            .map(|pair| {
                let evals = pair[0].final_column_evals();
                assert_eq!(evals, pair[1].final_column_evals());
                evals
            })
            .collect::<Vec<_>>();
        let claims = GroupedFinalClaims::from_column_evals(&layout, &column_evals, &beta).unwrap();
        assert_eq!(claims.sections.iter().map(Vec::len).sum::<usize>(), 256);
        assert_eq!(
            claims
                .evaluate(&layout, gamma, &beta, &eq, alpha, balance_weight, &point.0)
                .unwrap(),
            grouped_final_evaluation(
                &layout,
                &column_evals,
                gamma,
                &beta,
                &eq,
                alpha,
                balance_weight,
                &point.0
            )
            .unwrap()
        );
        claims.observe_prover(&mut prover);
        let public_point = MultilinearPoint(prover.sample_vec(log2_strict_usize(public.len())));
        let public_claim = SparseStatement::new(
            n_vars,
            public_point.clone(),
            vec![SparseValue::new(0, public.as_slice().evaluate(&public_point))],
        );
        let carried = vec![SparseStatement::unique_value(n_vars, 7, EF::from_u32(24))];
        let groups = grouped_pcs_statements(
            &layout,
            &claims,
            &point.0,
            &lookup_beta,
            &pcs,
            vec![public_claim],
            carried.clone(),
        )
        .unwrap();
        assert_eq!(
            groups
                .each_ref()
                .map(|g| g.iter().map(|s| s.values.len()).sum::<usize>()),
            [201, 9, 50]
        );
        let refs = [primary.global_polynomial.by_ref(), fixed.by_ref(), helper.by_ref()];
        config.prove_three_commitments(
            &mut prover,
            6,
            groups,
            [primary_witness, fixed_witness, helper_witness],
            refs.each_ref(),
        );
        let final_challenges = prover.sample_vec(8);
        let proof = prover.into_proof();
        // This verifier receives no source columns, helper polynomial, trace,
        // memory accumulator, or instruction table. The fixed root is trusted.
        let verify = |candidate: &Proof<F>, candidate_public: &[F], fixed_root: &[F; 8], altered_carry: bool| -> bool {
            let Ok(mut verifier) = VerifierState::<EF, _>::new_with_hash_profile(
                candidate.clone(),
                permutation.clone(),
                capacity,
                ProofHashProfile::Keccak240,
            ) else {
                return false;
            };
            verifier.observe_scalars(&binding);
            verifier.observe_scalars(candidate_public);
            let Ok(primary_commitment) = config.parse_commitment_without_ood::<F>(&mut verifier) else {
                return false;
            };
            let Ok(fixed_commitment) = config.parse_commitment_without_ood::<F>(&mut verifier) else {
                return false;
            };
            if &fixed_commitment.root != fixed_root {
                return false;
            }
            let gamma = verifier.sample();
            verifier.duplex();
            let lookup_beta = verifier.sample_vec(LOG_MAX_BUS_WIDTH);
            let beta = eval_eq(&lookup_beta).to_vec();
            let Ok(helper_commitment) = config.parse_commitment_without_ood::<F>(&mut verifier) else {
                return false;
            };
            verifier.duplex();
            let eq = verifier.sample_vec(h);
            let alpha = verifier.sample();
            let balance_weight = verifier.sample();
            let Ok(evaluation) = sumcheck_verify(&mut verifier, h, 11, EF::ZERO, None) else {
                return false;
            };
            let Ok(claims) = GroupedFinalClaims::read_verifier(&layout, &mut verifier) else {
                return false;
            };
            let Ok(value) = claims.evaluate(&layout, gamma, &beta, &eq, alpha, balance_weight, &evaluation.point.0)
            else {
                return false;
            };
            if value != evaluation.value {
                return false;
            }
            let public_point = MultilinearPoint(verifier.sample_vec(log2_strict_usize(candidate_public.len())));
            let public_claim = SparseStatement::new(
                n_vars,
                public_point.clone(),
                vec![SparseValue::new(0, candidate_public.evaluate(&public_point))],
            );
            let mut carried = carried.clone();
            if altered_carry {
                carried[0].values[0].value += EF::ONE;
            }
            let Ok(groups) = grouped_pcs_statements(
                &layout,
                &claims,
                &evaluation.point.0,
                &lookup_beta,
                &pcs,
                vec![public_claim],
                carried,
            ) else {
                return false;
            };
            if config
                .verify_three_commitments::<F>(
                    &mut verifier,
                    6,
                    [&primary_commitment, &fixed_commitment, &helper_commitment],
                    groups,
                )
                .is_err()
            {
                return false;
            }
            if verifier.check_fully_consumed().is_err() {
                return false;
            }
            assert_eq!(verifier.sample_vec(8), final_challenges);
            true
        };
        assert!(verify(&proof, &public, &trusted_fixed_root, false));
        let mut changed_public = public.clone();
        changed_public[1] = F::ONE;
        assert!(!verify(&proof, &changed_public, &trusted_fixed_root, false));
        let mut changed_root = trusted_fixed_root;
        changed_root[0] += F::ONE;
        assert!(!verify(&proof, &public, &changed_root, false));
        assert!(!verify(&proof, &public, &trusted_fixed_root, true));
        let encoded = serde_json::to_value(&proof).unwrap();
        let claim_start = 24 + h * 11 * DIMENSION;
        let mut offset = claim_start;
        let mut negative_claims = 0;
        for (section, values) in layout.sections.iter().zip(&claims.sections) {
            for index in 0..values.len() {
                let mut changed = encoded.clone();
                let scalar = changed["transcript"][offset + index * DIMENSION].as_u64().unwrap();
                changed["transcript"][offset + index * DIMENSION] = serde_json::json!((scalar + 1) % F::ORDER_U64);
                assert!(
                    !verify(
                        &serde_json::from_value(changed).unwrap(),
                        &public,
                        &trusted_fixed_root,
                        false
                    ),
                    "accepted changed claim {:?}/{index}",
                    section.source
                );
                negative_claims += 1;
            }
            offset += values.len() * DIMENSION;
        }
        println!(
            "grouped execution with three Keccak commitments: 2^{n_vars}, 256 transmitted claims, {} proof base fields; {negative_claims} claim mutations and 3 public-context changes rejected",
            proof.proof_size_fe()
        );
    });
}

#[test]
fn grouped_compact_bytecode_claims_handle_zero_and_one_lookup_challenges() {
    with_real_trace(|inputs| {
        let gamma = <EF as BasedVectorSpace<F>>::ith_basis_element(1).unwrap();
        let layout = inputs.layout();
        let h = layout.sections.iter().map(|s| s.log_n_rows).max().unwrap();
        let mut rng = StdRng::seed_from_u64(918);
        let point = (0..h).map(|_| rng.random::<EF>()).collect::<Vec<_>>();
        let eq = (0..h).map(|_| rng.random::<EF>()).collect::<Vec<_>>();
        let alpha = rng.random::<EF>();
        let balance_weight = rng.random::<EF>();
        for beta_point in [vec![EF::ZERO; LOG_MAX_BUS_WIDTH], vec![EF::ONE; LOG_MAX_BUS_WIDTH]] {
            let beta = eval_eq(&beta_point).to_vec();
            let helpers = GroupedWitness::build(&inputs, gamma, &beta).unwrap();
            let columns = helpers
                .sections
                .iter()
                .map(|section| {
                    let air = GroupedAir {
                        layout: section.layout.clone(),
                        kind: GroupedAirKind::Constraints,
                    };
                    let natural =
                        MultilinearPoint(natural_ordering_point_for_session(&point, section.layout.log_n_rows));
                    air.columns(&inputs, section)
                        .iter()
                        .map(|column| column.as_slice().evaluate(&natural))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let claims = GroupedFinalClaims::from_column_evals(&layout, &columns, &beta).unwrap();
            assert_eq!(
                claims
                    .evaluate(&layout, gamma, &beta, &eq, alpha, balance_weight, &point)
                    .unwrap(),
                grouped_final_evaluation(&layout, &columns, gamma, &beta, &eq, alpha, balance_weight, &point).unwrap()
            );
            let mut truncated = claims.clone();
            truncated.sections[0].pop();
            assert!(
                truncated
                    .evaluate(&layout, gamma, &beta, &eq, alpha, balance_weight, &point)
                    .is_err()
            );
        }
    });
}
