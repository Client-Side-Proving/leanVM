use backend::{PrimeCharacteristicRing, PrimeField32, poseidon16_permute};
use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_vm::{ExecutionWitness, F, try_execute_bytecode};
use std::{collections::BTreeMap, fmt::Write, path::PathBuf};

struct Sources(PathBuf);
impl Sources {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "spartan-guest-tests-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&path).unwrap();
        for entry in std::fs::read_dir(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("zkdsl_implem")).unwrap() {
            let entry = entry.unwrap();
            if entry.path().extension().is_some_and(|ext| ext == "py") {
                std::fs::copy(entry.path(), path.join(entry.file_name())).unwrap();
            }
        }
        Self(path)
    }
    fn run(&self, source: &str, bits: bool, paired: bool, product: bool, radix: bool) -> Result<String, String> {
        self.run_with_extension(source, bits, paired, product, radix, false)
    }
    fn run_with_extension(
        &self,
        source: &str,
        bits: bool,
        paired: bool,
        product: bool,
        radix: bool,
        extension: bool,
    ) -> Result<String, String> {
        self.run_with_transcript_options(source, bits, paired, product, radix, extension, false)
    }
    #[allow(clippy::too_many_arguments)]
    fn run_with_transcript_options(
        &self,
        source: &str,
        bits: bool,
        paired: bool,
        product: bool,
        radix: bool,
        extension: bool,
        transcript: bool,
    ) -> Result<String, String> {
        let path = self.0.join("optimization_test.py");
        std::fs::write(&path, source).unwrap();
        let mut replacements = BTreeMap::from([
            ("OPT_MERKLE_BITS_VALUE".into(), usize::from(bits).to_string()),
            ("OPT_MERKLE_PAIRED_VALUE".into(), usize::from(paired).to_string()),
            ("OPT_QUERY_PRODUCT_VALUE".into(), usize::from(product).to_string()),
            ("OPT_RADIX_PREFIX_VALUE".into(), usize::from(radix).to_string()),
            ("OPT_QUERY_PERMUTATION_VALUE".into(), "0".into()),
        ]);
        for matrix in ["A", "B", "C"] {
            for field in ["ROWS", "COLUMNS", "VALUES"] {
                replacements.insert(format!("FULL_ZK_MATRIX_{matrix}_{field}_PLACEHOLDER"), "[]".into());
            }
        }
        replacements.insert(
            "OPT_EXTENSION_ARITHMETIC_VALUE".into(),
            usize::from(extension).to_string(),
        );
        replacements.insert(
            "OPT_TRANSCRIPT_BLOCKS_VALUE".into(),
            usize::from(transcript).to_string(),
        );
        let bytecode = compile_program_with_flags(
            &ProgramSource::Filepath(path.to_string_lossy().into()),
            CompilationFlags { replacements },
        );
        try_execute_bytecode(&bytecode, &[F::ZERO; 8], &ExecutionWitness::default(), false)
            .map(|result| result.metadata.stdout)
            .map_err(|error| error.to_string())
    }
}
impl Drop for Sources {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn array(source: &mut String, name: &str, values: &[u32]) {
    writeln!(source, "    {name} = Array({})", values.len()).unwrap();
    for (index, value) in values.iter().enumerate() {
        writeln!(source, "    {name}[{index}] = {value}").unwrap();
    }
}
fn tree(height: usize, salt: usize) -> Vec<Vec<[F; 8]>> {
    let leaves = (0..1 << height)
        .map(|i| std::array::from_fn(|j| F::from_usize(salt + i * 31 + j)))
        .collect();
    let mut levels: Vec<Vec<[F; 8]>> = vec![leaves];
    for level in 0..height {
        levels.push(
            levels[level]
                .chunks_exact(2)
                .map(|pair| {
                    let input = std::array::from_fn(|i| pair[i / 8][i % 8]);
                    // Spartan's Merkle compression truncates the raw permutation.
                    poseidon16_permute(input)[..8].try_into().unwrap()
                })
                .collect(),
        );
    }
    levels
}
fn siblings(levels: &[Vec<[F; 8]>], queries: &[usize]) -> Vec<[F; 8]> {
    let mut indices = queries.to_vec();
    let mut siblings = Vec::new();
    for nodes in levels.iter().take(levels.len() - 1) {
        let mut parents = Vec::new();
        let mut cursor = 0;
        while cursor < indices.len() {
            let index = indices[cursor];
            if index.is_multiple_of(2) && indices.get(cursor + 1) == Some(&(index + 1)) {
                cursor += 2;
            } else {
                siblings.push(nodes[index ^ 1]);
                cursor += 1;
            }
            parents.push(index / 2);
        }
        indices = parents;
    }
    siblings
}
fn words(digests: &[[F; 8]]) -> Vec<u32> {
    digests.iter().flatten().map(|value| value.as_canonical_u32()).collect()
}

#[test]
fn fixed_sibling_capacity_compiles_at_binary_tree_boundaries() {
    let sources = Sources::new();
    let mut source = String::from("from full_zk_production_common import *\n\ndef main():\n");
    for (queries, height, expected) in [
        (1, 0, 0),
        (1, 1, 1),
        (2, 1, 1),
        (1, 3, 3),
        (2, 3, 4),
        (3, 3, 4),
        (8, 3, 4),
        (88, 10, 304),
    ] {
        writeln!(
            source,
            "    capacity_{queries}_{height} = fixed_merkle_sibling_capacity({queries}, {height})"
        )
        .unwrap();
        writeln!(source, "    assert capacity_{queries}_{height} == {expected}").unwrap();
    }
    source.push_str("    return\n");
    sources.run(&source, false, false, false, false).unwrap();
}

#[test]
fn cached_merkle_bits_and_shared_traversal_match_binary_trees() {
    let sources = Sources::new();
    for (height, queries) in [
        (0, vec![0]),
        (1, vec![1]),
        (1, vec![0, 1]),
        (4, vec![0]),
        (4, vec![15]),
        (4, vec![2, 3, 8, 10, 15]),
        (4, (0..16).collect()),
    ] {
        let a = tree(height, 1);
        let b = tree(height, 400);
        let sa = siblings(&a, &queries);
        let sb = siblings(&b, &queries);
        let mut source = String::from("from full_zk_production_common import *\n\ndef main():\n");
        let mut indices: Vec<u32> = queries.iter().map(|index| *index as u32).collect();
        for &index in &queries {
            indices.extend((0..height).map(|bit| ((index >> bit) & 1) as u32));
        }
        array(&mut source, "indices", &indices);
        array(&mut source, "root_a", &words(a.last().unwrap()));
        array(&mut source, "root_b", &words(b.last().unwrap()));
        array(
            &mut source,
            "rows_a",
            &words(&queries.iter().map(|&i| a[0][i]).collect::<Vec<_>>()),
        );
        array(
            &mut source,
            "rows_b",
            &words(&queries.iter().map(|&i| b[0][i]).collect::<Vec<_>>()),
        );
        array(&mut source, "siblings_a", &words(&sa));
        array(&mut source, "siblings_b", &words(&sb));
        writeln!(source, "    if OPT_MERKLE_PAIRED == 1:\n        verify_pruned_merkle_pair(root_a, root_b, indices, rows_a, rows_b, {}, {height}, siblings_a, {}, siblings_b, {})\n    else:\n        verify_pruned_merkle_runtime(root_a, indices, rows_a, {}, {height}, siblings_a, {})\n        verify_pruned_merkle_runtime(root_b, indices, rows_b, {}, {height}, siblings_b, {})\n    return", queries.len(), sa.len(), sb.len(), queries.len(), sa.len(), queries.len(), sb.len()).unwrap();
        for bits in [false, true] {
            for paired in [false, true] {
                assert!(
                    sources.run(&source, bits, paired, false, false).is_ok(),
                    "height={height}, queries={queries:?}"
                );
                // The second oracle must remain authenticated under shared traversal.
                let value = b.last().unwrap()[0][0].as_canonical_u32();
                let changed = source.replace(
                    &format!("root_b[0] = {value}\n"),
                    &format!("root_b[0] = {}\n", value + 1),
                );
                assert!(sources.run(&changed, bits, paired, false, false).is_err());
            }
        }
    }
}

#[test]
fn query_sampling_optimizations_preserve_positions_and_transcript() {
    let sources = Sources::new();
    let source = r#"from full_zk_production_common import *

def main():
    for seed in unroll(0, 8):
        fs = fs_new()
        observed = fs_observe_one(fs, seed)
        after, positions = sample_sorted_queries_bounded(observed, 5, 4, 32)
        for i in unroll(0, 5):
            print(positions[i])
        digest = fs_finalize(after)
        for i in unroll(0, 8):
            print(digest[i])
    return
"#;
    let expected = sources.run(source, false, false, false, false).unwrap();
    for bits in [false, true] {
        for product in [false, true] {
            for radix in [false, true] {
                assert_eq!(sources.run(source, bits, false, product, radix).unwrap(), expected);
            }
        }
    }
}

#[test]
fn unrolled_base_powers_match_recurrence_and_bounded_fallback() {
    let sources = Sources::new();
    let implementation = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("zkdsl_implem/hiding_whir_spark_poseidon1.py"),
    )
    .unwrap();
    let start = implementation.find("def base_power_table(").unwrap();
    let end = implementation[start..]
        .find("\n\ndef polynomial_dot_base_powers")
        .unwrap()
        + start;
    let function = &implementation[start..end];
    for length in [1, 3, 96, 368, 1024, 1025] {
        for point in [F::ZERO, F::ONE, -F::ONE, F::from_u32(371)] {
            for unroll in [false, true] {
                let mut source = format!(
                    "from full_zk_production_common import *\n\nOPT_UNROLL_POWERS = {}\n\n{function}\n\ndef main():\n    powers = base_power_table({}, {length})\n",
                    usize::from(unroll),
                    point.as_canonical_u32(),
                );
                let mut power = F::ONE;
                for index in 0..length {
                    writeln!(source, "    assert powers[{index}] == {}", power.as_canonical_u32()).unwrap();
                    power *= point;
                }
                source.push_str("    return\n");
                assert!(
                    sources.run(&source, false, false, false, false).is_ok(),
                    "length={length}, point={}, unroll={unroll}",
                    point.as_canonical_u32()
                );
            }
        }
    }
}

#[test]
fn blocked_query_power_updates_cover_blocks_tails_and_preserve_ood_slot() {
    let sources = Sources::new();
    let implementation = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("zkdsl_implem/hiding_whir_spark_poseidon1.py"),
    )
    .unwrap();
    let function = |name: &str| {
        let start = implementation.find(&format!("def {name}(")).unwrap();
        let end = implementation[start..].find("\n\ndef ").unwrap() + start;
        &implementation[start..end]
    };
    for count in [0, 1, 7, 8, 9, 15, 16, 17, 124, 268] {
        let mut source = format!(
            "from full_zk_production_common import *\n\n{}\n\n{}\n\ndef main():\n",
            function("hiding_copy_extension"),
            function("update_query_powers_blocked"),
        );
        let previous: Vec<_> = (0..(count + 1) * 5).map(|i| (i * 19 + 31) as u32).collect();
        let points: Vec<_> = (0..count * 5)
            .map(|i| {
                if i % 5 != 0 {
                    0
                } else {
                    [0, 1, 2130706432, 371][(i / 5) % 4]
                }
            })
            .collect();
        array(&mut source, "previous", &previous);
        array(&mut source, "points", &points);
        writeln!(source, "    current = Array({})", (count + 1) * 5).unwrap();
        for i in 0..5 {
            writeln!(source, "    current[{i}] = {}", 700 + i).unwrap();
        }
        writeln!(
            source,
            "    update_query_powers_blocked(previous, current, points, {count})"
        )
        .unwrap();
        for i in 0..5 {
            writeln!(source, "    assert current[{i}] == {}", 700 + i).unwrap();
        }
        for query in 0..count {
            for coefficient in 0..5 {
                let expected = F::from_u32(previous[(query + 1) * 5 + coefficient]) * F::from_u32(points[query * 5]);
                writeln!(
                    source,
                    "    assert current[{}] == {}",
                    (query + 1) * 5 + coefficient,
                    expected.as_canonical_u32()
                )
                .unwrap();
            }
        }
        source.push_str("    return\n");
        assert!(
            sources.run(&source, false, false, false, false).is_ok(),
            "count={count}"
        );
    }
}

#[test]
fn plain_whir_continuation_reserves_constant_coefficient_for_carried_claim() {
    let sources = Sources::new();
    let implementation =
        std::fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("zkdsl_implem/plain_whir_poseidon1.py"))
            .unwrap();
    let function = |name: &str| {
        let start = implementation.find(&format!("def {name}(")).unwrap();
        let end = implementation[start..].find("\n\ndef ").unwrap() + start;
        &implementation[start..end]
    };
    let prelude = format!(
        "from full_zk_production_common import *\n\n{}\n\n{}\n\n{}\n\n{}\n\n{}\n\ndef main():\n",
        function("copy_extension"),
        function("eq_expanded_univariate"),
        function("select_weight"),
        function("plain_combine_continuation"),
        function("accumulate_plain_round_weight"),
    );
    // A false carried residual and its negation must retain gamma dependence.
    // With a zero-variable polynomial every fresh weight equals one, so the
    // final weight can also be checked independently of point interpolation.
    for gamma in [0u32, 1, 2, 13] {
        let mut source = prelude.clone();
        source.push_str("    positions = Array(2)\n    positions[0] = 0\n    positions[1] = 0\n");
        writeln!(source, "    gamma = ef_from_base({gamma})").unwrap();
        source.push_str("    residual = plain_combine_continuation(ef_from_base(7), gamma, ef_from_base(2130706426), ef_zero(), 1, 0)\n");
        writeln!(
            source,
            "    ef_assert_equal(residual, ef_from_base({}))",
            (F::from_u32(7) * (F::ONE - F::from_u32(gamma))).as_canonical_u32()
        )
        .unwrap();
        source.push_str("    fresh = Array(10)\n    copy_extension(ef_from_base(11), fresh)\n    copy_extension(ef_from_base(17), fresh + DIM)\n    total = plain_combine_continuation(ef_from_base(5), gamma, ef_from_base(7), fresh, 1, 2)\n");
        let g = F::from_u32(gamma);
        let expected = F::from_u32(5) + g * F::from_u32(7) + g * g * F::from_u32(11) + g * g * g * F::from_u32(17);
        writeln!(
            source,
            "    ef_assert_equal(total, ef_from_base({}))",
            expected.as_canonical_u32()
        )
        .unwrap();
        source.push_str("    weight = accumulate_plain_round_weight(ef_from_base(5), ef_zero(), ef_zero(), gamma, positions, 2, 1, 1, 0, 1)\n");
        writeln!(
            source,
            "    ef_assert_equal(weight, ef_from_base({}))",
            (F::from_u32(5) + g + g * g + g * g * g).as_canonical_u32()
        )
        .unwrap();
        source.push_str("    return\n");
        for extension in [false, true] {
            assert!(
                sources
                    .run_with_extension(&source, false, false, false, false, extension)
                    .is_ok()
            );
        }
    }
}

#[test]
fn extension_instructions_match_coordinate_arithmetic() {
    let sources = Sources::new();
    let mut vectors = vec![[0; 5], [1; 5], [2_130_706_432; 5]];
    for coefficient in 0..5 {
        let mut basis = [0; 5];
        basis[coefficient] = 1;
        vectors.push(basis);
        basis[coefficient] = 2_130_706_432;
        vectors.push(basis);
    }
    let mut state = 17u64;
    for _ in 0..16 {
        vectors.push(std::array::from_fn(|_| {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            (state % 2_130_706_433) as u32
        }));
    }
    let mut source = String::from("from extension import *\n\ndef main():\n");
    for (index, left) in vectors.iter().enumerate() {
        let right = &vectors[(index + 7) % vectors.len()];
        array(&mut source, &format!("a{index}"), left);
        array(&mut source, &format!("b{index}"), right);
        writeln!(source, "    sum{index} = ef_add(a{index}, b{index})").unwrap();
        writeln!(source, "    difference{index} = ef_sub(a{index}, b{index})").unwrap();
        writeln!(source, "    complement{index} = ef_one_minus(a{index})").unwrap();
        for coefficient in 0..5 {
            let a = F::from_u32(left[coefficient]);
            let b = F::from_u32(right[coefficient]);
            writeln!(
                source,
                "    assert sum{index}[{coefficient}] == {}",
                (a + b).as_canonical_u32()
            )
            .unwrap();
            writeln!(
                source,
                "    assert difference{index}[{coefficient}] == {}",
                (a - b).as_canonical_u32()
            )
            .unwrap();
            writeln!(
                source,
                "    assert complement{index}[{coefficient}] == {}",
                (F::from_usize(usize::from(coefficient == 0)) - a).as_canonical_u32()
            )
            .unwrap();
        }
        for (scalar_index, scalar) in [0, 1, 2_130_706_432, 371].into_iter().enumerate() {
            writeln!(
                source,
                "    scaled{index}_{scalar_index} = ef_scale(a{index}, {scalar})"
            )
            .unwrap();
            writeln!(
                source,
                "    shifted{index}_{scalar_index} = ef_sub_base(a{index}, {scalar})"
            )
            .unwrap();
            for (coefficient, &left_coefficient) in left.iter().enumerate() {
                let a = F::from_u32(left_coefficient);
                writeln!(
                    source,
                    "    assert scaled{index}_{scalar_index}[{coefficient}] == {}",
                    (a * F::from_u32(scalar)).as_canonical_u32()
                )
                .unwrap();
                let shift = if coefficient == 0 { F::from_u32(scalar) } else { F::ZERO };
                writeln!(
                    source,
                    "    assert shifted{index}_{scalar_index}[{coefficient}] == {}",
                    (a - shift).as_canonical_u32()
                )
                .unwrap();
            }
        }
    }
    source.push_str("    return\n");
    for enabled in [false, true] {
        sources
            .run_with_extension(&source, false, false, false, false, enabled)
            .unwrap();
    }
}

#[test]
fn hiding_covectors_match_dense_prefix_folds_and_switch_padding() {
    use backend::{BasedVectorSpace, QuinticExtensionFieldKB as EF};
    let sources = Sources::new();
    let implementation = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("zkdsl_implem/hiding_whir_spark_poseidon1.py"),
    )
    .unwrap();
    let function = |name: &str| {
        let start = implementation.find(&format!("def {name}(")).unwrap();
        let end = implementation[start..].find("\n\ndef ").unwrap() + start;
        &implementation[start..end]
    };
    let extension = |seed: usize| EF::from_basis_coefficients_fn(|i| F::from_usize(3 + seed * 17 + i * 11));
    let flatten = |values: &[EF]| -> Vec<u32> {
        values
            .iter()
            .flat_map(|value| {
                value
                    .as_basis_coefficients_slice()
                    .iter()
                    .map(|f: &F| f.as_canonical_u32())
            })
            .collect()
    };
    for folds in [vec![2, 1], vec![1, 2, 1], vec![1, 1, 2, 1]] {
        let after: Vec<_> = (0..folds.len())
            .map(|batch| 2 + folds[batch + 1..].iter().sum::<usize>())
            .collect();
        let mut source = format!(
            "from extension import *\n\nRELATION_SUMCHECKS = {}\nRELATION_SUMCHECK_FOLDING = {folds:?}\nRELATION_AFTER_FOLD_VARIABLES = {after:?}\n\n{}\n\n{}\n\ndef main():\n    random_points = Array({})\n    epsilons = Array({})\n",
            folds.len(),
            function("fold_power_coefficient"),
            function("select_weight_extension"),
            folds.len(),
            folds.len(),
        );
        let randomness: Vec<Vec<EF>> = folds
            .iter()
            .enumerate()
            .map(|(i, count)| (0..*count).map(|j| extension(i * 5 + j)).collect())
            .collect();
        let epsilons: Vec<EF> = (0..folds.len()).map(|i| extension(50 + i)).collect();
        for batch in 0..folds.len() {
            array(&mut source, &format!("randomness{batch}"), &flatten(&randomness[batch]));
            array(&mut source, &format!("epsilon{batch}"), &flatten(&[epsilons[batch]]));
            writeln!(
                source,
                "    random_points[{batch}] = randomness{batch}\n    epsilons[{batch}] = epsilon{batch}"
            )
            .unwrap();
        }
        let var = extension(91);
        let coefficient = extension(93);
        array(&mut source, "point", &flatten(&[var]));
        array(&mut source, "coefficient", &flatten(&[coefficient]));
        for (round, &remaining_variables) in after.iter().take(folds.len() - 1).enumerate() {
            let mut power = coefficient;
            let mut dense: Vec<EF> = (0..1 << remaining_variables)
                .map(|_| {
                    let value = power;
                    power *= var;
                    value
                })
                .collect();
            for batch in round + 1..folds.len() {
                let suffix_length = dense.len() >> folds[batch];
                let mut folded = vec![EF::ZERO; suffix_length];
                for prefix in 0..1usize << folds[batch] {
                    let mut weight = EF::ONE;
                    for (coordinate, &challenge) in randomness[batch].iter().enumerate() {
                        weight *= if (prefix >> (folds[batch] - 1 - coordinate)) & 1 == 0 {
                            EF::ONE - challenge
                        } else {
                            challenge
                        };
                    }
                    for suffix in 0..suffix_length {
                        folded[suffix] += weight * dense[prefix * suffix_length + suffix] * epsilons[batch];
                    }
                }
                dense = folded;
            }
            writeln!(
                source,
                "    result{round} = fold_power_coefficient(point, coefficient, random_points, epsilons, {round})"
            )
            .unwrap();
            for (coordinate, value) in flatten(&[dense[0]]).into_iter().enumerate() {
                writeln!(source, "    assert result{round}[{coordinate}] == {value}").unwrap();
            }
        }
        source.push_str("    return\n");
        sources
            .run_with_extension(&source, false, false, false, false, true)
            .unwrap();
    }
    for query_count in [1, 7, 9] {
        for ood_count in [1, 2, 4] {
            let oods: Vec<_> = (0..ood_count).map(|i| extension(11 + i)).collect();
            let queries: Vec<_> = (0..query_count).map(|i| extension(21 + i)).collect();
            let coefficients: Vec<_> = (0..ood_count + query_count).map(|i| extension(31 + i)).collect();
            let scale = extension(71);
            let mut source = format!(
                "from extension import *\n\nOPT_BLOCK_QUERY_POWERS = 1\n\n{}\n\n{}\n\n{}\n\ndef main():\n",
                function("hiding_copy_extension"),
                function("update_query_powers_blocked"),
                function("build_switch_covector")
            );
            array(&mut source, "oods", &flatten(&oods));
            array(&mut source, "queries", &flatten(&queries));
            array(&mut source, "coefficients", &flatten(&coefficients));
            array(&mut source, "scale", &flatten(&[scale]));
            writeln!(source, "    result = Array({})\n    build_switch_covector(result, 3, {query_count}, {ood_count}, oods, coefficients, queries, scale)", (query_count + ood_count) * 5).unwrap();
            for slot in 0..query_count + ood_count {
                let mut expected: EF = oods
                    .iter()
                    .zip(&coefficients)
                    .map(|(&point, &coefficient)| coefficient * point.exp_u64((8 + slot) as u64))
                    .sum();
                if slot < query_count {
                    expected += queries
                        .iter()
                        .zip(&coefficients[ood_count..])
                        .map(|(&point, &coefficient)| coefficient * point.exp_u64((8 + slot) as u64))
                        .sum::<EF>();
                }
                expected *= scale;
                for (coordinate, value) in flatten(&[expected]).into_iter().enumerate() {
                    writeln!(source, "    assert result[{}] == {value}", slot * 5 + coordinate).unwrap();
                }
            }
            source.push_str("    return\n");
            sources
                .run_with_extension(&source, false, false, false, false, true)
                .unwrap();
        }
    }
}

#[test]
fn transcript_block_absorption_preserves_state_and_future_samples() {
    let sources = Sources::new();
    for length in [0usize, 1, 2, 5, 7, 8, 9, 10, 15, 16, 17, 31, 64] {
        let mut source = String::from("from transcript_poseidon1 import *\n\ndef main():\n");
        let values: Vec<_> = (0..length.max(1))
            .map(|i| ((i * 91 + 37) % 2_130_706_433) as u32)
            .collect();
        array(&mut source, "values", &values);
        for pending in 0..8 {
            for sampled in [0, 1, 7, 8, 9] {
                let name = format!("s{pending}_{sampled}");
                writeln!(source, "    {name}: Mut = fs_new()\n    {name} = _fs_duplex({name})").unwrap();
                for sample in 0..sampled {
                    writeln!(source, "    {name}, ignored_{name}_{sample} = fs_sample_base({name})").unwrap();
                }
                for word in 0..pending {
                    writeln!(source, "    {name} = fs_observe_one({name}, {})", word + 101).unwrap();
                }
                writeln!(source, "    {name} = fs_observe_const({name}, values, {length})").unwrap();
                for field in 0..26 {
                    writeln!(source, "    print({name}[{field}])").unwrap();
                }
                for sample in 0..10 {
                    writeln!(
                        source,
                        "    {name}, out_{name}_{sample} = fs_sample_base({name})\n    print(out_{name}_{sample})"
                    )
                    .unwrap();
                }
            }
        }
        source.push_str("    return\n");
        let expected = sources
            .run_with_transcript_options(&source, false, false, false, false, false, false)
            .unwrap();
        let actual = sources
            .run_with_transcript_options(&source, false, false, false, false, false, true)
            .unwrap();
        for (index, (actual_line, expected_line)) in actual.lines().zip(expected.lines()).enumerate() {
            assert_eq!(
                actual_line,
                expected_line,
                "slice length {length}, state {}, output {}",
                index / 36,
                index % 36
            );
        }
        assert_eq!(actual.lines().count(), expected.lines().count());
    }
}

#[test]
fn transcript_extension_sampling_preserves_state_and_samples() {
    let sources = Sources::new();
    let mut source = String::from("from transcript_poseidon1 import *\n\ndef main():\n");
    for pending in 0..8 {
        for sampled in 0..10 {
            let name = format!("s{pending}_{sampled}");
            writeln!(source, "    {name}: Mut = fs_new()\n    {name} = _fs_duplex({name})").unwrap();
            for sample in 0..sampled {
                writeln!(source, "    {name}, ignored_{name}_{sample} = fs_sample_base({name})").unwrap();
            }
            for word in 0..pending {
                writeln!(source, "    {name} = fs_observe_one({name}, {})", word + 101).unwrap();
            }
            for sample in 0..3 {
                writeln!(source, "    {name}, ef_{name}_{sample} = fs_sample_extension({name})").unwrap();
                for coordinate in 0..5 {
                    writeln!(source, "    print(ef_{name}_{sample}[{coordinate}])").unwrap();
                }
                for field in 0..26 {
                    writeln!(source, "    print({name}[{field}])").unwrap();
                }
            }
            for sample in 0..10 {
                writeln!(
                    source,
                    "    {name}, out_{name}_{sample} = fs_sample_base({name})\n    print(out_{name}_{sample})"
                )
                .unwrap();
            }
        }
    }
    source.push_str("    return\n");
    let expected = sources
        .run_with_transcript_options(&source, false, false, false, false, false, false)
        .unwrap();
    let actual = sources
        .run_with_transcript_options(&source, false, false, false, false, false, true)
        .unwrap();
    for (index, (actual_line, expected_line)) in actual.lines().zip(expected.lines()).enumerate() {
        assert_eq!(
            actual_line,
            expected_line,
            "state {}, output {}",
            index / 103,
            index % 103
        );
    }
    assert_eq!(actual.lines().count(), expected.lines().count());
}
