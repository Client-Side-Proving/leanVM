use backend::PrimeCharacteristicRing;
use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_vm::{Bytecode, CustomHint, ExecutionWitness, F, Hint, MemOrFpOrConstant, try_execute_bytecode};
use std::{collections::BTreeMap, fmt::Write, path::PathBuf};

struct Sources(PathBuf);

impl Sources {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "query-permutation-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&path).unwrap();
        for entry in std::fs::read_dir(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("zkdsl_implem")).unwrap() {
            let entry = entry.unwrap();
            if entry.path().extension().is_some_and(|extension| extension == "py") {
                std::fs::copy(entry.path(), path.join(entry.file_name())).unwrap();
            }
        }
        Self(path)
    }

    fn compile(&self, source: &str, permutation: bool, bits: bool) -> Bytecode {
        let path = self.0.join("query_test.py");
        std::fs::write(&path, source).unwrap();
        let mut replacements = BTreeMap::from([
            ("OPT_MERKLE_BITS_VALUE".into(), usize::from(bits).to_string()),
            ("OPT_MERKLE_PAIRED_VALUE".into(), "0".into()),
            ("OPT_QUERY_PRODUCT_VALUE".into(), "1".into()),
            ("OPT_RADIX_PREFIX_VALUE".into(), "1".into()),
            (
                "OPT_QUERY_PERMUTATION_VALUE".into(),
                usize::from(permutation).to_string(),
            ),
        ]);
        for matrix in ["A", "B", "C"] {
            for field in ["ROWS", "COLUMNS", "VALUES"] {
                replacements.insert(format!("FULL_ZK_MATRIX_{matrix}_{field}_PLACEHOLDER"), "[]".into());
            }
        }
        replacements.insert("OPT_EXTENSION_ARITHMETIC_VALUE".into(), "0".into());
        replacements.insert("OPT_TRANSCRIPT_BLOCKS_VALUE".into(), "0".into());
        compile_program_with_flags(
            &ProgramSource::Filepath(path.to_string_lossy().into()),
            CompilationFlags { replacements },
        )
    }
}

impl Drop for Sources {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn run(bytecode: &Bytecode) -> Result<String, String> {
    try_execute_bytecode(bytecode, &[F::ZERO; 8], &ExecutionWitness::default(), false)
        .map(|result| result.metadata.stdout)
        .map_err(|error| error.to_string())
}

fn array(source: &mut String, name: &str, values: &[u32]) {
    writeln!(source, "    {name} = Array({})", values.len()).unwrap();
    for (index, value) in values.iter().enumerate() {
        writeln!(source, "    {name}[{index}] = {value}").unwrap();
    }
}

#[test]
fn permutation_sampler_matches_existing_positions_bits_and_transcript() {
    let sources = Sources::new();
    for (domain_bits, count, max_draws) in [
        (1, 1, 8),
        (2, 4, 48),
        (4, 8, 64),
        (8, 24, 96),
        (18, 259, 323),
        (24, 3, 16),
    ] {
        for bits in [false, true] {
            let printed = count * (1 + usize::from(bits) * domain_bits);
            let source = format!(
                "from full_zk_production_common import *\n\ndef main():\n    for seed in unroll(0, 3):\n        fs = fs_observe_one(fs_new(), seed)\n        after, positions = sample_sorted_queries_bounded(fs, {count}, {domain_bits}, {max_draws})\n        for i in unroll(0, {printed}):\n            print(positions[i])\n        for i in unroll(0, FS_SIZE):\n            print(after[i])\n    return\n"
            );
            let control = run(&sources.compile(&source, false, bits)).unwrap();
            let candidate = run(&sources.compile(&source, true, bits)).unwrap();
            assert_eq!(
                candidate, control,
                "domain_bits={domain_bits}, count={count}, bits={bits}"
            );
        }
    }
}

fn buffered_sampler_source(outputs: &[u32], count: usize) -> String {
    let mut source = String::from("from full_zk_production_common import *\n\ndef main():\n");
    let mut state = vec![0; 26];
    for (index, value) in outputs.iter().enumerate() {
        state[outputs.len() - 1 - index] = *value;
    }
    state[25] = outputs.len() as u32;
    array(&mut source, "fs", &state);
    writeln!(
        source,
        "    after, positions = sample_sorted_queries_bounded(fs, {count}, 4, 16)\n    for i in unroll(0, {count}):\n        print(positions[i])\n    for i in unroll(0, FS_SIZE):\n        print(after[i])\n    return"
    )
    .unwrap();
    source
}

#[test]
fn sampler_preserves_rejection_collision_and_draw_exhaustion_behavior() {
    let sources = Sources::new();
    for outputs in [
        vec![17, 1, 34, 2, 51, 3, 68, 99],
        vec![2_130_706_432, 2_130_706_432, 2_130_706_432, 17, 1, 34, 51, 68],
    ] {
        let source = buffered_sampler_source(&outputs, 4);
        let control = run(&sources.compile(&source, false, true)).unwrap();
        let candidate = run(&sources.compile(&source, true, true)).unwrap();
        assert_eq!(candidate, control);
    }
    let rejected = buffered_sampler_source(&[2_130_706_432; 8], 1);
    for candidate in [false, true] {
        assert!(run(&sources.compile(&rejected, candidate, false)).is_err());
    }
    let exhausted = buffered_sampler_source(&[1; 8], 4).replace("4, 4, 16)", "4, 4, 4)");
    for candidate in [false, true] {
        assert!(run(&sources.compile(&exhausted, candidate, false)).is_err());
    }
}

fn permutation_check_source(draws: &[u32], flags: &[u32], permutation: &[u32], count: usize) -> String {
    let mut source = String::from("from full_zk_production_common import *\n\ndef main():\n");
    array(&mut source, "draws", draws);
    array(&mut source, "flags", flags);
    array(&mut source, "permutation", permutation);
    let bits: Vec<_> = draws
        .iter()
        .flat_map(|value| (0..4).map(move |bit| (value >> bit) & 1))
        .collect();
    array(&mut source, "bits", &bits);
    writeln!(
        source,
        "    positions = verify_query_permutation(draws, flags, bits, permutation, {}, {count}, 4, 16)\n    return",
        draws.len()
    )
    .unwrap();
    source
}

#[test]
fn permutation_checks_reject_bad_order_multiplicity_flags_and_stopping() {
    let sources = Sources::new();
    let draws = [5, 1, 5, 2];
    let flags = [1, 1, 0, 1];
    let permutation = [1, 3, 0, 2];
    assert!(run(&sources.compile(&permutation_check_source(&draws, &flags, &permutation, 3), true, true)).is_ok());
    for changed in [
        [1, 3, 0, 0],
        [1, 3, 2, 0],
        [3, 1, 0, 2],
        [1, 3, 0, 4],
        [1, 3, 0, 2_130_706_432],
    ] {
        assert!(run(&sources.compile(&permutation_check_source(&draws, &flags, &changed, 3), true, true)).is_err());
    }
    for changed in [[1, 0, 0, 1], [1, 1, 1, 1], [2, 1, 0, 1], [1, 1, 0, 0]] {
        assert!(
            run(&sources.compile(&permutation_check_source(&draws, &changed, &permutation, 3), true, true)).is_err()
        );
    }
    for source in [
        permutation_check_source(&[5, 1, 5], &[1, 1, 0], &[1, 0, 2], 3),
        permutation_check_source(&[5, 1, 5, 2, 2], &[1, 1, 0, 1, 0], &[1, 3, 4, 0, 2], 3),
        permutation_check_source(&[5, 1, 5, 2, 3], &[1, 1, 0, 1, 1], &[1, 3, 4, 0, 2], 3),
    ] {
        assert!(run(&sources.compile(&source, true, true)).is_err());
    }
}

#[test]
fn malicious_first_occurrence_hints_do_not_change_verified_bytecode() {
    let sources = Sources::new();
    let original = sources.compile(&buffered_sampler_source(&[5, 1, 5, 2, 3, 4, 7, 8], 3), true, true);
    assert!(run(&original).is_ok());
    for forced in [false, true] {
        let mut code = original.code().to_vec();
        let mut changed = 0;
        for entry in &mut code {
            for hint in &mut entry.hints {
                if let Hint::Custom(CustomHint::IsFirstOccurrence, args) = hint {
                    *hint = Hint::Custom(
                        CustomHint::LessThan,
                        vec![
                            MemOrFpOrConstant::Constant(F::ZERO),
                            MemOrFpOrConstant::Constant(F::from_bool(forced)),
                            args[3],
                        ],
                    );
                    changed += 1;
                }
            }
        }
        assert!(changed > 0);
        let corrupted = Bytecode::new(
            code,
            original.unpadded_size(),
            original.starting_frame_memory(),
            BTreeMap::new(),
            original.debug_info().clone(),
        );
        assert_eq!(corrupted.hash(), original.hash());
        assert!(run(&corrupted).is_err(), "forced first-occurrence flag={forced}");
    }
}

#[test]
fn sampler_parameter_bounds_fit_vm_range_checks_and_hint_allocations() {
    let sources = Sources::new();
    let original = permutation_check_source(&[5], &[1], &[0], 1);
    let largest = original.replace("1, 1, 4, 16)", "1, 1, 24, 32767)");
    assert!(run(&sources.compile(&largest, true, false)).is_ok());
    let too_large = largest.replace("24, 32767)", "24, 32768)");
    assert!(run(&sources.compile(&too_large, true, false)).is_err());
    for body in [
        "    hint_sort_indices(values, 32768, output)\n",
        "    first: Imm\n    hint_is_first_occurrence(values, 32768, 1, first)\n",
    ] {
        let source = format!(
            "from full_zk_production_common import *\n\ndef main():\n    values = Array(1)\n    values[0] = 1\n    output = Array(1)\n{body}    return\n"
        );
        assert!(run(&sources.compile(&source, true, false)).is_err());
    }
}
