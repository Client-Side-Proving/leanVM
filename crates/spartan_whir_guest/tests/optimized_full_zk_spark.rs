use serde_json::Value;
use spartan_whir_guest::{
    GuestError, SparkGuestOptimizations, compact_full_zk_spark_words,
    compile_full_zk_spark_poseidon1_guest_with_optimizations, execute_full_zk_spark_poseidon1_guest_report,
    full_zk_spark_compact_offset, full_zk_spark_poseidon1_execution_witness, full_zk_spark_poseidon1_public_input,
    full_zk_spark_poseidon1_words, validate_full_zk_spark_poseidon1_guest,
};

#[test]
fn arithmetic_only_options_preserve_the_original_input_layout() {
    let original = full_zk_spark_poseidon1_words().unwrap();
    for options in [
        SparkGuestOptimizations::default(),
        SparkGuestOptimizations {
            fresh_relation: true,
            merkle_query_bits: true,
            ..SparkGuestOptimizations::default()
        },
    ] {
        assert_eq!(compact_full_zk_spark_words(&original, &options).unwrap(), original);
        assert_eq!(
            full_zk_spark_compact_offset(original.len() - 1, &options).unwrap(),
            Some(original.len() - 1)
        );
        assert_eq!(full_zk_spark_compact_offset(original.len(), &options).unwrap(), None);
    }
}

#[test]
fn optimized_guest_fits_capacity_and_rejects_mutations() {
    let options = SparkGuestOptimizations::recommended();
    let compiled = compile_full_zk_spark_poseidon1_guest_with_optimizations(&options).unwrap();
    let public_input = full_zk_spark_poseidon1_public_input().unwrap();
    let original = full_zk_spark_poseidon1_words().unwrap();
    let compact = compact_full_zk_spark_words(&original, &options).unwrap();
    assert!(compact.len() < original.len());
    let report = execute_full_zk_spark_poseidon1_guest_report(&compiled.bytecode, &public_input, &compact).unwrap();
    assert!(report.metadata.cycles < 1usize << 24);
    assert!(report.padded_memory_cells <= 1usize << 25);
    assert!(report.metadata.n_extension_ops < 1usize << 20);
    assert!(report.metadata.n_poseidons < 1usize << 17);

    let mutations: Value = serde_json::from_str(include_str!(
        "../testdata/full_zk_spark_poseidon1/full_zk_spark_mutations.json"
    ))
    .unwrap();
    for case in mutations["cases"].as_array().unwrap() {
        let mut changed = compact.clone();
        for patch in case["patches"].as_array().unwrap() {
            let offset = full_zk_spark_compact_offset(patch["offset"].as_u64().unwrap() as usize, &options)
                .unwrap()
                .expect("mutation field remains encoded");
            assert_eq!(changed[offset], patch["before"].as_u64().unwrap() as u32);
            changed[offset] = patch["after"].as_u64().unwrap() as u32;
        }
        assert!(
            validate_full_zk_spark_poseidon1_guest(&compiled.bytecode, &public_input, &changed).is_err(),
            "{}",
            case["name"]
        );
    }
    assert!(matches!(
        full_zk_spark_poseidon1_execution_witness(&compiled.bytecode, &compact[..compact.len() - 1]),
        Err(GuestError::InvalidWordCount { .. })
    ));
    let mut trailing = compact.clone();
    trailing.push(0);
    assert!(matches!(
        full_zk_spark_poseidon1_execution_witness(&compiled.bytecode, &trailing),
        Err(GuestError::InvalidWordCount { .. })
    ));
    let mut noncanonical = compact;
    noncanonical[0] = 2_130_706_433;
    assert!(matches!(
        full_zk_spark_poseidon1_execution_witness(&compiled.bytecode, &noncanonical),
        Err(GuestError::NonCanonicalWord { .. })
    ));
}
