use serde_json::Value;
use sha2::{Digest, Sha256};
use spartan_whir_guest::{
    FULL_ZK_SPARK_POSEIDON1_WORDS, SparkGuestFixture, compile_full_zk_spark_poseidon1_guest,
    execute_full_zk_spark_poseidon1_guest_report, full_zk_spark_poseidon1_public_input, full_zk_spark_poseidon1_words,
    validate_full_zk_spark_poseidon1_guest,
};

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes).iter().map(|byte| format!("{byte:02x}")).collect()
}

fn assertion_failure(error: &str) -> String {
    // Allocation offsets depend on the generated WHIR schedule dispatch.
    // Retain the failure category and both conflicting field values.
    const PREFIX: &str = "LeanVM execution failed: memory already set at ";
    if let Some((address, values)) = error.strip_prefix(PREFIX).and_then(|rest| rest.split_once(':')) {
        assert!(address.parse::<usize>().is_ok());
        return format!("{PREFIX}<address>:{values}");
    }
    error.to_owned()
}

#[test]
fn production_fixture_and_mutations_validate_in_leanvm() {
    let manifest: Value = serde_json::from_str(include_str!(
        "../testdata/full_zk_spark_poseidon1/full_zk_spark_manifest.json"
    ))
    .unwrap();
    assert_eq!(manifest["hash_profile"], "poseidon1-width16");
    assert_eq!(manifest["matrix_closing"], "spark");
    assert_eq!(manifest["guest_words"], FULL_ZK_SPARK_POSEIDON1_WORDS);
    assert_eq!(
        manifest["canonical_words"],
        SparkGuestFixture::embedded().unwrap().canonical_words()
    );
    let artifacts: &[(&str, &[u8], &str)] = &[
        (
            "guest_input",
            include_bytes!("../testdata/full_zk_spark_poseidon1/full_zk_spark_guest_input.words"),
            "full_zk_spark_guest_input.words",
        ),
        (
            "guest_layout",
            include_bytes!("../testdata/full_zk_spark_poseidon1/full_zk_spark_guest_layout.json"),
            "full_zk_spark_guest_layout.json",
        ),
        (
            "guest_constants",
            include_bytes!("../testdata/full_zk_spark_poseidon1/full_zk_spark_guest_constants.json"),
            "full_zk_spark_guest_constants.json",
        ),
        (
            "transcript_trace",
            include_bytes!("../testdata/full_zk_spark_poseidon1/full_zk_spark_transcript_trace.json"),
            "full_zk_spark_transcript_trace.json",
        ),
        (
            "statement",
            include_bytes!("../testdata/full_zk_spark_poseidon1/full_zk_spark_statement.json"),
            "full_zk_spark_statement.json",
        ),
        (
            "mutations",
            include_bytes!("../testdata/full_zk_spark_poseidon1/full_zk_spark_mutations.json"),
            "full_zk_spark_mutations.json",
        ),
    ];
    for &(key, bytes, filename) in artifacts {
        assert_eq!(manifest["artifacts"][key]["file"], filename);
        assert_eq!(manifest["artifacts"][key]["bytes"], bytes.len());
        assert_eq!(manifest["artifacts"][key]["sha256"], sha256(bytes));
    }

    let statement: Value = serde_json::from_str(include_str!(
        "../testdata/full_zk_spark_poseidon1/full_zk_spark_statement.json"
    ))
    .unwrap();
    assert_eq!(statement["schema"], "sha256-digest-bits-msb-first-v1");
    assert_eq!(statement["inner_public_inputs"].as_array().unwrap().len(), 256);
    assert_eq!(statement["digest"].as_array().unwrap().len(), 8);

    let compile = compile_full_zk_spark_poseidon1_guest().unwrap();
    let public_input = full_zk_spark_poseidon1_public_input().unwrap();
    assert_eq!(public_input.len(), 8);
    let honest_words = full_zk_spark_poseidon1_words().unwrap();
    let report = execute_full_zk_spark_poseidon1_guest_report(&compile.bytecode, &public_input, &honest_words).unwrap();
    assert!(
        report.metadata.cycles < (1usize << 25),
        "execution cycles reached the fixed 2^25 table ceiling"
    );
    assert!(report.padded_memory_cells <= 1usize << 26);

    let mutations: Value = serde_json::from_str(include_str!(
        "../testdata/full_zk_spark_poseidon1/full_zk_spark_mutations.json"
    ))
    .unwrap();
    for case in mutations["cases"].as_array().unwrap() {
        let mut changed = honest_words.clone();
        for patch in case["patches"].as_array().unwrap() {
            let offset = patch["offset"].as_u64().unwrap() as usize;
            let before = patch["before"].as_u64().unwrap() as u32;
            let after = patch["after"].as_u64().unwrap() as u32;
            assert_eq!(changed[offset], before, "{} precondition", case["name"]);
            changed[offset] = after;
        }
        let error = validate_full_zk_spark_poseidon1_guest(&compile.bytecode, &public_input, &changed).unwrap_err();
        assert_eq!(
            assertion_failure(&error.to_string()),
            assertion_failure(case["expected_guest_error"].as_str().unwrap()),
            "{} failed at a different guest assertion",
            case["name"]
        );
        assert!(!case["assertion_site"].as_str().unwrap().is_empty());
    }
}
