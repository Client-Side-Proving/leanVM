use serde_json::Value;
use sha2::{Digest, Sha256};
use spartan_whir_guest::{
    FULL_ZK_DIRECT_POSEIDON2_WORDS, GuestError, compile_full_zk_direct_poseidon2_guest, decode_word_bytes,
    execute_full_zk_direct_poseidon2_guest, full_zk_direct_poseidon2_execution_witness,
    full_zk_direct_poseidon2_public_input, full_zk_direct_poseidon2_words, prove_full_zk_direct_poseidon2_guest,
};

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes).iter().map(|byte| format!("{byte:02x}")).collect()
}

#[test]
fn copied_full_zk_fixture_matches_its_manifest() {
    let manifest: Value = serde_json::from_str(include_str!(
        "../testdata/full_zk_direct_poseidon2/full_zk_direct_manifest.json"
    ))
    .unwrap();
    assert_eq!(manifest["hash_profile"], "poseidon2-width16-width24");
    assert_eq!(manifest["matrix_closing"], "direct_sparse");
    assert_eq!(manifest["guest_words"], FULL_ZK_DIRECT_POSEIDON2_WORDS);
    let trace: Vec<Value> = serde_json::from_str(include_str!(
        "../testdata/full_zk_direct_poseidon2/full_zk_direct_transcript_trace.json"
    ))
    .unwrap();
    assert_eq!(manifest["transcript_events"], trace.len());

    let artifacts: &[(&str, &[u8], &str)] = &[
        (
            "guest_input",
            include_bytes!("../testdata/full_zk_direct_poseidon2/full_zk_direct_guest_input.words"),
            "full_zk_direct_guest_input.words",
        ),
        (
            "guest_constants",
            include_bytes!("../testdata/full_zk_direct_poseidon2/full_zk_direct_guest_constants.json"),
            "full_zk_direct_guest_constants.json",
        ),
        (
            "statement",
            include_bytes!("../testdata/full_zk_direct_poseidon2/full_zk_direct_statement.json"),
            "full_zk_direct_statement.json",
        ),
        (
            "transcript_trace",
            include_bytes!("../testdata/full_zk_direct_poseidon2/full_zk_direct_transcript_trace.json"),
            "full_zk_direct_transcript_trace.json",
        ),
        (
            "verifying_key",
            include_bytes!("../testdata/full_zk_direct_poseidon2/full_zk_direct_verifying_key.json"),
            "full_zk_direct_verifying_key.json",
        ),
    ];
    for &(key, bytes, filename) in artifacts {
        assert_eq!(manifest["artifacts"][key]["file"], filename);
        assert_eq!(manifest["artifacts"][key]["bytes"], bytes.len());
        assert_eq!(manifest["artifacts"][key]["sha256"], sha256(bytes));
    }
}

#[test]
fn full_zk_direct_poseidon2_proof_executes_in_leanvm() {
    let compile = compile_full_zk_direct_poseidon2_guest().unwrap();
    let public_input = full_zk_direct_poseidon2_public_input().unwrap();
    let words = full_zk_direct_poseidon2_words().unwrap();
    let metadata = execute_full_zk_direct_poseidon2_guest(&compile.bytecode, &public_input, &words).unwrap();
    assert!(metadata.cycles > 0);
    assert_eq!(metadata.n_poseidons, 0);
}

#[test]
fn full_zk_direct_poseidon2_execution_proof_verifies() {
    let compile = compile_full_zk_direct_poseidon2_guest().unwrap();
    let public_input = full_zk_direct_poseidon2_public_input().unwrap();
    let words = full_zk_direct_poseidon2_words().unwrap();
    let root = prove_full_zk_direct_poseidon2_guest(&compile.bytecode, &public_input, &words).unwrap();
    assert!(root.serialized_proof_bytes > 0);
}

#[test]
fn full_zk_direct_poseidon2_mutations_are_rejected() {
    const EXECUTION_MUTATIONS: &[(&str, &[u8])] = &[
        (
            "changed public input",
            include_bytes!("../testdata/full_zk_direct_poseidon2/mutations/changed_public_input.words"),
        ),
        (
            "changed witness commitment",
            include_bytes!("../testdata/full_zk_direct_poseidon2/mutations/changed_witness_commitment.words"),
        ),
        (
            "changed application mask commitment",
            include_bytes!("../testdata/full_zk_direct_poseidon2/mutations/changed_application_mask_commitment.words"),
        ),
        (
            "changed outer sumcheck",
            include_bytes!("../testdata/full_zk_direct_poseidon2/mutations/changed_outer_sumcheck.words"),
        ),
        (
            "changed inner sumcheck",
            include_bytes!("../testdata/full_zk_direct_poseidon2/mutations/changed_inner_sumcheck.words"),
        ),
        (
            "changed hiding-WHIR base claim",
            include_bytes!("../testdata/full_zk_direct_poseidon2/mutations/changed_hiding_whir_base_claim.words"),
        ),
    ];

    let compile = compile_full_zk_direct_poseidon2_guest().unwrap();
    let public_input = full_zk_direct_poseidon2_public_input().unwrap();
    for &(name, bytes) in EXECUTION_MUTATIONS {
        let words = decode_word_bytes(bytes).unwrap();
        let result = execute_full_zk_direct_poseidon2_guest(&compile.bytecode, &public_input, &words);
        assert!(result.is_err(), "{name} was accepted");
    }

    let mut trailing = full_zk_direct_poseidon2_words().unwrap();
    trailing.push(0);
    assert!(matches!(
        full_zk_direct_poseidon2_execution_witness(&compile.bytecode, &trailing),
        Err(GuestError::InvalidWordCount { expected, actual })
            if expected == FULL_ZK_DIRECT_POSEIDON2_WORDS && actual == FULL_ZK_DIRECT_POSEIDON2_WORDS + 1
    ));
}
