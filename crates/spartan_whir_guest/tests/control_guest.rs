use backend::{KoalaBear, PrimeCharacteristicRing, PrimeField32, poseidon16_permute};
use serde_json::Value;
use sha2::{Digest, Sha256};
use spartan_whir_guest::{
    CONTROL_GUEST_WORDS, GuestError, compile_control_guest, compile_poseidon1_primitives_guest, control_public_input,
    control_words, decode_word_bytes, execute_control_guest, execute_poseidon1_primitives_guest, execution_witness,
    poseidon1_primitive_words, prove_control_guest,
};

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes).iter().map(|byte| format!("{byte:02x}")).collect()
}

#[test]
fn poseidon1_width_16_matches_the_spartan_whir_vector() {
    let input = core::array::from_fn(KoalaBear::from_usize);
    let actual = poseidon16_permute(input).map(|value| value.as_canonical_u32());
    assert_eq!(
        actual,
        [
            610_090_613,
            935_319_874,
            1_893_335_292,
            796_792_199,
            356_405_232,
            552_237_741,
            55_134_556,
            1_215_104_204,
            1_823_723_405,
            1_133_298_033,
            1_780_633_798,
            1_453_946_561,
            710_069_176,
            1_128_629_550,
            1_917_333_254,
            1_175_481_618,
        ]
    );
}

#[test]
fn poseidon1_precompile_matches_plonky3_challenger_leaf_and_node_vectors() {
    let compile = compile_poseidon1_primitives_guest();
    let words = poseidon1_primitive_words();
    let report = execute_poseidon1_primitives_guest(&compile.bytecode, &words).unwrap();
    assert!(report.metadata.cycles > 0);
    assert!(
        report
            .tables
            .iter()
            .any(|table| table.name == "poseidon16" && table.non_padded_rows > 0)
    );

    for index in [0, 23, 35, 59, 67, 75, 83] {
        let mut tampered = words.clone();
        tampered[index] = (tampered[index] + 1) % 2_130_706_433;
        assert!(execute_poseidon1_primitives_guest(&compile.bytecode, &tampered).is_err());
    }
}

#[test]
fn copied_m0_fixture_matches_its_manifest() {
    let manifest: Value = serde_json::from_str(include_str!("../testdata/control_fixture_manifest.json")).unwrap();
    assert_eq!(
        manifest["profile_id"],
        "spartan-whir-poseidon2-quintic-no-zk-direct-control-v1"
    );
    assert_eq!(manifest["guest_input_words"], CONTROL_GUEST_WORDS);
    let trace: Vec<Value> = serde_json::from_str(include_str!("../testdata/control_transcript_trace.json")).unwrap();
    assert_eq!(manifest["transcript_events"], trace.len());

    let artifacts: &[(&str, &[u8], &str)] = &[
        (
            "guest_input",
            include_bytes!("../testdata/control_guest_input.words"),
            "control_guest_input.words",
        ),
        (
            "guest_constants",
            include_bytes!("../testdata/control_guest_constants.json"),
            "control_guest_constants.json",
        ),
        (
            "statement",
            include_bytes!("../testdata/control_statement.json"),
            "control_statement.json",
        ),
        (
            "transcript_trace",
            include_bytes!("../testdata/control_transcript_trace.json"),
            "control_transcript_trace.json",
        ),
    ];
    for &(key, bytes, filename) in artifacts {
        assert_eq!(manifest[key]["file"], filename);
        assert_eq!(manifest[key]["bytes"], bytes.len());
        assert_eq!(manifest[key]["sha256"], sha256(bytes));
    }
}

#[test]
fn control_proof_executes_in_leanvm() {
    let compile = compile_control_guest().unwrap();
    let public_input = control_public_input().unwrap();
    let words = control_words().unwrap();
    let metadata = execute_control_guest(&compile.bytecode, &public_input, &words).unwrap();
    assert!(metadata.cycles > 0);
}

#[test]
fn control_execution_proof_verifies() {
    let compile = compile_control_guest().unwrap();
    let public_input = control_public_input().unwrap();
    let words = control_words().unwrap();
    let root = prove_control_guest(&compile.bytecode, &public_input, &words).unwrap();
    assert!(root.serialized_proof_bytes > 0);
}

#[test]
fn control_mutations_are_rejected() {
    const EXECUTION_MUTATIONS: &[(&str, &[u8])] = &[
        (
            "changed public input",
            include_bytes!("../testdata/mutations/changed_public_input.words"),
        ),
        (
            "changed witness commitment",
            include_bytes!("../testdata/mutations/changed_witness_commitment.words"),
        ),
        (
            "changed outer sumcheck",
            include_bytes!("../testdata/mutations/changed_outer_sumcheck.words"),
        ),
        (
            "changed outer claim",
            include_bytes!("../testdata/mutations/changed_outer_claim.words"),
        ),
        (
            "changed inner sumcheck",
            include_bytes!("../testdata/mutations/changed_inner_sumcheck.words"),
        ),
        (
            "changed witness evaluation",
            include_bytes!("../testdata/mutations/changed_witness_evaluation.words"),
        ),
        (
            "changed WHIR opening",
            include_bytes!("../testdata/mutations/changed_whir_opening.words"),
        ),
        (
            "wrong version",
            include_bytes!("../testdata/mutations/wrong_version.words"),
        ),
    ];

    let compile = compile_control_guest().unwrap();
    let public_input = control_public_input().unwrap();
    for &(name, bytes) in EXECUTION_MUTATIONS {
        let words = decode_word_bytes(bytes).unwrap();
        let result = execute_control_guest(&compile.bytecode, &public_input, &words);
        assert!(result.is_err(), "{name} was accepted");
    }

    let trailing = decode_word_bytes(include_bytes!("../testdata/mutations/trailing_word.words")).unwrap();
    assert!(matches!(
        execution_witness(&compile.bytecode, &trailing),
        Err(GuestError::InvalidWordCount { expected, actual })
            if expected == CONTROL_GUEST_WORDS && actual == CONTROL_GUEST_WORDS + 1
    ));
}
