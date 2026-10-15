use super::*;
use crate::{
    ProverError, WhirExecutionProfile,
    prove_execution::{prove_execution_with_profile_and_hash, prove_execution_with_profile_hash_and_public_memory},
    verify_execution::{verify_execution_with_profile_and_hash, verify_execution_with_profile_hash_and_public_memory},
};
use backend::*;
use lean_compiler::{ProgramSource, compile_program};
use lean_vm::{EF, ExecutionWitness, Hints, PUBLIC_INPUT_LEN};

fn region() -> PublicMemoryRegion {
    PublicMemoryRegion {
        start: 4096,
        values: (1..=256).map(F::from_usize).collect(),
    }
}

#[test]
fn public_memory_geometry_and_witness_are_checked() {
    let region = region();
    assert_eq!(region.num_variables(), 8);
    assert_eq!(region.selector(), 16);
    assert_eq!(
        region.transcript_header(),
        [0x5055_4d31, 4096, 256, 0, 0, 0, 0, 0].map(F::from_u32)
    );
    let mut memory = vec![F::ZERO; 4352];
    memory[4096..].copy_from_slice(&region.values);
    assert!(region.check_witness(&memory).is_ok());
    memory[4200] += F::ONE;
    assert!(region.check_witness(&memory).is_err());
    assert!(region.validate_for_memory_len(4351).is_err());
    for invalid in [
        PublicMemoryRegion {
            start: 4096,
            values: vec![],
        },
        PublicMemoryRegion {
            start: 4096,
            values: vec![F::ZERO; 255],
        },
        PublicMemoryRegion {
            start: 4097,
            values: region.values.clone(),
        },
        PublicMemoryRegion {
            start: usize::MAX,
            values: vec![F::ZERO],
        },
        PublicMemoryRegion {
            start: 1 << MAX_LOG_MEMORY_SIZE,
            values: vec![F::ZERO],
        },
    ] {
        assert!(invalid.validate().is_err());
    }
}

fn first_challenge(header: Option<[F; 8]>, values: &[F], cap: [F; 8]) -> EF {
    let mut state = ProverState::new_with_hash_profile(get_poseidon16().clone(), cap, ProofHashProfile::Keccak240);
    state.observe_scalars(&[F::ZERO; PUBLIC_INPUT_LEN]);
    if let Some(header) = header {
        state.observe_scalars(&header);
        state.observe_scalars(values);
    }
    state.sample()
}

#[test]
fn public_memory_statement_changes_first_challenge() {
    let region = region();
    let header = region.transcript_header();
    let cap = [F::ZERO; 8];
    let expected = first_challenge(Some(header), &region.values, cap);
    for index in [0, 1, 2] {
        let mut changed = header;
        changed[index] += F::ONE;
        assert_ne!(expected, first_challenge(Some(changed), &region.values, cap));
    }
    let mut changed = region.values.clone();
    changed[104] += F::ONE;
    assert_ne!(expected, first_challenge(Some(header), &changed, cap));
    changed = region.values.clone();
    changed.swap(0, 1);
    assert_ne!(expected, first_challenge(Some(header), &changed, cap));
    assert_ne!(expected, first_challenge(None, &[], cap));
    let mut other_cap = cap;
    other_cap[0] = F::ONE;
    assert_ne!(expected, first_challenge(Some(header), &region.values, other_cap));
}

#[test]
fn public_memory_proof_roundtrip_and_statement_substitution() {
    let bytecode = compile_program(&ProgramSource::Raw(
        "def main():\n    data = fixed_address()\n    hint_witness(\"region\", data)\n    for i in unroll(0, 256):\n        assert data[i] == i + 1\n    public = 0\n    for i in unroll(0, 8):\n        public[i] = i + 1\n    return\n\ndef fixed_address():\n    return 4096\n".to_owned(),
    ));
    let region = region();
    let public_input = std::array::from_fn(|i| F::from_usize(i + 1));
    let mut hints = Hints::default();
    hints.insert(&bytecode, "region", arena_vec![ArenaVec::from_slice(&region.values)]);
    let witness = ExecutionWitness {
        preamble_memory_len: 4344,
        hints,
        ..Default::default()
    };
    let profile = WhirExecutionProfile {
        security_bits: 40,
        grinding_bits: 0,
        first_folding_factor: 3,
        subsequent_folding_factor: 3,
        rs_domain_initial_reduction_factor: 3,
        max_num_variables_to_send_coeffs: 4,
        log_inv_rate: 1,
    };
    let hash = ProofHashProfile::Keccak240;
    let proof = prove_execution_with_profile_hash_and_public_memory(
        &bytecode,
        &public_input,
        &witness,
        &profile,
        hash,
        Some(&region),
        false,
    )
    .expect("public memory proof");
    let verify = |candidate: Option<&PublicMemoryRegion>, input: &[F; PUBLIC_INPUT_LEN]| {
        verify_execution_with_profile_hash_and_public_memory(
            &bytecode,
            input,
            proof.proof.clone(),
            &profile,
            hash,
            candidate,
        )
    };
    assert!(verify(Some(&region), &public_input).is_ok());
    assert!(verify(None, &public_input).is_err());
    let mut changed = region.clone();
    changed.values[104] += F::ONE;
    assert!(verify(Some(&changed), &public_input).is_err());
    assert!(matches!(
        prove_execution_with_profile_hash_and_public_memory(
            &bytecode,
            &public_input,
            &witness,
            &profile,
            hash,
            Some(&changed),
            false,
        ),
        Err(ProverError::InvalidPublicMemory(_))
    ));
    changed = region.clone();
    changed.start += 256;
    assert!(verify(Some(&changed), &public_input).is_err());
    changed = region.clone();
    changed.values.truncate(128);
    assert!(verify(Some(&changed), &public_input).is_err());
    let mut changed_input = public_input;
    changed_input[0] += F::ONE;
    assert!(verify(Some(&region), &changed_input).is_err());

    // None retains the existing transcript, including its verifier entry point.
    let legacy = prove_execution_with_profile_and_hash(&bytecode, &public_input, &witness, &profile, hash, false)
        .expect("legacy proof");
    assert!(
        verify_execution_with_profile_hash_and_public_memory(
            &bytecode,
            &public_input,
            legacy.proof.clone(),
            &profile,
            hash,
            None,
        )
        .is_ok()
    );
    assert!(verify_execution_with_profile_and_hash(&bytecode, &public_input, legacy.proof, &profile, hash,).is_ok());
}
