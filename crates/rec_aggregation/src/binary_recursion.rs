use std::collections::BTreeMap;

use backend::{
    ArenaVec, BasedVectorSpace, Evaluation, MleOwned, MultilinearPoint, PrimeCharacteristicRing, PrimeField32,
    ProofError, ProofHashProfile, RawProof, SparseStatement, WhirConfig, arena_vec, poseidon_hash_slice,
};
use lean_prover::{
    PublicMemoryRegion, TwoCommitmentWhirPreprocessedCommitment, TwoCommitmentWhirProverInput,
    TwoCommitmentWhirStatementBinding, TwoCommitmentWhirVerifierInput, WhirExecutionProfile, default_whir_config,
    fiat_shamir_domain_sep,
    prove_execution::{
        ExecutionProof, prove_execution, prove_execution_with_profile, prove_execution_with_profile_and_hash,
        prove_execution_with_profile_hash_and_public_memory, prove_execution_with_two_commitment_whir,
    },
    verify_execution::{
        verify_execution, verify_execution_with_profile, verify_execution_with_profile_and_hash,
        verify_execution_with_profile_hash_and_public_memory, verify_execution_with_two_commitment_whir,
    },
};
use lean_vm::{Bytecode, DIGEST_LEN, DIMENSION, EF, ExecutionWitness, F, Hints, PUBLIC_INPUT_LEN};

use crate::bytecode_claims::{
    ReducedBytecodeClaims, bytecode_reduction_sumcheck_proof_size, compute_bytecode_value_at_for,
    flatten_bytecode_claim, reduce_evaluations_for_bytecode, reduce_evaluations_for_bytecode_with_cap,
};
use crate::compilation::{
    NUM_REPEATED_ONES, RecursiveChildShape, RecursiveVerifierOptions, ZERO_VEC_LEN, compile_recursive_entry,
    compile_recursive_entry_for_dimension, compile_recursive_entry_for_fixed_shape,
    compile_recursive_entry_with_options,
};
use crate::{AggregationError, InnerVerified};

pub const LIFTED_INFO_DOMAIN: u32 = 1_279_677_489; // ASCII "LFT1".
pub const BINARY_NODE_INFO_DOMAIN: u32 = 1_313_817_649; // ASCII "NOD1".
pub const RECURSIVE_VERIFIER_PREAMBLE_MEMORY_LEN: usize = ZERO_VEC_LEN + DIGEST_LEN + DIMENSION + NUM_REPEATED_ONES;
pub const TERMINAL_NODE_INFO_ADDRESS: usize = 4096;
pub const TERMINAL_NODE_INFO_SIZE: usize = 256;
pub const TERMINAL_NODE_PREAMBLE_MEMORY_LEN: usize =
    TERMINAL_NODE_INFO_ADDRESS + TERMINAL_NODE_INFO_SIZE - PUBLIC_INPUT_LEN;
pub const TERMINAL_C1_TWO_COMMITMENT_BATCHING_POW_BITS: usize = lean_prover::TWO_COMMITMENT_WHIR_BATCHING_POW_BITS;
pub const TERMINAL_C1_EXECUTION_PROGRAM_PREFIX: [usize; 2] = [1, 1];

/// The application-derived fixed-program commitment used by terminal C1 proofs.
///
/// The evaluation vector is laid out as `[spark | lift | root | zero padding]`.
/// Within the occupied power-of-two region, spark occupies the lower half and
/// lift and root occupy the two quarters of the upper half.
#[derive(Debug)]
pub struct TerminalC1FixedPrograms {
    pub program_dimensions: [usize; 3],
    pub num_variables: usize,
    pub actual_data_len: usize,
    pub polynomial: MleOwned<EF>,
    pub whir_config: WhirConfig<EF>,
}

#[derive(Debug, Clone)]
pub struct TerminalC1VerifierPreprocessing {
    pub program_dimensions: [usize; 3],
    pub num_variables: usize,
    pub actual_data_len: usize,
    pub expected_keccak240_root: [F; DIGEST_LEN],
}

impl TerminalC1FixedPrograms {
    /// Precompute the fixed Merkle tree once, before online proof generation.
    pub fn preprocess_keccak240(&self) -> TwoCommitmentWhirPreprocessedCommitment {
        let (prover_data, root) = self.whir_config.build_commitment_data_with_hash_profile(
            &self.polynomial,
            self.actual_data_len,
            ProofHashProfile::Keccak240,
        );
        TwoCommitmentWhirPreprocessedCommitment { prover_data, root }
    }

    pub fn verifier_preprocessing_with_root(
        &self,
        expected_keccak240_root: [F; DIGEST_LEN],
    ) -> TerminalC1VerifierPreprocessing {
        TerminalC1VerifierPreprocessing {
            program_dimensions: self.program_dimensions,
            num_variables: self.num_variables,
            actual_data_len: self.actual_data_len,
            expected_keccak240_root,
        }
    }

    pub fn verifier_preprocessing(&self) -> TerminalC1VerifierPreprocessing {
        let commitment = self.preprocess_keccak240();
        self.verifier_preprocessing_with_root(commitment.root)
    }

    /// Embed the two public fixed-program claims in the combined polynomial.
    /// Each prefix selects its program inside the occupied region, including
    /// leading zero coordinates for any trailing padding.
    pub fn public_statements(&self, info: &BinaryNodeInfo) -> Result<Vec<SparseStatement<EF>>, ProofError> {
        terminal_c1_public_statements(self.program_dimensions, self.num_variables, info)
    }
}

impl TerminalC1VerifierPreprocessing {
    pub fn public_statements(&self, info: &BinaryNodeInfo) -> Result<Vec<SparseStatement<EF>>, ProofError> {
        terminal_c1_public_statements(self.program_dimensions, self.num_variables, info)
    }
}

fn terminal_c1_public_statements(
    program_dimensions: [usize; 3],
    num_variables: usize,
    info: &BinaryNodeInfo,
) -> Result<Vec<SparseStatement<EF>>, ProofError> {
    let claims = [&info.original_bytecode_claim, &info.child_bytecode_claim];
    if claims[0].point.len() != program_dimensions[0] || claims[1].point.len() != program_dimensions[1] {
        return Err(ProofError::InvalidProof);
    }

    let [spark_prefix, lift_prefix, _] = terminal_c1_program_prefixes(program_dimensions, num_variables)?;
    Ok(claims
        .into_iter()
        .zip([spark_prefix, lift_prefix])
        .map(|(claim, prefix)| {
            let mut point = Vec::with_capacity(num_variables);
            point.extend_from_slice(&prefix);
            point.extend_from_slice(&claim.point);
            SparseStatement::dense(MultilinearPoint(point), claim.value)
        })
        .collect())
}

fn terminal_c1_point_prefix(
    num_variables: usize,
    program_num_variables: usize,
    suffix: &[EF],
) -> Result<Vec<EF>, ProofError> {
    let prefix_len = num_variables
        .checked_sub(program_num_variables)
        .filter(|&len| len >= suffix.len() && num_variables < usize::BITS as usize)
        .ok_or(ProofError::InvalidProof)?;
    let mut prefix = vec![EF::ZERO; prefix_len];
    prefix[prefix_len - suffix.len()..].copy_from_slice(suffix);
    Ok(prefix)
}

fn terminal_c1_program_prefixes(
    program_dimensions: [usize; 3],
    num_variables: usize,
) -> Result<[Vec<EF>; 3], ProofError> {
    if program_dimensions[1].checked_add(1) != Some(program_dimensions[0])
        || program_dimensions[1] != program_dimensions[2]
    {
        return Err(ProofError::InvalidProof);
    }
    Ok([
        terminal_c1_point_prefix(num_variables, program_dimensions[0], &[EF::ZERO])?,
        terminal_c1_point_prefix(num_variables, program_dimensions[1], &[EF::ONE, EF::ZERO])?,
        terminal_c1_point_prefix(num_variables, program_dimensions[2], &[EF::ONE, EF::ONE])?,
    ])
}

/// Select the root program within the terminal polynomial's occupied region.
pub fn terminal_c1_execution_program_prefix(
    root_bytecode: &Bytecode,
    num_variables: usize,
) -> Result<Vec<EF>, ProofError> {
    terminal_c1_point_prefix(
        num_variables,
        root_bytecode.cumulated_n_vars(),
        &TERMINAL_C1_EXECUTION_PROGRAM_PREFIX.map(EF::from_usize),
    )
}

/// Offsets of the spark and lift claim coefficients in the observed terminal
/// public-memory region, in the same order as `terminal_c1_public_statements`.
pub fn terminal_c1_statement_public_memory_bindings(
    spark_bytecode: &Bytecode,
    lift_bytecode: &Bytecode,
) -> [TwoCommitmentWhirStatementBinding; 2] {
    let layout = NodeInfoLayout::for_children(spark_bytecode, lift_bytecode);
    [
        TwoCommitmentWhirStatementBinding {
            public_memory_offset: layout.original_claim_offset,
            point_prefix: vec![EF::ZERO],
        },
        TwoCommitmentWhirStatementBinding {
            public_memory_offset: layout.claim_offset,
            point_prefix: vec![EF::ONE, EF::ZERO],
        },
    ]
}

/// Bind the two public claims when the fixed-program polynomial is zero-padded
/// to the application-selected execution dimension.
pub fn terminal_c1_statement_public_memory_bindings_for_dimension(
    spark_bytecode: &Bytecode,
    lift_bytecode: &Bytecode,
    num_variables: usize,
) -> Result<[TwoCommitmentWhirStatementBinding; 2], ProofError> {
    let spark_dimension = spark_bytecode.cumulated_n_vars();
    let lift_dimension = lift_bytecode.cumulated_n_vars();
    let [spark_prefix, lift_prefix, _] =
        terminal_c1_program_prefixes([spark_dimension, lift_dimension, lift_dimension], num_variables)?;
    let mut bindings = terminal_c1_statement_public_memory_bindings(spark_bytecode, lift_bytecode);
    bindings[0].point_prefix = spark_prefix;
    bindings[1].point_prefix = lift_prefix;
    Ok(bindings)
}

#[derive(Debug, Clone)]
pub struct LiftedExecutionInfo {
    pub application_digest: [F; PUBLIC_INPUT_LEN],
    pub child_bytecode_claim: Evaluation<EF>,
}

#[derive(Debug, Clone)]
pub struct LiftedExecutionProof {
    pub info: LiftedExecutionInfo,
    pub proof: ExecutionProof,
}

#[derive(Debug, Clone)]
pub struct BinaryNodeInfo {
    pub original_bytecode_claim: Evaluation<EF>,
    pub application_root: [F; PUBLIC_INPUT_LEN],
    pub child_bytecode_claim: Evaluation<EF>,
}

#[derive(Debug, Clone)]
pub struct BinaryNodeProof {
    pub info: BinaryNodeInfo,
    pub proof: ExecutionProof,
}

#[derive(Debug, Clone, Copy)]
struct LiftedInfoLayout {
    claim_offset: usize,
    claim_size_padded: usize,
    cap_offset: usize,
    application_digest_offset: usize,
    size: usize,
}

impl LiftedInfoLayout {
    fn for_child(child_bytecode: &Bytecode) -> Self {
        let claim_offset = DIGEST_LEN;
        let claim_size_padded = child_bytecode.bytecode_claim_size().next_multiple_of(DIGEST_LEN);
        let cap_offset = claim_offset + claim_size_padded;
        let application_digest_offset = cap_offset + DIGEST_LEN;
        let size = application_digest_offset + DIGEST_LEN;
        Self {
            claim_offset,
            claim_size_padded,
            cap_offset,
            application_digest_offset,
            size,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct NodeInfoLayout {
    original_claim_offset: usize,
    original_claim_size_padded: usize,
    claim_offset: usize,
    claim_size_padded: usize,
    cap_offset: usize,
    application_root_offset: usize,
    size: usize,
}

impl NodeInfoLayout {
    fn for_children(original_bytecode: &Bytecode, child_bytecode: &Bytecode) -> Self {
        let claim_offset = DIGEST_LEN;
        let claim_size_padded = child_bytecode.bytecode_claim_size().next_multiple_of(DIGEST_LEN);
        let cap_offset = claim_offset + claim_size_padded;
        let original_claim_offset = cap_offset + DIGEST_LEN;
        let original_claim_size_padded = original_bytecode.bytecode_claim_size().next_multiple_of(DIGEST_LEN);
        let application_root_offset = original_claim_offset + original_claim_size_padded;
        let size = application_root_offset + DIGEST_LEN;
        Self {
            claim_offset,
            claim_size_padded,
            cap_offset,
            original_claim_offset,
            original_claim_size_padded,
            application_root_offset,
            size,
        }
    }
}

fn original_bytecode_reduction_cap(bytecode: &Bytecode) -> [F; DIGEST_LEN] {
    let mut cap = fiat_shamir_domain_sep(bytecode);
    cap[0] += F::from_u32(0x4f424331); // Separate the original-bytecode reduction transcript.
    cap
}

fn original_bytecode_replacements(bytecode: &Bytecode) -> BTreeMap<String, String> {
    let mut replacements = BTreeMap::new();
    for (key, value) in [
        ("ORIGINAL_POINT_N_VARS_PLACEHOLDER", bytecode.cumulated_n_vars()),
        ("ORIGINAL_CLAIM_SIZE_PLACEHOLDER", bytecode.bytecode_claim_size()),
        (
            "ORIGINAL_CLAIM_SIZE_PADDED_PLACEHOLDER",
            bytecode.bytecode_claim_size().next_multiple_of(DIGEST_LEN),
        ),
        (
            "ORIGINAL_SUMCHECK_SIZE_PLACEHOLDER",
            bytecode_reduction_sumcheck_proof_size(bytecode.cumulated_n_vars()),
        ),
    ] {
        replacements.insert(key.to_owned(), value.to_string());
    }
    replacements.insert(
        "ORIGINAL_REDUCTION_CAP_PLACEHOLDER".to_owned(),
        format!(
            "[{}]",
            original_bytecode_reduction_cap(bytecode)
                .iter()
                .map(|x| x.as_canonical_u32().to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ),
    );
    replacements
}

pub fn compile_lifted_execution_bytecode(child_bytecode: &Bytecode) -> Bytecode {
    compile_recursive_entry(
        "lift_execution.py",
        child_bytecode,
        expected_child_cap_replacement(child_bytecode, None),
    )
}

pub fn compile_binary_node_bytecode(child_bytecode: &Bytecode, lifted_child_bytecode: &Bytecode) -> Bytecode {
    let lifted_layout = LiftedInfoLayout::for_child(child_bytecode);
    let mut replacements = expected_child_cap_replacement(lifted_child_bytecode, None);
    replacements.extend(original_bytecode_replacements(child_bytecode));
    replacements.insert(
        "LIFTED_INFO_SIZE_PLACEHOLDER".to_string(),
        lifted_layout.size.to_string(),
    );
    replacements.insert(
        "LIFTED_INFO_NUM_CHUNKS_PLACEHOLDER".to_string(),
        (lifted_layout.size / DIGEST_LEN).to_string(),
    );
    replacements.insert(
        "LIFTED_APPLICATION_DIGEST_OFFSET_PLACEHOLDER".to_string(),
        lifted_layout.application_digest_offset.to_string(),
    );
    compile_recursive_entry("binary_node.py", lifted_child_bytecode, replacements)
}

pub fn lift_execution_proof(
    child_bytecode: &Bytecode,
    lifted_bytecode: &Bytecode,
    application_digest: &[F; PUBLIC_INPUT_LEN],
    child_proof: &ExecutionProof,
    log_inv_rate: usize,
) -> Result<LiftedExecutionProof, AggregationError> {
    let verified = verify_child(child_bytecode, application_digest, child_proof)?;
    let reduction =
        reduce_evaluations_for_bytecode(child_bytecode, std::slice::from_ref(&verified.bytecode_evaluation));
    let info = LiftedExecutionInfo {
        application_digest: *application_digest,
        child_bytecode_claim: reduction.final_claim.clone(),
    };
    let info_data = lifted_info_data(child_bytecode, &info, None)?;
    let public_input = poseidon_hash_slice(&info_data);
    let mut hints = recursion_hints(lifted_bytecode, &[verified], &reduction);
    hints.insert(
        lifted_bytecode,
        "leaf_info",
        arena_vec![ArenaVec::from_slice(&info_data)],
    );
    let witness = ExecutionWitness {
        preamble_memory_len: RECURSIVE_VERIFIER_PREAMBLE_MEMORY_LEN,
        hints,
        min_table_log_n_rows: BTreeMap::new(),
    };
    let proof = prove_execution(
        lifted_bytecode,
        &public_input,
        &witness,
        &default_whir_config(log_inv_rate),
        false,
    )?;
    Ok(LiftedExecutionProof { info, proof })
}

pub fn verify_lifted_execution_proof(
    child_bytecode: &Bytecode,
    lifted_bytecode: &Bytecode,
    lifted: &LiftedExecutionProof,
) -> Result<InnerVerified, ProofError> {
    let info_data = lifted_info_data(child_bytecode, &lifted.info, None)?;
    let public_input = poseidon_hash_slice(&info_data);
    let (verification, raw_proof) = verify_execution(lifted_bytecode, &public_input, lifted.proof.proof.clone())?;
    Ok(InnerVerified {
        input_data: info_data,
        input_data_hash: public_input,
        bytecode_evaluation: verification.bytecode_evaluation,
        raw_proof,
        sorted_table_perm: verification.sorted_table_perm,
    })
}

pub fn prove_binary_node(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    node_bytecode: &Bytecode,
    children: [&LiftedExecutionProof; 2],
    log_inv_rate: usize,
) -> Result<BinaryNodeProof, AggregationError> {
    let verified = children
        .iter()
        .map(|child| verify_lifted_execution_proof(child_bytecode, lifted_child_bytecode, child))
        .collect::<Result<Vec<_>, _>>()?;
    let claims = verified
        .iter()
        .map(|child| child.bytecode_evaluation.clone())
        .collect::<Vec<_>>();
    let reduction = reduce_evaluations_for_bytecode(lifted_child_bytecode, &claims);
    let original_claims = children
        .iter()
        .map(|child| child.info.child_bytecode_claim.clone())
        .collect::<Vec<_>>();
    let original_reduction = reduce_evaluations_for_bytecode_with_cap(
        child_bytecode,
        &original_claims,
        original_bytecode_reduction_cap(child_bytecode),
    );
    let application_root = binary_application_root(
        &children[0].info.application_digest,
        &children[1].info.application_digest,
    );
    let info = BinaryNodeInfo {
        original_bytecode_claim: original_reduction.final_claim.clone(),
        application_root,
        child_bytecode_claim: reduction.final_claim.clone(),
    };
    let info_data = binary_node_info_data(child_bytecode, lifted_child_bytecode, &info, None)?;
    let public_input = poseidon_hash_slice(&info_data);
    let mut hints = recursion_hints(node_bytecode, &verified, &reduction);
    hints.insert(
        node_bytecode,
        "original_bytecode_sumcheck_proof",
        arena_vec![ArenaVec::from_slice(&original_reduction.sumcheck_transcript)],
    );
    hints.insert(node_bytecode, "node_info", arena_vec![ArenaVec::from_slice(&info_data)]);
    hints.insert(
        node_bytecode,
        "lifted_info",
        children
            .iter()
            .map(|child| lifted_info_data(child_bytecode, &child.info, None).map(|data| ArenaVec::from_slice(&data)))
            .collect::<Result<ArenaVec<_>, _>>()?,
    );
    let witness = ExecutionWitness {
        preamble_memory_len: RECURSIVE_VERIFIER_PREAMBLE_MEMORY_LEN,
        hints,
        min_table_log_n_rows: BTreeMap::new(),
    };
    let proof = prove_execution(
        node_bytecode,
        &public_input,
        &witness,
        &default_whir_config(log_inv_rate),
        false,
    )?;
    Ok(BinaryNodeProof { info, proof })
}

pub fn verify_binary_node(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    node_bytecode: &Bytecode,
    node: &BinaryNodeProof,
) -> Result<InnerVerified, ProofError> {
    let info_data = binary_node_info_data(child_bytecode, lifted_child_bytecode, &node.info, None)?;
    let public_input = poseidon_hash_slice(&info_data);
    let (verification, raw_proof) = verify_execution(node_bytecode, &public_input, node.proof.proof.clone())?;
    Ok(InnerVerified {
        input_data: info_data,
        input_data_hash: public_input,
        bytecode_evaluation: verification.bytecode_evaluation,
        raw_proof,
        sorted_table_perm: verification.sorted_table_perm,
    })
}

pub fn binary_application_root(left: &[F; PUBLIC_INPUT_LEN], right: &[F; PUBLIC_INPUT_LEN]) -> [F; PUBLIC_INPUT_LEN] {
    let mut preimage = Vec::with_capacity(3 * DIGEST_LEN);
    preimage.push(F::from_u32(BINARY_NODE_INFO_DOMAIN));
    preimage.push(F::from_usize(2));
    preimage.resize(DIGEST_LEN, F::ZERO);
    preimage.extend_from_slice(left);
    preimage.extend_from_slice(right);
    poseidon_hash_slice(&preimage)
}

fn verify_child(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    proof: &ExecutionProof,
) -> Result<InnerVerified, ProofError> {
    let (verification, raw_proof) = verify_execution(bytecode, public_input, proof.proof.clone())?;
    Ok(InnerVerified {
        input_data: Vec::new(),
        input_data_hash: *public_input,
        bytecode_evaluation: verification.bytecode_evaluation,
        raw_proof,
        sorted_table_perm: verification.sorted_table_perm,
    })
}

fn lifted_info_data(
    child_bytecode: &Bytecode,
    info: &LiftedExecutionInfo,
    profile: Option<&WhirExecutionProfile>,
) -> Result<Vec<F>, ProofError> {
    require_valid_claim(child_bytecode, &info.child_bytecode_claim)?;
    let layout = LiftedInfoLayout::for_child(child_bytecode);
    let mut data = Vec::with_capacity(layout.size);
    data.push(F::from_u32(LIFTED_INFO_DOMAIN));
    data.push(F::ONE);
    data.resize(DIGEST_LEN, F::ZERO);
    debug_assert_eq!(data.len(), layout.claim_offset);
    data.extend(flatten_bytecode_claim(&info.child_bytecode_claim));
    data.resize(layout.claim_offset + layout.claim_size_padded, F::ZERO);
    debug_assert_eq!(data.len(), layout.cap_offset);
    data.extend_from_slice(&profile.map_or_else(
        || fiat_shamir_domain_sep(child_bytecode),
        |profile| profile.fiat_shamir_domain_sep(child_bytecode),
    ));
    debug_assert_eq!(data.len(), layout.application_digest_offset);
    data.extend_from_slice(&info.application_digest);
    debug_assert_eq!(data.len(), layout.size);
    Ok(data)
}

fn binary_node_info_data(
    original_bytecode: &Bytecode,
    child_bytecode: &Bytecode,
    info: &BinaryNodeInfo,
    profile: Option<&WhirExecutionProfile>,
) -> Result<Vec<F>, ProofError> {
    require_valid_claim(child_bytecode, &info.child_bytecode_claim)?;
    require_valid_claim(original_bytecode, &info.original_bytecode_claim)?;
    let layout = NodeInfoLayout::for_children(original_bytecode, child_bytecode);
    let mut data = Vec::with_capacity(layout.size);
    data.push(F::from_u32(BINARY_NODE_INFO_DOMAIN));
    data.push(F::from_usize(2));
    data.resize(DIGEST_LEN, F::ZERO);
    debug_assert_eq!(data.len(), layout.claim_offset);
    data.extend(flatten_bytecode_claim(&info.child_bytecode_claim));
    data.resize(layout.claim_offset + layout.claim_size_padded, F::ZERO);
    debug_assert_eq!(data.len(), layout.cap_offset);
    data.extend_from_slice(&profile.map_or_else(
        || fiat_shamir_domain_sep(child_bytecode),
        |profile| profile.fiat_shamir_domain_sep(child_bytecode),
    ));
    debug_assert_eq!(data.len(), layout.original_claim_offset);
    data.extend(flatten_bytecode_claim(&info.original_bytecode_claim));
    data.resize(
        layout.original_claim_offset + layout.original_claim_size_padded,
        F::ZERO,
    );
    debug_assert_eq!(data.len(), layout.application_root_offset);
    data.extend_from_slice(&info.application_root);
    debug_assert_eq!(data.len(), layout.size);
    Ok(data)
}

fn require_valid_claim(bytecode: &Bytecode, claim: &Evaluation<EF>) -> Result<(), ProofError> {
    if claim.point.len() != bytecode.cumulated_n_vars()
        || claim.value != compute_bytecode_value_at_for(bytecode, &claim.point)
    {
        return Err(ProofError::InvalidProof);
    }
    Ok(())
}

fn recursion_hints(bytecode: &Bytecode, verified: &[InnerVerified], reduction: &ReducedBytecodeClaims) -> Hints {
    let mut hints = Hints::default();
    hints.insert(
        bytecode,
        "bytecode_value_hint",
        verified
            .iter()
            .map(|child| ArenaVec::from_slice(child.bytecode_evaluation.value.as_basis_coefficients_slice()))
            .collect(),
    );
    hints.insert(
        bytecode,
        "proof_transcript_size",
        verified
            .iter()
            .map(|child| arena_vec![F::from_usize(child.raw_proof.transcript.len())])
            .collect(),
    );
    hints.insert(
        bytecode,
        "proof_transcript",
        verified
            .iter()
            .map(|child| ArenaVec::from_slice(&child.raw_proof.transcript))
            .collect(),
    );
    if bytecode.has_hint("table_sort_perm") {
        hints.insert(
            bytecode,
            "table_sort_perm",
            verified
                .iter()
                .map(|child| {
                    child
                        .sorted_table_perm
                        .iter()
                        .map(|&index| F::from_usize(index))
                        .collect()
                })
                .collect(),
        );
    }
    let (merkle_leaf, merkle_path) = extract_merkle_hints(verified.iter().map(|child| &child.raw_proof));
    hints.insert(bytecode, "merkle_leaf", merkle_leaf);
    hints.insert(bytecode, "merkle_path", merkle_path);
    hints.insert(
        bytecode,
        "bytecode_sumcheck_proof",
        arena_vec![ArenaVec::from_slice(&reduction.sumcheck_transcript)],
    );
    hints
}

fn extract_merkle_hints<'a>(
    raw_proofs: impl IntoIterator<Item = &'a RawProof<F>>,
) -> (ArenaVec<ArenaVec<F>>, ArenaVec<ArenaVec<F>>) {
    raw_proofs
        .into_iter()
        .flat_map(|proof| proof.merkle_openings.iter())
        .map(|opening| {
            let leaf = ArenaVec::from_slice(&opening.leaf_data);
            let path = opening.path.iter().flat_map(|digest| digest.iter().copied()).collect();
            (leaf, path)
        })
        .unzip()
}

fn expected_child_cap_replacement(
    child_bytecode: &Bytecode,
    profile: Option<&WhirExecutionProfile>,
) -> BTreeMap<String, String> {
    let cap = profile.map_or_else(
        || fiat_shamir_domain_sep(child_bytecode),
        |profile| profile.fiat_shamir_domain_sep(child_bytecode),
    );
    let mut replacements = BTreeMap::new();
    replacements.insert(
        "EXPECTED_CHILD_CAP_PLACEHOLDER".to_string(),
        format!(
            "[{}]",
            cap.iter()
                .map(|value| value.as_canonical_u32().to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ),
    );
    replacements
}

pub fn compile_lifted_execution_bytecode_with_profile(
    child_bytecode: &Bytecode,
    child_profile: &WhirExecutionProfile,
) -> Bytecode {
    compile_lifted_execution_bytecode_with_options(child_bytecode, child_profile, &RecursiveVerifierOptions::default())
}

pub fn compile_lifted_execution_bytecode_with_options(
    child_bytecode: &Bytecode,
    child_profile: &WhirExecutionProfile,
    options: &RecursiveVerifierOptions,
) -> Bytecode {
    compile_recursive_entry_with_options(
        "lift_execution.py",
        child_bytecode,
        expected_child_cap_replacement(child_bytecode, Some(child_profile)),
        Some(child_profile),
        *options,
    )
}

/// Compile a lift restricted to one child stacked dimension, enforced by the guest.
pub fn compile_lifted_execution_bytecode_for_dimension_with_options(
    child_bytecode: &Bytecode,
    child_profile: &WhirExecutionProfile,
    options: &RecursiveVerifierOptions,
    child_num_variables: usize,
) -> Bytecode {
    compile_recursive_entry_for_dimension(
        "lift_execution.py",
        child_bytecode,
        expected_child_cap_replacement(child_bytecode, Some(child_profile)),
        Some(child_profile),
        *options,
        Some(child_num_variables),
    )
}

/// Compile a lift restricted to the exact dimensions of its child proof.
pub fn compile_lifted_execution_bytecode_for_fixed_shape_with_options(
    child_bytecode: &Bytecode,
    child_profile: &WhirExecutionProfile,
    options: &RecursiveVerifierOptions,
    child_shape: &RecursiveChildShape,
) -> Bytecode {
    compile_recursive_entry_for_fixed_shape(
        "lift_execution.py",
        child_bytecode,
        expected_child_cap_replacement(child_bytecode, Some(child_profile)),
        child_profile,
        *options,
        child_shape,
    )
}

pub fn compile_binary_node_bytecode_with_profile(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    lift_profile: &WhirExecutionProfile,
) -> Bytecode {
    compile_binary_node_bytecode_with_options(
        child_bytecode,
        lifted_child_bytecode,
        lift_profile,
        &RecursiveVerifierOptions::default(),
    )
}

pub fn compile_binary_node_bytecode_with_options(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    lift_profile: &WhirExecutionProfile,
    options: &RecursiveVerifierOptions,
) -> Bytecode {
    compile_binary_node_with_dimension(
        child_bytecode,
        lifted_child_bytecode,
        lift_profile,
        options,
        None,
        None,
        false,
    )
}

/// Compile a binary verifier whose two lifted children must have the specified
/// stacked dimension. The restriction is enforced by the generated bytecode.
pub fn compile_binary_node_bytecode_for_dimension_with_options(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    lift_profile: &WhirExecutionProfile,
    options: &RecursiveVerifierOptions,
    child_num_variables: usize,
) -> Bytecode {
    compile_binary_node_with_dimension(
        child_bytecode,
        lifted_child_bytecode,
        lift_profile,
        options,
        Some(child_num_variables),
        None,
        false,
    )
}

/// Compile a binary verifier restricted to the exact dimensions of both child proofs.
pub fn compile_binary_node_bytecode_for_fixed_shape_with_options(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    lift_profile: &WhirExecutionProfile,
    options: &RecursiveVerifierOptions,
    child_shape: &RecursiveChildShape,
) -> Bytecode {
    compile_binary_node_with_dimension(
        child_bytecode,
        lifted_child_bytecode,
        lift_profile,
        options,
        None,
        Some(child_shape),
        false,
    )
}

/// Compile a terminal node whose full metadata is authenticated by a public memory opening.
pub fn compile_terminal_binary_node_bytecode_with_options(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    lift_profile: &WhirExecutionProfile,
    options: &RecursiveVerifierOptions,
) -> Bytecode {
    compile_binary_node_with_dimension(
        child_bytecode,
        lifted_child_bytecode,
        lift_profile,
        options,
        None,
        None,
        true,
    )
}

pub fn compile_terminal_binary_node_bytecode_for_dimension_with_options(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    lift_profile: &WhirExecutionProfile,
    options: &RecursiveVerifierOptions,
    child_num_variables: usize,
) -> Bytecode {
    compile_binary_node_with_dimension(
        child_bytecode,
        lifted_child_bytecode,
        lift_profile,
        options,
        Some(child_num_variables),
        None,
        true,
    )
}

pub fn compile_terminal_binary_node_bytecode_for_fixed_shape_with_options(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    lift_profile: &WhirExecutionProfile,
    options: &RecursiveVerifierOptions,
    child_shape: &RecursiveChildShape,
) -> Bytecode {
    compile_binary_node_with_dimension(
        child_bytecode,
        lifted_child_bytecode,
        lift_profile,
        options,
        None,
        Some(child_shape),
        true,
    )
}

fn compile_binary_node_with_dimension(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    lift_profile: &WhirExecutionProfile,
    options: &RecursiveVerifierOptions,
    child_num_variables: Option<usize>,
    child_shape: Option<&RecursiveChildShape>,
    terminal_public_memory: bool,
) -> Bytecode {
    assert!(
        child_num_variables.is_none() || child_shape.is_none(),
        "choose either a child dimension or an exact child shape"
    );
    let lifted_layout = LiftedInfoLayout::for_child(child_bytecode);
    let mut replacements = expected_child_cap_replacement(lifted_child_bytecode, Some(lift_profile));
    replacements.extend(original_bytecode_replacements(child_bytecode));
    replacements.insert(
        "LIFTED_INFO_SIZE_PLACEHOLDER".to_string(),
        lifted_layout.size.to_string(),
    );
    replacements.insert(
        "LIFTED_INFO_NUM_CHUNKS_PLACEHOLDER".to_string(),
        (lifted_layout.size / DIGEST_LEN).to_string(),
    );
    replacements.insert(
        "LIFTED_APPLICATION_DIGEST_OFFSET_PLACEHOLDER".to_string(),
        lifted_layout.application_digest_offset.to_string(),
    );
    if terminal_public_memory {
        assert_eq!(
            NodeInfoLayout::for_children(child_bytecode, lifted_child_bytecode).size,
            TERMINAL_NODE_INFO_SIZE,
            "terminal node metadata must contain exactly 256 field elements"
        );
        replacements.insert(
            "NODE_INFO_ALLOCATION_PLACEHOLDER".to_string(),
            "terminal_node_info_address()".to_string(),
        );
        // Keep the pointer as a variable for hint_witness while the return equation fixes its value.
        replacements.insert(
            "NODE_INFO_ADDRESS_FUNCTION_PLACEHOLDER".to_string(),
            format!("def terminal_node_info_address():\n    return {TERMINAL_NODE_INFO_ADDRESS}\n"),
        );
        replacements.insert(
            "NODE_INFO_PUBLIC_OUTPUT_PLACEHOLDER".to_string(),
            "copy_8(computed_root, pub_mem)".to_string(),
        );
    }
    if let Some(child_shape) = child_shape {
        compile_recursive_entry_for_fixed_shape(
            "binary_node.py",
            lifted_child_bytecode,
            replacements,
            lift_profile,
            *options,
            child_shape,
        )
    } else {
        compile_recursive_entry_for_dimension(
            "binary_node.py",
            lifted_child_bytecode,
            replacements,
            Some(lift_profile),
            *options,
            child_num_variables,
        )
    }
}

pub fn lift_execution_proof_with_profiles(
    child_bytecode: &Bytecode,
    lifted_bytecode: &Bytecode,
    application_digest: &[F; PUBLIC_INPUT_LEN],
    child_proof: &ExecutionProof,
    child_profile: &WhirExecutionProfile,
    lift_profile: &WhirExecutionProfile,
    vm_profiler: bool,
) -> Result<LiftedExecutionProof, AggregationError> {
    let verified = verify_child_with_profile(child_bytecode, application_digest, child_proof, child_profile)?;
    let reduction = reduce_evaluations_for_bytecode_with_cap(
        child_bytecode,
        std::slice::from_ref(&verified.bytecode_evaluation),
        child_profile.fiat_shamir_domain_sep(child_bytecode),
    );
    let info = LiftedExecutionInfo {
        application_digest: *application_digest,
        child_bytecode_claim: reduction.final_claim.clone(),
    };
    let info_data = lifted_info_data(child_bytecode, &info, Some(child_profile))?;
    let public_input = poseidon_hash_slice(&info_data);
    let mut hints = recursion_hints(lifted_bytecode, &[verified], &reduction);
    hints.insert(
        lifted_bytecode,
        "leaf_info",
        arena_vec![ArenaVec::from_slice(&info_data)],
    );
    let witness = ExecutionWitness {
        preamble_memory_len: RECURSIVE_VERIFIER_PREAMBLE_MEMORY_LEN,
        hints,
        min_table_log_n_rows: BTreeMap::new(),
    };
    let proof = prove_execution_with_profile(lifted_bytecode, &public_input, &witness, lift_profile, vm_profiler)?;
    Ok(LiftedExecutionProof { info, proof })
}

pub fn verify_lifted_execution_proof_with_profiles(
    child_bytecode: &Bytecode,
    lifted_bytecode: &Bytecode,
    lifted: &LiftedExecutionProof,
    child_profile: &WhirExecutionProfile,
    lift_profile: &WhirExecutionProfile,
) -> Result<InnerVerified, ProofError> {
    child_profile.validate().map_err(|_| ProofError::InvalidProof)?;
    let info_data = lifted_info_data(child_bytecode, &lifted.info, Some(child_profile))?;
    let public_input = poseidon_hash_slice(&info_data);
    let (verification, raw_proof) =
        verify_execution_with_profile(lifted_bytecode, &public_input, lifted.proof.proof.clone(), lift_profile)?;
    Ok(InnerVerified {
        input_data: info_data,
        input_data_hash: public_input,
        bytecode_evaluation: verification.bytecode_evaluation,
        raw_proof,
        sorted_table_perm: verification.sorted_table_perm,
    })
}

#[allow(clippy::too_many_arguments)]
pub fn prove_binary_node_with_profiles(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    node_bytecode: &Bytecode,
    children: [&LiftedExecutionProof; 2],
    child_profile: &WhirExecutionProfile,
    lift_profile: &WhirExecutionProfile,
    node_profile: &WhirExecutionProfile,
    vm_profiler: bool,
) -> Result<BinaryNodeProof, AggregationError> {
    prove_binary_node_with_profiles_and_hash(
        child_bytecode,
        lifted_child_bytecode,
        node_bytecode,
        children,
        child_profile,
        lift_profile,
        node_profile,
        ProofHashProfile::Poseidon1,
        vm_profiler,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn prove_binary_node_with_profiles_and_hash(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    node_bytecode: &Bytecode,
    children: [&LiftedExecutionProof; 2],
    child_profile: &WhirExecutionProfile,
    lift_profile: &WhirExecutionProfile,
    node_profile: &WhirExecutionProfile,
    hash_profile: ProofHashProfile,
    vm_profiler: bool,
) -> Result<BinaryNodeProof, AggregationError> {
    let (info, public_input, witness) = prepare_binary_node_with_profiles(
        child_bytecode,
        lifted_child_bytecode,
        node_bytecode,
        children,
        child_profile,
        lift_profile,
    )?;
    let proof = prove_execution_with_profile_and_hash(
        node_bytecode,
        &public_input,
        &witness,
        node_profile,
        hash_profile,
        vm_profiler,
    )?;
    Ok(BinaryNodeProof { info, proof })
}

/// Prepare the fixed binary-node witness, including both independently reduced bytecode claims.
pub fn prepare_binary_node_with_profiles(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    node_bytecode: &Bytecode,
    children: [&LiftedExecutionProof; 2],
    child_profile: &WhirExecutionProfile,
    lift_profile: &WhirExecutionProfile,
) -> Result<(BinaryNodeInfo, [F; PUBLIC_INPUT_LEN], ExecutionWitness), AggregationError> {
    prepare_binary_node_with_public_memory_mode(
        child_bytecode,
        lifted_child_bytecode,
        node_bytecode,
        children,
        child_profile,
        lift_profile,
        false,
    )
}

/// Prepare a terminal node with metadata at the fixed public memory address.
pub fn prepare_terminal_binary_node_with_profiles(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    node_bytecode: &Bytecode,
    children: [&LiftedExecutionProof; 2],
    child_profile: &WhirExecutionProfile,
    lift_profile: &WhirExecutionProfile,
) -> Result<(BinaryNodeInfo, [F; PUBLIC_INPUT_LEN], ExecutionWitness), AggregationError> {
    prepare_binary_node_with_public_memory_mode(
        child_bytecode,
        lifted_child_bytecode,
        node_bytecode,
        children,
        child_profile,
        lift_profile,
        true,
    )
}

fn prepare_binary_node_with_public_memory_mode(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    node_bytecode: &Bytecode,
    children: [&LiftedExecutionProof; 2],
    child_profile: &WhirExecutionProfile,
    lift_profile: &WhirExecutionProfile,
    terminal_public_memory: bool,
) -> Result<(BinaryNodeInfo, [F; PUBLIC_INPUT_LEN], ExecutionWitness), AggregationError> {
    let verified = children
        .iter()
        .map(|child| {
            verify_lifted_execution_proof_with_profiles(
                child_bytecode,
                lifted_child_bytecode,
                child,
                child_profile,
                lift_profile,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let claims = verified
        .iter()
        .map(|child| child.bytecode_evaluation.clone())
        .collect::<Vec<_>>();
    let reduction = reduce_evaluations_for_bytecode_with_cap(
        lifted_child_bytecode,
        &claims,
        lift_profile.fiat_shamir_domain_sep(lifted_child_bytecode),
    );
    let original_claims = children
        .iter()
        .map(|child| child.info.child_bytecode_claim.clone())
        .collect::<Vec<_>>();
    let original_reduction = reduce_evaluations_for_bytecode_with_cap(
        child_bytecode,
        &original_claims,
        original_bytecode_reduction_cap(child_bytecode),
    );
    let application_root = binary_application_root(
        &children[0].info.application_digest,
        &children[1].info.application_digest,
    );
    let info = BinaryNodeInfo {
        original_bytecode_claim: original_reduction.final_claim.clone(),
        application_root,
        child_bytecode_claim: reduction.final_claim.clone(),
    };
    let info_data = binary_node_info_data(child_bytecode, lifted_child_bytecode, &info, Some(lift_profile))?;
    let public_input = if terminal_public_memory {
        if info_data.len() != TERMINAL_NODE_INFO_SIZE {
            return Err(ProofError::InvalidProof.into());
        }
        info.application_root
    } else {
        poseidon_hash_slice(&info_data)
    };
    let mut hints = recursion_hints(node_bytecode, &verified, &reduction);
    hints.insert(
        node_bytecode,
        "original_bytecode_sumcheck_proof",
        arena_vec![ArenaVec::from_slice(&original_reduction.sumcheck_transcript)],
    );
    hints.insert(node_bytecode, "node_info", arena_vec![ArenaVec::from_slice(&info_data)]);
    hints.insert(
        node_bytecode,
        "lifted_info",
        children
            .iter()
            .map(|child| {
                lifted_info_data(child_bytecode, &child.info, Some(child_profile))
                    .map(|data| ArenaVec::from_slice(&data))
            })
            .collect::<Result<ArenaVec<_>, _>>()?,
    );
    let witness = ExecutionWitness {
        preamble_memory_len: if terminal_public_memory {
            TERMINAL_NODE_PREAMBLE_MEMORY_LEN
        } else {
            RECURSIVE_VERIFIER_PREAMBLE_MEMORY_LEN
        },
        hints,
        min_table_log_n_rows: BTreeMap::new(),
    };
    Ok((info, public_input, witness))
}

/// Reconstruct the authenticated terminal metadata from typed public claims.
pub fn terminal_binary_node_public_memory(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    info: &BinaryNodeInfo,
    lift_profile: &WhirExecutionProfile,
) -> Result<PublicMemoryRegion, ProofError> {
    lift_profile.validate().map_err(|_| ProofError::InvalidProof)?;
    let values = binary_node_info_data(child_bytecode, lifted_child_bytecode, info, Some(lift_profile))?;
    if values.len() != TERMINAL_NODE_INFO_SIZE {
        return Err(ProofError::InvalidProof);
    }
    Ok(PublicMemoryRegion {
        start: TERMINAL_NODE_INFO_ADDRESS,
        values,
    })
}

/// Build the fixed-program polynomial and its application-pinned Keccak240
/// commitment for a terminal C1 proof.
pub fn terminal_c1_fixed_programs(
    spark_bytecode: &Bytecode,
    lift_bytecode: &Bytecode,
    root_bytecode: &Bytecode,
    profile: &WhirExecutionProfile,
) -> Result<TerminalC1FixedPrograms, ProofError> {
    terminal_c1_fixed_programs_from_slices(
        spark_bytecode.instructions_multilinear(),
        lift_bytecode.instructions_multilinear(),
        root_bytecode.instructions_multilinear(),
        profile,
    )
}

/// Build the fixed-program polynomial with trailing zeros up to the selected
/// execution dimension. The verifier must use the same dimension and root.
pub fn terminal_c1_fixed_programs_for_dimension(
    spark_bytecode: &Bytecode,
    lift_bytecode: &Bytecode,
    root_bytecode: &Bytecode,
    profile: &WhirExecutionProfile,
    num_variables: usize,
) -> Result<TerminalC1FixedPrograms, ProofError> {
    terminal_c1_fixed_programs_from_slices_for_dimension(
        spark_bytecode.instructions_multilinear(),
        lift_bytecode.instructions_multilinear(),
        root_bytecode.instructions_multilinear(),
        profile,
        num_variables,
    )
}

fn terminal_c1_fixed_programs_from_slices(
    spark: &[F],
    lift: &[F],
    root: &[F],
    profile: &WhirExecutionProfile,
) -> Result<TerminalC1FixedPrograms, ProofError> {
    let num_variables = spark.len().checked_ilog2().ok_or(ProofError::InvalidProof)? as usize + 1;
    terminal_c1_fixed_programs_from_slices_for_dimension(spark, lift, root, profile, num_variables)
}

fn terminal_c1_fixed_programs_from_slices_for_dimension(
    spark: &[F],
    lift: &[F],
    root: &[F],
    profile: &WhirExecutionProfile,
    num_variables: usize,
) -> Result<TerminalC1FixedPrograms, ProofError> {
    if !spark.len().is_power_of_two() || !lift.len().is_power_of_two() || !root.len().is_power_of_two() {
        return Err(ProofError::InvalidProof);
    }
    let program_dimensions = [
        spark.len().ilog2() as usize,
        lift.len().ilog2() as usize,
        root.len().ilog2() as usize,
    ];
    terminal_c1_program_prefixes(program_dimensions, num_variables)?;
    profile
        .validate_for_hash(ProofHashProfile::Keccak240)
        .map_err(|_| ProofError::InvalidProof)?;
    profile
        .validate_for_n_vars(num_variables)
        .map_err(|_| ProofError::InvalidProof)?;

    let actual_data_len = spark.len() + lift.len() + root.len();
    let mut evaluations = F::zero_vec(1usize << num_variables);
    let mut offset = 0;
    for program in [spark, lift, root] {
        evaluations[offset..offset + program.len()].copy_from_slice(program);
        offset += program.len();
    }
    let polynomial = MleOwned::Base(ArenaVec::from_slice(&evaluations));
    let whir_config = WhirConfig::<EF>::new(&profile.whir_config(), num_variables);

    Ok(TerminalC1FixedPrograms {
        program_dimensions,
        num_variables,
        actual_data_len,
        polynomial,
        whir_config,
    })
}

/// Produce the version-one terminal C1 proof. Its execution trace and the
/// `[spark | lift | root]` fixed-program polynomial share one WHIR continuation.
#[allow(clippy::too_many_arguments)]
pub fn prove_terminal_binary_node_c1_v1_with_profiles(
    spark_bytecode: &Bytecode,
    lift_bytecode: &Bytecode,
    root_bytecode: &Bytecode,
    children: [&LiftedExecutionProof; 2],
    child_profile: &WhirExecutionProfile,
    lift_profile: &WhirExecutionProfile,
    root_profile: &WhirExecutionProfile,
    vm_profiler: bool,
) -> Result<BinaryNodeProof, AggregationError> {
    let fixed_programs = terminal_c1_fixed_programs(spark_bytecode, lift_bytecode, root_bytecode, root_profile)?;
    let secondary_commitment = fixed_programs.preprocess_keccak240();
    prove_terminal_binary_node_c1_v1_with_preprocessing(
        spark_bytecode,
        lift_bytecode,
        root_bytecode,
        children,
        child_profile,
        lift_profile,
        root_profile,
        fixed_programs,
        secondary_commitment,
        vm_profiler,
    )
}

/// Produce a terminal C1 proof using fixed-program Merkle data prepared before
/// this call.
#[allow(clippy::too_many_arguments)]
pub fn prove_terminal_binary_node_c1_v1_with_preprocessing(
    spark_bytecode: &Bytecode,
    lift_bytecode: &Bytecode,
    root_bytecode: &Bytecode,
    children: [&LiftedExecutionProof; 2],
    child_profile: &WhirExecutionProfile,
    lift_profile: &WhirExecutionProfile,
    root_profile: &WhirExecutionProfile,
    fixed_programs: TerminalC1FixedPrograms,
    secondary_commitment: TwoCommitmentWhirPreprocessedCommitment,
    vm_profiler: bool,
) -> Result<BinaryNodeProof, AggregationError> {
    prove_terminal_binary_node_fixed_programs_inner(
        spark_bytecode,
        lift_bytecode,
        root_bytecode,
        children,
        child_profile,
        lift_profile,
        root_profile,
        fixed_programs,
        secondary_commitment,
        vm_profiler,
        false,
    )
}

/// Experimental grouped LogUp terminal mode with shared three-commitment WHIR.
#[allow(clippy::too_many_arguments)]
pub fn prove_terminal_binary_node_grouped_logup_with_preprocessing(
    spark_bytecode: &Bytecode,
    lift_bytecode: &Bytecode,
    root_bytecode: &Bytecode,
    children: [&LiftedExecutionProof; 2],
    child_profile: &WhirExecutionProfile,
    lift_profile: &WhirExecutionProfile,
    root_profile: &WhirExecutionProfile,
    fixed_programs: TerminalC1FixedPrograms,
    secondary_commitment: TwoCommitmentWhirPreprocessedCommitment,
    vm_profiler: bool,
) -> Result<BinaryNodeProof, AggregationError> {
    prove_terminal_binary_node_fixed_programs_inner(
        spark_bytecode,
        lift_bytecode,
        root_bytecode,
        children,
        child_profile,
        lift_profile,
        root_profile,
        fixed_programs,
        secondary_commitment,
        vm_profiler,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_terminal_binary_node_fixed_programs_inner(
    spark_bytecode: &Bytecode,
    lift_bytecode: &Bytecode,
    root_bytecode: &Bytecode,
    children: [&LiftedExecutionProof; 2],
    child_profile: &WhirExecutionProfile,
    lift_profile: &WhirExecutionProfile,
    root_profile: &WhirExecutionProfile,
    fixed_programs: TerminalC1FixedPrograms,
    secondary_commitment: TwoCommitmentWhirPreprocessedCommitment,
    vm_profiler: bool,
    grouped_logup: bool,
) -> Result<BinaryNodeProof, AggregationError> {
    let prove_execution = if grouped_logup {
        lean_prover::prove_execution::prove_execution_with_grouped_logup
    } else {
        prove_execution_with_two_commitment_whir
    };
    let expected_dimensions = [
        spark_bytecode.cumulated_n_vars(),
        lift_bytecode.cumulated_n_vars(),
        root_bytecode.cumulated_n_vars(),
    ];
    if fixed_programs.program_dimensions != expected_dimensions {
        return Err(ProofError::InvalidProof.into());
    }
    let (info, public_input, witness) = prepare_terminal_binary_node_with_profiles(
        spark_bytecode,
        lift_bytecode,
        root_bytecode,
        children,
        child_profile,
        lift_profile,
    )?;
    let region = terminal_binary_node_public_memory(spark_bytecode, lift_bytecode, &info, lift_profile)?;
    let secondary_statements = fixed_programs.public_statements(&info)?;
    let input = TwoCommitmentWhirProverInput {
        secondary_polynomial: fixed_programs.polynomial,
        secondary_actual_data_len: fixed_programs.actual_data_len,
        secondary_commitment,
        secondary_statements,
        secondary_statement_public_memory_bindings: terminal_c1_statement_public_memory_bindings_for_dimension(
            spark_bytecode,
            lift_bytecode,
            fixed_programs.num_variables,
        )?
        .to_vec(),
        execution_bytecode_point_prefix: terminal_c1_execution_program_prefix(
            root_bytecode,
            fixed_programs.num_variables,
        )?,
        two_commitment_batching_pow_bits: TERMINAL_C1_TWO_COMMITMENT_BATCHING_POW_BITS,
    };
    let proof = prove_execution(
        root_bytecode,
        &public_input,
        &witness,
        root_profile,
        ProofHashProfile::Keccak240,
        Some(&region),
        input,
        vm_profiler,
    )?;
    Ok(BinaryNodeProof { info, proof })
}

/// Verify the version-one terminal C1 proof against the fixed-program root
/// derived from the three application-selected bytecodes.
pub fn verify_terminal_binary_node_c1_v1_with_profiles(
    spark_bytecode: &Bytecode,
    lift_bytecode: &Bytecode,
    root_bytecode: &Bytecode,
    node: &BinaryNodeProof,
    lift_profile: &WhirExecutionProfile,
    root_profile: &WhirExecutionProfile,
) -> Result<InnerVerified, ProofError> {
    let fixed_programs = terminal_c1_fixed_programs(spark_bytecode, lift_bytecode, root_bytecode, root_profile)?;
    let preprocessing = fixed_programs.verifier_preprocessing();
    verify_terminal_binary_node_c1_v1_with_preprocessing(
        spark_bytecode,
        lift_bytecode,
        root_bytecode,
        node,
        lift_profile,
        root_profile,
        &preprocessing,
    )
}

/// Verify a terminal C1 proof with an application-precomputed fixed-program
/// root. Building the fixed polynomial and Merkle tree is outside this call.
#[allow(clippy::too_many_arguments)]
pub fn verify_terminal_binary_node_c1_v1_with_preprocessing(
    spark_bytecode: &Bytecode,
    lift_bytecode: &Bytecode,
    root_bytecode: &Bytecode,
    node: &BinaryNodeProof,
    lift_profile: &WhirExecutionProfile,
    root_profile: &WhirExecutionProfile,
    preprocessing: &TerminalC1VerifierPreprocessing,
) -> Result<InnerVerified, ProofError> {
    verify_terminal_binary_node_fixed_programs_inner(
        spark_bytecode,
        lift_bytecode,
        root_bytecode,
        node,
        lift_profile,
        root_profile,
        preprocessing,
        false,
    )
}

/// Experimental grouped LogUp terminal mode with shared three-commitment WHIR.
#[allow(clippy::too_many_arguments)]
pub fn verify_terminal_binary_node_grouped_logup_with_preprocessing(
    spark_bytecode: &Bytecode,
    lift_bytecode: &Bytecode,
    root_bytecode: &Bytecode,
    node: &BinaryNodeProof,
    lift_profile: &WhirExecutionProfile,
    root_profile: &WhirExecutionProfile,
    preprocessing: &TerminalC1VerifierPreprocessing,
) -> Result<InnerVerified, ProofError> {
    verify_terminal_binary_node_fixed_programs_inner(
        spark_bytecode,
        lift_bytecode,
        root_bytecode,
        node,
        lift_profile,
        root_profile,
        preprocessing,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn verify_terminal_binary_node_fixed_programs_inner(
    spark_bytecode: &Bytecode,
    lift_bytecode: &Bytecode,
    root_bytecode: &Bytecode,
    node: &BinaryNodeProof,
    lift_profile: &WhirExecutionProfile,
    root_profile: &WhirExecutionProfile,
    preprocessing: &TerminalC1VerifierPreprocessing,
    grouped_logup: bool,
) -> Result<InnerVerified, ProofError> {
    let verify_execution = if grouped_logup {
        lean_prover::verify_execution::verify_execution_with_grouped_logup
    } else {
        verify_execution_with_two_commitment_whir
    };
    let expected_dimensions = [
        spark_bytecode.cumulated_n_vars(),
        lift_bytecode.cumulated_n_vars(),
        root_bytecode.cumulated_n_vars(),
    ];
    let minimum_num_variables = expected_dimensions[0] + 1;
    let expected_actual_data_len = u32::try_from(minimum_num_variables)
        .ok()
        .and_then(|shift| 1usize.checked_shl(shift));
    if expected_dimensions[1].checked_add(1) != Some(expected_dimensions[0])
        || expected_dimensions[1] != expected_dimensions[2]
        || preprocessing.program_dimensions != expected_dimensions
        || preprocessing.num_variables < minimum_num_variables
        || expected_actual_data_len != Some(preprocessing.actual_data_len)
    {
        return Err(ProofError::InvalidProof);
    }
    root_profile
        .validate_for_hash(ProofHashProfile::Keccak240)
        .map_err(|_| ProofError::InvalidProof)?;
    root_profile
        .validate_for_n_vars(preprocessing.num_variables)
        .map_err(|_| ProofError::InvalidProof)?;

    let region = terminal_binary_node_public_memory(spark_bytecode, lift_bytecode, &node.info, lift_profile)?;
    let secondary_statements = preprocessing.public_statements(&node.info)?;
    let input = TwoCommitmentWhirVerifierInput {
        secondary_num_variables: preprocessing.num_variables,
        secondary_actual_data_len: preprocessing.actual_data_len,
        expected_secondary_root: preprocessing.expected_keccak240_root,
        secondary_statements,
        secondary_statement_public_memory_bindings: terminal_c1_statement_public_memory_bindings_for_dimension(
            spark_bytecode,
            lift_bytecode,
            preprocessing.num_variables,
        )?
        .to_vec(),
        execution_bytecode_point_prefix: terminal_c1_execution_program_prefix(
            root_bytecode,
            preprocessing.num_variables,
        )?,
        two_commitment_batching_pow_bits: TERMINAL_C1_TWO_COMMITMENT_BATCHING_POW_BITS,
    };
    let public_input = node.info.application_root;
    let (verification, raw_proof) = verify_execution(
        root_bytecode,
        &public_input,
        node.proof.proof.clone(),
        root_profile,
        ProofHashProfile::Keccak240,
        Some(&region),
        input,
    )?;
    Ok(InnerVerified {
        input_data: region.values,
        input_data_hash: public_input,
        bytecode_evaluation: verification.bytecode_evaluation,
        raw_proof,
        sorted_table_perm: verification.sorted_table_perm,
    })
}

#[allow(clippy::too_many_arguments)]
pub fn prove_terminal_binary_node_with_profiles_and_hash(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    node_bytecode: &Bytecode,
    children: [&LiftedExecutionProof; 2],
    child_profile: &WhirExecutionProfile,
    lift_profile: &WhirExecutionProfile,
    node_profile: &WhirExecutionProfile,
    hash_profile: ProofHashProfile,
    vm_profiler: bool,
) -> Result<BinaryNodeProof, AggregationError> {
    let (info, public_input, witness) = prepare_terminal_binary_node_with_profiles(
        child_bytecode,
        lifted_child_bytecode,
        node_bytecode,
        children,
        child_profile,
        lift_profile,
    )?;
    let region = terminal_binary_node_public_memory(child_bytecode, lifted_child_bytecode, &info, lift_profile)?;
    let proof = prove_execution_with_profile_hash_and_public_memory(
        node_bytecode,
        &public_input,
        &witness,
        node_profile,
        hash_profile,
        Some(&region),
        vm_profiler,
    )?;
    Ok(BinaryNodeProof { info, proof })
}

pub fn verify_terminal_binary_node_with_profiles_and_hash(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    node_bytecode: &Bytecode,
    node: &BinaryNodeProof,
    lift_profile: &WhirExecutionProfile,
    node_profile: &WhirExecutionProfile,
    hash_profile: ProofHashProfile,
) -> Result<InnerVerified, ProofError> {
    let region = terminal_binary_node_public_memory(child_bytecode, lifted_child_bytecode, &node.info, lift_profile)?;
    let public_input = node.info.application_root;
    let (verification, raw_proof) = verify_execution_with_profile_hash_and_public_memory(
        node_bytecode,
        &public_input,
        node.proof.proof.clone(),
        node_profile,
        hash_profile,
        Some(&region),
    )?;
    Ok(InnerVerified {
        input_data: region.values,
        input_data_hash: public_input,
        bytecode_evaluation: verification.bytecode_evaluation,
        raw_proof,
        sorted_table_perm: verification.sorted_table_perm,
    })
}

pub fn verify_binary_node_with_profiles(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    node_bytecode: &Bytecode,
    node: &BinaryNodeProof,
    lift_profile: &WhirExecutionProfile,
    node_profile: &WhirExecutionProfile,
) -> Result<InnerVerified, ProofError> {
    verify_binary_node_with_profiles_and_hash(
        child_bytecode,
        lifted_child_bytecode,
        node_bytecode,
        node,
        lift_profile,
        node_profile,
        ProofHashProfile::Poseidon1,
    )
}

pub fn verify_binary_node_with_profiles_and_hash(
    child_bytecode: &Bytecode,
    lifted_child_bytecode: &Bytecode,
    node_bytecode: &Bytecode,
    node: &BinaryNodeProof,
    lift_profile: &WhirExecutionProfile,
    node_profile: &WhirExecutionProfile,
    hash_profile: ProofHashProfile,
) -> Result<InnerVerified, ProofError> {
    lift_profile.validate().map_err(|_| ProofError::InvalidProof)?;
    let info_data = binary_node_info_data(child_bytecode, lifted_child_bytecode, &node.info, Some(lift_profile))?;
    let public_input = poseidon_hash_slice(&info_data);
    let (verification, raw_proof) = verify_execution_with_profile_and_hash(
        node_bytecode,
        &public_input,
        node.proof.proof.clone(),
        node_profile,
        hash_profile,
    )?;
    Ok(InnerVerified {
        input_data: info_data,
        input_data_hash: public_input,
        bytecode_evaluation: verification.bytecode_evaluation,
        raw_proof,
        sorted_table_perm: verification.sorted_table_perm,
    })
}

fn verify_child_with_profile(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    proof: &ExecutionProof,
    profile: &WhirExecutionProfile,
) -> Result<InnerVerified, ProofError> {
    let (verification, raw_proof) =
        verify_execution_with_profile(bytecode, public_input, proof.proof.clone(), profile)?;
    Ok(InnerVerified {
        input_data: Vec::new(),
        input_data_hash: *public_input,
        bytecode_evaluation: verification.bytecode_evaluation,
        raw_proof,
        sorted_table_perm: verification.sorted_table_perm,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::EvaluationsList;

    fn terminal_c1_test_profile() -> WhirExecutionProfile {
        WhirExecutionProfile {
            security_bits: 32,
            grinding_bits: 8,
            first_folding_factor: 4,
            subsequent_folding_factor: 3,
            rs_domain_initial_reduction_factor: 2,
            max_num_variables_to_send_coeffs: 3,
            log_inv_rate: 1,
        }
    }

    fn patterned_program(len: usize, multiplier: usize, addend: usize) -> Vec<F> {
        (0..len)
            .map(|index| F::from_usize(index * multiplier + addend))
            .collect()
    }

    #[test]
    fn terminal_c1_fixed_program_layout_and_claim_prefixes() {
        let spark = patterned_program(1 << 12, 3, 1);
        let lift = patterned_program(1 << 11, 5, 2);
        let root = patterned_program(1 << 11, 7, 4);
        let fixed = terminal_c1_fixed_programs_from_slices(&spark, &lift, &root, &terminal_c1_test_profile()).unwrap();
        assert_eq!(fixed.program_dimensions, [12, 11, 11]);
        assert_eq!(fixed.num_variables, 13);
        assert_eq!(fixed.actual_data_len, 1 << 13);

        let spark_point = MultilinearPoint(vec![EF::from_usize(3); 12]);
        let lift_point = MultilinearPoint(vec![EF::from_usize(5); 11]);
        let root_point = MultilinearPoint(vec![EF::from_usize(7); 11]);
        let info = BinaryNodeInfo {
            original_bytecode_claim: Evaluation::new(spark_point.clone(), spark.evaluate_sequential(&spark_point)),
            application_root: [F::ZERO; PUBLIC_INPUT_LEN],
            child_bytecode_claim: Evaluation::new(lift_point.clone(), lift.evaluate_sequential(&lift_point)),
        };
        let statements = fixed.public_statements(&info).unwrap();
        assert_eq!(statements.len(), 2);
        assert_eq!(statements[0].point[0], EF::ZERO);
        assert_eq!(&statements[0].point[1..], spark_point.as_slice());
        assert_eq!(&statements[1].point[..2], &[EF::ONE, EF::ZERO]);
        assert_eq!(&statements[1].point[2..], lift_point.as_slice());
        for statement in &statements {
            assert_eq!(statement.total_num_variables, fixed.num_variables);
            assert_eq!(statement.values.len(), 1);
            assert_eq!(fixed.polynomial.evaluate(&statement.point), statement.values[0].value);
        }

        let mut combined_root_point = vec![EF::ONE, EF::ONE];
        combined_root_point.extend_from_slice(&root_point);
        assert_eq!(
            fixed.polynomial.evaluate(&MultilinearPoint(combined_root_point)),
            root.evaluate_sequential(&root_point),
        );
    }

    #[test]
    fn terminal_c1_zero_padding_preserves_program_claims_and_binds_capacity() {
        let profile = terminal_c1_test_profile();
        let spark = patterned_program(1 << 12, 3, 1);
        let lift = patterned_program(1 << 11, 5, 2);
        let root = patterned_program(1 << 11, 7, 4);
        let unpadded = terminal_c1_fixed_programs_from_slices(&spark, &lift, &root, &profile).unwrap();
        let unpadded_commitment = unpadded.preprocess_keccak240();
        let point = |dimension, coordinate| MultilinearPoint(vec![EF::from_usize(coordinate); dimension]);
        let spark_point = point(12, 3);
        let lift_point = point(11, 5);
        let root_point = point(11, 7);
        let info = BinaryNodeInfo {
            original_bytecode_claim: Evaluation::new(spark_point.clone(), spark.evaluate_sequential(&spark_point)),
            application_root: [F::ZERO; PUBLIC_INPUT_LEN],
            child_bytecode_claim: Evaluation::new(lift_point.clone(), lift.evaluate_sequential(&lift_point)),
        };
        for num_variables in [14, 15] {
            let fixed =
                terminal_c1_fixed_programs_from_slices_for_dimension(&spark, &lift, &root, &profile, num_variables)
                    .unwrap();
            assert_eq!(fixed.actual_data_len, 1 << 13);
            let evaluations = fixed.polynomial.as_base().unwrap();
            assert_eq!(evaluations.len(), 1 << num_variables);
            assert_eq!(&evaluations[..1 << 13], unpadded.polynomial.as_base().unwrap());
            assert!(evaluations[1 << 13..].iter().all(|&value| value == F::ZERO));

            let prefixes = terminal_c1_program_prefixes(fixed.program_dimensions, num_variables).unwrap();
            assert_eq!(&prefixes[0][num_variables - 13..], &[EF::ZERO]);
            assert_eq!(&prefixes[1][num_variables - 13..], &[EF::ONE, EF::ZERO]);
            assert_eq!(&prefixes[2][num_variables - 13..], &[EF::ONE, EF::ONE]);
            for prefix in &prefixes {
                assert!(prefix[..num_variables - 13].iter().all(|&value| value == EF::ZERO));
            }
            let statements = fixed.public_statements(&info).unwrap();
            let mut changed_high_region = evaluations.to_vec();
            changed_high_region[fixed.actual_data_len] = F::ONE;
            let changed_high_region = MleOwned::<EF>::Base(ArenaVec::from_slice(&changed_high_region));
            for (statement, prefix) in statements.iter().zip(&prefixes) {
                assert!(statement.point.0.starts_with(prefix));
                assert_eq!(statement.total_num_variables, num_variables);
                assert_eq!(fixed.polynomial.evaluate(&statement.point), statement.values[0].value);
                assert_eq!(
                    changed_high_region.evaluate(&statement.point),
                    statement.values[0].value
                );
                let mut padding_point = statement.point.clone();
                padding_point.0[0] = EF::ONE;
                assert_eq!(fixed.polynomial.evaluate(&padding_point), EF::ZERO);
                padding_point.0[0] = EF::TWO;
                assert_eq!(fixed.polynomial.evaluate(&padding_point), -statement.values[0].value);
            }
            let mut combined_root_point = prefixes[2].clone();
            combined_root_point.extend_from_slice(&root_point);
            let combined_root_point = MultilinearPoint(combined_root_point);
            assert_eq!(
                fixed.polynomial.evaluate(&combined_root_point),
                root.evaluate_sequential(&root_point),
            );
            assert_eq!(
                changed_high_region.evaluate(&combined_root_point),
                root.evaluate_sequential(&root_point),
            );

            let commitment = fixed.preprocess_keccak240();
            let (_, full_length_root) = fixed.whir_config.build_commitment_data_with_hash_profile(
                &fixed.polynomial,
                1 << num_variables,
                ProofHashProfile::Keccak240,
            );
            assert_eq!(commitment.root, full_length_root);
            assert_ne!(commitment.root, unpadded_commitment.root);
            let preprocessing = fixed.verifier_preprocessing_with_root(commitment.root);
            assert_eq!(preprocessing.num_variables, num_variables);
            assert_eq!(preprocessing.actual_data_len, 1 << 13);
            for (actual, expected) in preprocessing.public_statements(&info).unwrap().iter().zip(statements) {
                assert_eq!(actual.point, expected.point);
                assert_eq!(actual.values[0].value, expected.values[0].value);
            }
        }
        assert!(terminal_c1_fixed_programs_from_slices_for_dimension(&spark, &lift, &root, &profile, 12).is_err());
        assert!(
            terminal_c1_fixed_programs_from_slices_for_dimension(&spark, &lift, &root, &profile, usize::MAX).is_err()
        );
    }

    #[test]
    fn terminal_c1_fixed_program_root_is_stable_and_binds_each_program() {
        let profile = terminal_c1_test_profile();
        let spark = patterned_program(1 << 12, 3, 1);
        let lift = patterned_program(1 << 11, 5, 2);
        let root = patterned_program(1 << 11, 7, 4);
        let first = terminal_c1_fixed_programs_from_slices(&spark, &lift, &root, &profile).unwrap();
        let second = terminal_c1_fixed_programs_from_slices(&spark, &lift, &root, &profile).unwrap();
        let first_commitment = first.preprocess_keccak240();
        let second_commitment = second.preprocess_keccak240();
        assert_eq!(
            first_commitment.root.map(|value| value.as_canonical_u32()),
            [
                143_945_171,
                550_339_903,
                259_688_829,
                352_609_386,
                1_034_094_470,
                957_912_433,
                594_209_898,
                782_253_636,
            ]
        );
        assert_eq!(first_commitment.root, second_commitment.root);
        let verifier_preprocessing = first.verifier_preprocessing_with_root(first_commitment.root);
        assert_eq!(verifier_preprocessing.program_dimensions, [12, 11, 11]);
        assert_eq!(verifier_preprocessing.num_variables, 13);
        assert_eq!(verifier_preprocessing.actual_data_len, 1 << 13);
        assert_eq!(verifier_preprocessing.expected_keccak240_root, first_commitment.root);

        for changed_program in 0..3 {
            let mut changed_spark = spark.clone();
            let mut changed_lift = lift.clone();
            let mut changed_root = root.clone();
            [&mut changed_spark, &mut changed_lift, &mut changed_root][changed_program][0] += F::ONE;
            let changed =
                terminal_c1_fixed_programs_from_slices(&changed_spark, &changed_lift, &changed_root, &profile).unwrap();
            assert_ne!(first_commitment.root, changed.preprocess_keccak240().root);
        }
    }

    #[test]
    fn terminal_c1_fixed_program_layout_rejects_wrong_dimensions() {
        let profile = terminal_c1_test_profile();
        let spark = F::zero_vec(1 << 12);
        let lift = F::zero_vec(1 << 11);
        let wrong_root = F::zero_vec(1 << 10);
        assert!(terminal_c1_fixed_programs_from_slices(&spark, &lift, &wrong_root, &profile).is_err());
    }

    #[test]
    fn original_bytecode_reduction_binds_program_and_ordered_claims() {
        let compile = |value| {
            lean_compiler::compile_program(&lean_compiler::ProgramSource::Raw(format!(
                "def main():\n    public = 0\n    assert public[0] == {value}\n    return\n"
            )))
        };
        let bytecode = compile(1);
        let changed_program = compile(2);
        assert_eq!(bytecode.cumulated_n_vars(), changed_program.cumulated_n_vars());
        let cap = original_bytecode_reduction_cap(&bytecode);
        assert_ne!(cap, original_bytecode_reduction_cap(&changed_program));
        assert_ne!(cap, fiat_shamir_domain_sep(&bytecode));
        let claim = |coordinate| {
            let point = backend::MultilinearPoint(vec![coordinate; bytecode.cumulated_n_vars()]);
            Evaluation::new(point.clone(), compute_bytecode_value_at_for(&bytecode, &point))
        };
        let claims = [claim(EF::ZERO), claim(EF::ONE)];
        let baseline = reduce_evaluations_for_bytecode_with_cap(&bytecode, &claims, cap);
        let swapped = reduce_evaluations_for_bytecode_with_cap(&bytecode, &[claims[1].clone(), claims[0].clone()], cap);
        let changed = reduce_evaluations_for_bytecode_with_cap(&bytecode, &[claims[0].clone(), claim(EF::TWO)], cap);
        let single = reduce_evaluations_for_bytecode_with_cap(&bytecode, &claims[..1], cap);
        assert_ne!(baseline.final_claim.point, swapped.final_claim.point);
        assert_ne!(baseline.final_claim.point, changed.final_claim.point);
        assert_ne!(baseline.final_claim.point, single.final_claim.point);
    }

    #[test]
    fn binary_application_root_is_ordered_and_domain_separated() {
        let left = std::array::from_fn(|index| F::from_usize(index + 1));
        let right = std::array::from_fn(|index| F::from_usize(index + 11));
        assert_ne!(
            binary_application_root(&left, &right),
            binary_application_root(&right, &left),
        );
        assert_ne!(binary_application_root(&left, &right), left);
        assert_ne!(binary_application_root(&left, &right), right);
    }
}
