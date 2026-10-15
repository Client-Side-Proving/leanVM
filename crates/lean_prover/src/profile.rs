use backend::*;
use lean_vm::*;
use serde::{Deserialize, Serialize};

use crate::fiat_shamir_domain_sep;

pub const TWO_COMMITMENT_WHIR_BATCHING_POW_BITS: usize = 2;

/// Version-one protocol tag for LeanVM's two-commitment WHIR continuation.
pub const TWO_COMMITMENT_WHIR_MODE_TAG: u32 = 0x3257_0001;

/// Domain tag for the dynamic secondary statements observed before either
/// commitment root is parsed.
pub const TWO_COMMITMENT_WHIR_STATEMENT_TAG: u32 = 0x3257_4f31;

/// Merkle data and root precomputed for the immutable fixed-program
/// polynomial.
#[derive(Debug, Clone)]
pub struct TwoCommitmentWhirPreprocessedCommitment {
    pub prover_data: MerkleData<EF>,
    pub root: [F; DIGEST_LEN],
}

/// Projection of one secondary PCS statement into the public-memory values
/// already observed by the execution transcript.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TwoCommitmentWhirStatementBinding {
    pub public_memory_offset: usize,
    pub point_prefix: Vec<EF>,
}

/// Prover-owned inputs for the terminal two-commitment WHIR continuation.
/// The secondary polynomial is the fixed-program polynomial selected by the
/// application, and its pre-existing statements use coordinates in that
/// polynomial's complete layout.
#[derive(Debug, Clone)]
pub struct TwoCommitmentWhirProverInput {
    pub secondary_polynomial: MleOwned<EF>,
    pub secondary_actual_data_len: usize,
    pub secondary_commitment: TwoCommitmentWhirPreprocessedCommitment,
    pub secondary_statements: Vec<SparseStatement<EF>>,
    /// Start of each statement's flattened point/value coefficients in the
    /// already-observed public-memory region.
    pub secondary_statement_public_memory_bindings: Vec<TwoCommitmentWhirStatementBinding>,
    pub execution_bytecode_point_prefix: Vec<EF>,
    pub two_commitment_batching_pow_bits: usize,
}

/// Verifier-owned inputs for the terminal two-commitment WHIR continuation.
/// The trusted root is checked immediately after it is read, before LogUp or
/// any challenge that depends on either commitment.
#[derive(Debug, Clone)]
pub struct TwoCommitmentWhirVerifierInput {
    pub secondary_num_variables: usize,
    pub secondary_actual_data_len: usize,
    pub expected_secondary_root: [F; DIGEST_LEN],
    pub secondary_statements: Vec<SparseStatement<EF>>,
    /// Start of each statement's flattened point/value coefficients in the
    /// already-observed public-memory region.
    pub secondary_statement_public_memory_bindings: Vec<TwoCommitmentWhirStatementBinding>,
    pub execution_bytecode_point_prefix: Vec<EF>,
    pub two_commitment_batching_pow_bits: usize,
}

impl TwoCommitmentWhirProverInput {
    pub(crate) fn secondary_num_variables(&self) -> Result<usize, &'static str> {
        let polynomial = self.secondary_polynomial.by_ref();
        let len = polynomial.unpacked_len();
        if len == 0 || !len.is_power_of_two() {
            return Err("secondary polynomial length must be a non-zero power of two");
        }
        if polynomial.as_base().is_none() && polynomial.as_packed_base().is_none() {
            return Err("secondary polynomial must be base-field valued");
        }
        Ok(log2_strict_usize(len))
    }

    pub(crate) fn validate(&self) -> Result<usize, &'static str> {
        let n_vars = self.secondary_num_variables()?;
        validate_two_commitment_input(
            n_vars,
            self.secondary_actual_data_len,
            &self.secondary_statements,
            &self.secondary_statement_public_memory_bindings,
            &self.execution_bytecode_point_prefix,
            self.two_commitment_batching_pow_bits,
        )?;
        Ok(n_vars)
    }
}

impl TwoCommitmentWhirVerifierInput {
    pub(crate) fn validate(&self) -> Result<(), &'static str> {
        validate_two_commitment_input(
            self.secondary_num_variables,
            self.secondary_actual_data_len,
            &self.secondary_statements,
            &self.secondary_statement_public_memory_bindings,
            &self.execution_bytecode_point_prefix,
            self.two_commitment_batching_pow_bits,
        )
    }
}

fn validate_two_commitment_input(
    secondary_num_variables: usize,
    secondary_actual_data_len: usize,
    secondary_statements: &[SparseStatement<EF>],
    secondary_statement_public_memory_bindings: &[TwoCommitmentWhirStatementBinding],
    execution_bytecode_point_prefix: &[EF],
    two_commitment_batching_pow_bits: usize,
) -> Result<(), &'static str> {
    let polynomial_len = 1usize
        .checked_shl(
            secondary_num_variables
                .try_into()
                .map_err(|_| "secondary polynomial dimension is too large")?,
        )
        .ok_or("secondary polynomial dimension is too large")?;
    if secondary_actual_data_len == 0 || secondary_actual_data_len > polynomial_len {
        return Err("secondary actual data length is outside its polynomial domain");
    }
    if secondary_statements.is_empty() {
        return Err("secondary statements must not be empty");
    }
    if secondary_statement_public_memory_bindings.len() != secondary_statements.len() {
        return Err("every secondary statement must be bound to public memory");
    }
    if execution_bytecode_point_prefix.len() > secondary_num_variables
        || !execution_bytecode_point_prefix.ends_with(&[EF::ONE, EF::ONE])
        || execution_bytecode_point_prefix[..execution_bytecode_point_prefix.len().saturating_sub(2)]
            .iter()
            .any(|&coordinate| coordinate != EF::ZERO)
    {
        return Err("terminal execution bytecode point prefix must be zero padding followed by [1, 1]");
    }
    if two_commitment_batching_pow_bits != TWO_COMMITMENT_WHIR_BATCHING_POW_BITS {
        return Err("terminal two-commitment batching must use two grinding bits");
    }
    for statement in secondary_statements {
        if statement.total_num_variables != secondary_num_variables
            || statement.point.len() > secondary_num_variables
            || statement.values.is_empty()
        {
            return Err("secondary statement has the wrong polynomial layout");
        }
        let selector_variables = secondary_num_variables - statement.point.len();
        let selector_count = 1usize
            .checked_shl(
                selector_variables
                    .try_into()
                    .map_err(|_| "secondary selector dimension is too large")?,
            )
            .ok_or("secondary selector dimension is too large")?;
        if statement.values.iter().any(|value| value.selector >= selector_count) {
            return Err("secondary statement selector is outside its polynomial layout");
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn two_commitment_fiat_shamir_domain_sep(
    profile: &WhirExecutionProfile,
    bytecode: &Bytecode,
    secondary_num_variables: usize,
    secondary_actual_data_len: usize,
    secondary_statements: &[SparseStatement<EF>],
    secondary_statement_public_memory_bindings: &[TwoCommitmentWhirStatementBinding],
    execution_bytecode_point_prefix: &[EF],
    two_commitment_batching_pow_bits: usize,
) -> [F; DIGEST_LEN] {
    // The capacity is fixed for a generated verifier. It binds the protocol
    // shape, while application-supplied statement points and values are
    // observed separately before dimensions and commitment roots.
    let (_, encoded) = two_commitment_fiat_shamir_static_descriptor(
        secondary_num_variables,
        secondary_actual_data_len,
        secondary_statements,
        secondary_statement_public_memory_bindings,
        execution_bytecode_point_prefix,
        two_commitment_batching_pow_bits,
    );
    let descriptor = poseidon_hash_slice(&encoded);
    poseidon16_compress_pair(&profile.fiat_shamir_domain_sep(bytecode), &descriptor)
}

/// Return the static C1 descriptor exactly as hashed into the Fiat-Shamir
/// capacity, together with its field count before digest-width padding.
pub fn two_commitment_fiat_shamir_static_descriptor(
    secondary_num_variables: usize,
    secondary_actual_data_len: usize,
    secondary_statements: &[SparseStatement<EF>],
    secondary_statement_public_memory_bindings: &[TwoCommitmentWhirStatementBinding],
    execution_bytecode_point_prefix: &[EF],
    two_commitment_batching_pow_bits: usize,
) -> (usize, Vec<F>) {
    let mut encoded = vec![
        F::from_u32(TWO_COMMITMENT_WHIR_MODE_TAG),
        F::from_usize(two_commitment_batching_pow_bits),
        F::from_usize(secondary_num_variables),
        F::from_usize(secondary_actual_data_len),
        F::from_usize(secondary_statements.len()),
        F::from_usize(execution_bytecode_point_prefix.len()),
        F::ZERO,
        F::from_usize(secondary_statement_public_memory_bindings.len()),
    ];
    for coordinate in execution_bytecode_point_prefix {
        encoded.extend_from_slice(coordinate.as_basis_coefficients_slice());
    }
    for (statement, binding) in secondary_statements
        .iter()
        .zip(secondary_statement_public_memory_bindings)
    {
        encoded.extend([
            F::from_usize(statement.total_num_variables),
            F::from_usize(statement.point.len()),
            F::from_usize(statement.values.len()),
            F::from_bool(statement.is_next),
            F::from_usize(binding.public_memory_offset),
            F::from_usize(binding.point_prefix.len()),
        ]);
        for coordinate in &binding.point_prefix {
            encoded.extend_from_slice(coordinate.as_basis_coefficients_slice());
        }
        for value in &statement.values {
            encoded.push(F::from_usize(value.selector));
        }
    }
    let field_count_before_padding = encoded.len();
    encoded[6] = F::from_usize(field_count_before_padding);
    encoded.resize(encoded.len().next_multiple_of(DIGEST_LEN), F::ZERO);
    (field_count_before_padding, encoded)
}

/// Require each secondary statement to be an exact projection of base-field
/// words that the execution transcript has already observed as public memory.
/// Statement selectors and offsets are bound by the static domain separator.
pub(crate) fn validate_two_commitment_public_memory_binding(
    public_memory: &[F],
    secondary_statements: &[SparseStatement<EF>],
    secondary_statement_public_memory_bindings: &[TwoCommitmentWhirStatementBinding],
) -> Result<(), &'static str> {
    if secondary_statements.len() != secondary_statement_public_memory_bindings.len() {
        return Err("every secondary statement must be bound to public memory");
    }
    for (statement, binding) in secondary_statements
        .iter()
        .zip(secondary_statement_public_memory_bindings)
    {
        if !statement.point.0.starts_with(&binding.point_prefix) {
            return Err("secondary statement has the wrong public-memory point prefix");
        }
        let field_count = (statement.point.len() - binding.point_prefix.len() + statement.values.len())
            .checked_mul(<EF as BasedVectorSpace<F>>::DIMENSION)
            .ok_or("secondary statement binding is too large")?;
        let end = binding
            .public_memory_offset
            .checked_add(field_count)
            .ok_or("secondary statement binding is too large")?;
        let observed = public_memory
            .get(binding.public_memory_offset..end)
            .ok_or("secondary statement binding is outside public memory")?;
        let expected = statement
            .point
            .iter()
            .skip(binding.point_prefix.len())
            .chain(statement.values.iter().map(|value| &value.value))
            .flat_map(|value| value.as_basis_coefficients_slice().iter().copied());
        if !observed.iter().copied().eq(expected) {
            return Err("secondary statement differs from observed public memory");
        }
    }
    Ok(())
}

/// Canonically encode the dynamic secondary claims for transcript observation.
/// This occurs before proof dimensions and both commitment roots, so every C1
/// challenge is bound to the carried spark/lift claims without making the
/// generated verifier capacity proof-specific.
pub fn two_commitment_statement_observation(secondary_statements: &[SparseStatement<EF>]) -> Vec<F> {
    let mut encoded = vec![
        F::from_u32(TWO_COMMITMENT_WHIR_STATEMENT_TAG),
        F::from_usize(secondary_statements.len()),
        F::ZERO,
        F::ZERO,
    ];
    for statement in secondary_statements {
        encoded.extend([
            F::from_usize(statement.total_num_variables),
            F::from_usize(statement.point.len()),
            F::from_usize(statement.values.len()),
            F::from_bool(statement.is_next),
        ]);
        for coordinate in &statement.point.0 {
            encoded.extend_from_slice(coordinate.as_basis_coefficients_slice());
        }
        for value in &statement.values {
            encoded.push(F::from_usize(value.selector));
            encoded.extend_from_slice(value.value.as_basis_coefficients_slice());
        }
    }
    encoded[2] = F::from_usize(encoded.len());
    encoded
}

/// An application-selected WHIR configuration. Explicit-profile proofs bind all
/// these parameters into their initial Fiat-Shamir cap before public inputs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct WhirExecutionProfile {
    pub security_bits: usize,
    pub grinding_bits: usize,
    pub first_folding_factor: usize,
    pub subsequent_folding_factor: usize,
    pub rs_domain_initial_reduction_factor: usize,
    pub max_num_variables_to_send_coeffs: usize,
    pub log_inv_rate: usize,
}

impl WhirExecutionProfile {
    pub fn validate_for_hash(&self, hash_profile: ProofHashProfile) -> Result<(), &'static str> {
        self.validate()?;
        if hash_profile == ProofHashProfile::Keccak240 && self.security_bits > 120 {
            return Err("Keccak240 supports at most 120 bits of generic collision security");
        }
        Ok(())
    }

    pub const fn security_100(log_inv_rate: usize) -> Self {
        Self {
            security_bits: 100,
            grinding_bits: 16,
            first_folding_factor: 9,
            subsequent_folding_factor: 5,
            rs_domain_initial_reduction_factor: 5,
            max_num_variables_to_send_coeffs: 8,
            log_inv_rate,
        }
    }

    pub fn validate(&self) -> Result<(), &'static str> {
        if !(MIN_WHIR_LOG_INV_RATE..=6).contains(&self.log_inv_rate) {
            return Err("explicit profile log_inv_rate must be between 1 and 6");
        }
        if !(1..=121).contains(&self.security_bits) || self.grinding_bits >= self.security_bits {
            return Err("security must be between 1 and 121 and exceed grinding");
        }
        if self.grinding_bits > 30 {
            return Err("recursive grinding supports at most 30 bits");
        }
        if !(3..=9).contains(&self.first_folding_factor) || !(3..=9).contains(&self.subsequent_folding_factor) {
            return Err("recursive folding factors must be between 3 and 9");
        }
        if self.rs_domain_initial_reduction_factor == 0
            || self.rs_domain_initial_reduction_factor > self.first_folding_factor
        {
            return Err("initial RS reduction must be positive and no larger than the first fold");
        }
        if self.max_num_variables_to_send_coeffs < self.subsequent_folding_factor - 1
            || self.max_num_variables_to_send_coeffs > 10
        {
            return Err("final coefficient threshold must be between the subsequent fold minus one and 10");
        }
        Ok(())
    }

    pub fn validate_for_n_vars(&self, n_vars: usize) -> Result<(), &'static str> {
        self.validate()?;
        if n_vars <= self.first_folding_factor + self.max_num_variables_to_send_coeffs
            || n_vars > F::TWO_ADICITY + self.first_folding_factor
            || n_vars + self.log_inv_rate
                > F::TWO_ADICITY
                    + self
                        .first_folding_factor
                        .min(self.rs_domain_initial_reduction_factor + self.subsequent_folding_factor)
        {
            return Err("stacked polynomial does not fit the WHIR folded two-adic domains");
        }
        let config = WhirConfig::<EF>::new(&self.whir_config(), n_vars);
        if !(1..=4).contains(&config.commitment_ood_samples)
            || config.round_parameters.iter().any(|round| {
                !(1..=4).contains(&round.ood_samples)
                    || round.num_queries == 0
                    || round.num_queries + round.ood_samples >= 400
            })
            || config.final_queries == 0
            || config.final_queries >= 400
        {
            return Err("derived query or OOD counts exceed recursive verifier bounds");
        }
        let actual_grinding = config
            .round_parameters
            .iter()
            .flat_map(|round| [round.query_pow_bits, round.folding_pow_bits])
            .chain([config.starting_folding_pow_bits, config.final_query_pow_bits])
            .max()
            .unwrap();
        if actual_grinding > self.grinding_bits {
            return Err("derived grinding exceeds the requested budget");
        }
        Ok(())
    }

    pub fn whir_config(&self) -> WhirConfigBuilder {
        WhirConfigBuilder {
            folding_factor: FoldingFactor::new(self.first_folding_factor, self.subsequent_folding_factor),
            soundness_type: SecurityAssumption::JohnsonBound,
            pow_bits: self.grinding_bits,
            max_num_variables_to_send_coeffs: self.max_num_variables_to_send_coeffs,
            rs_domain_initial_reduction_factor: self.rs_domain_initial_reduction_factor,
            security_level: self.security_bits,
            starting_log_inv_rate: self.log_inv_rate,
        }
    }

    pub fn fiat_shamir_domain_sep(&self, bytecode: &Bytecode) -> [F; 8] {
        // Version two separates the carried WHIR claim from fresh constraints
        // with distinct powers of the continuation batching challenge.
        // The fixed-width block also pins Johnson-bound parameter selection.
        let encoded = [
            0x5750_0002,
            self.security_bits,
            self.grinding_bits,
            self.first_folding_factor,
            self.subsequent_folding_factor,
            self.rs_domain_initial_reduction_factor,
            self.max_num_variables_to_send_coeffs,
            self.log_inv_rate,
        ]
        .map(F::from_usize);
        poseidon16_compress_pair(&fiat_shamir_domain_sep(bytecode), &encoded)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lean_compiler::{ProgramSource, compile_program};

    fn dense_statement(n_vars: usize, point_value: u32, value: u32) -> SparseStatement<EF> {
        SparseStatement::dense(
            MultilinearPoint(vec![EF::from_u32(point_value); n_vars]),
            EF::from_u32(value),
        )
    }

    #[test]
    fn explicit_profile_separates_previous_continuation_equations() {
        let bytecode = compile_program(&ProgramSource::Raw("def main():\n    return\n".to_owned()));
        let profile = WhirExecutionProfile::security_100(4);
        let previous_encoding = [
            0x5750_0001,
            profile.security_bits,
            profile.grinding_bits,
            profile.first_folding_factor,
            profile.subsequent_folding_factor,
            profile.rs_domain_initial_reduction_factor,
            profile.max_num_variables_to_send_coeffs,
            profile.log_inv_rate,
        ]
        .map(F::from_usize);
        let previous_cap = poseidon16_compress_pair(&fiat_shamir_domain_sep(&bytecode), &previous_encoding);
        assert_ne!(profile.fiat_shamir_domain_sep(&bytecode), previous_cap);
    }

    #[test]
    fn two_commitment_domain_binds_static_layout_and_public_memory_binds_claims() {
        let bytecode = compile_program(&ProgramSource::Raw(
            "def main():\n    public = 0\n    assert public[0] == 1\n    return\n".to_owned(),
        ));
        let profile = WhirExecutionProfile::security_100(4);
        let n_vars = 13;
        let actual_data_len = 1 << n_vars;
        let statements = vec![dense_statement(n_vars, 3, 5)];
        let public_memory_bindings = vec![TwoCommitmentWhirStatementBinding {
            public_memory_offset: 8,
            point_prefix: vec![EF::from_u32(3)],
        }];
        let prefix = vec![EF::ONE, EF::ONE];
        let cap = two_commitment_fiat_shamir_domain_sep(
            &profile,
            &bytecode,
            n_vars,
            actual_data_len,
            &statements,
            &public_memory_bindings,
            &prefix,
            TWO_COMMITMENT_WHIR_BATCHING_POW_BITS,
        );

        let changed_statement = vec![dense_statement(n_vars, 3, 6)];
        assert_eq!(
            cap,
            two_commitment_fiat_shamir_domain_sep(
                &profile,
                &bytecode,
                n_vars,
                actual_data_len,
                &changed_statement,
                &public_memory_bindings,
                &prefix,
                TWO_COMMITMENT_WHIR_BATCHING_POW_BITS,
            )
        );
        let mut public_memory = vec![F::ZERO; 8];
        let mut dynamic_claim = statements[0].point.0[1..].to_vec();
        dynamic_claim.extend(statements[0].values.iter().map(|value| value.value));
        public_memory.extend(flatten_scalars_to_base::<F, EF>(&dynamic_claim));
        assert!(
            validate_two_commitment_public_memory_binding(&public_memory, &statements, &public_memory_bindings,)
                .is_ok()
        );
        assert!(
            validate_two_commitment_public_memory_binding(&public_memory, &changed_statement, &public_memory_bindings,)
                .is_err()
        );
        let mut wrong_prefix_statement = statements.clone();
        wrong_prefix_statement[0].point.0[0] = EF::from_u32(4);
        assert!(
            validate_two_commitment_public_memory_binding(
                &public_memory,
                &wrong_prefix_statement,
                &public_memory_bindings,
            )
            .is_err()
        );
        let changed_prefix_bindings = vec![TwoCommitmentWhirStatementBinding {
            public_memory_offset: 8,
            point_prefix: vec![EF::from_u32(4)],
        }];
        assert_ne!(
            cap,
            two_commitment_fiat_shamir_domain_sep(
                &profile,
                &bytecode,
                n_vars,
                actual_data_len,
                &statements,
                &changed_prefix_bindings,
                &prefix,
                TWO_COMMITMENT_WHIR_BATCHING_POW_BITS,
            )
        );
        assert_ne!(
            cap,
            two_commitment_fiat_shamir_domain_sep(
                &profile,
                &bytecode,
                n_vars,
                actual_data_len - 1,
                &statements,
                &public_memory_bindings,
                &prefix,
                TWO_COMMITMENT_WHIR_BATCHING_POW_BITS,
            )
        );
        assert_ne!(
            cap,
            two_commitment_fiat_shamir_domain_sep(
                &profile,
                &bytecode,
                n_vars,
                actual_data_len,
                &statements,
                &public_memory_bindings,
                &[EF::ONE, EF::ZERO],
                TWO_COMMITMENT_WHIR_BATCHING_POW_BITS,
            )
        );
        assert_ne!(
            cap,
            two_commitment_fiat_shamir_domain_sep(
                &profile,
                &bytecode,
                n_vars,
                actual_data_len,
                &statements,
                &public_memory_bindings,
                &prefix,
                TWO_COMMITMENT_WHIR_BATCHING_POW_BITS + 1,
            )
        );
    }

    #[test]
    fn two_commitment_layout_rejects_invalid_actual_data_length() {
        let statements = vec![dense_statement(3, 2, 7)];
        let public_memory_bindings = [TwoCommitmentWhirStatementBinding {
            public_memory_offset: 0,
            point_prefix: Vec::new(),
        }];
        let prefix = [EF::ONE, EF::ONE];
        assert!(
            validate_two_commitment_input(
                3,
                0,
                &statements,
                &public_memory_bindings,
                &prefix,
                TWO_COMMITMENT_WHIR_BATCHING_POW_BITS,
            )
            .is_err()
        );
        assert!(
            validate_two_commitment_input(
                3,
                9,
                &statements,
                &public_memory_bindings,
                &prefix,
                TWO_COMMITMENT_WHIR_BATCHING_POW_BITS,
            )
            .is_err()
        );
    }

    #[test]
    fn two_commitment_zero_padding_binds_selectors_and_public_memory() {
        let bytecode = compile_program(&ProgramSource::Raw("def main():\n    return\n".to_owned()));
        let profile = WhirExecutionProfile::security_100(4);
        let public_memory = flatten_scalars_to_base::<F, EF>(&[EF::from_u32(3), EF::from_u32(5), EF::from_u32(7)]);
        let mut previous_cap = None;
        for padding in 0..=2 {
            let num_variables = 3 + padding;
            let mut point_prefix = vec![EF::ZERO; padding + 1];
            let mut point = point_prefix.clone();
            point.extend([EF::from_u32(3), EF::from_u32(5)]);
            let statements = [SparseStatement::dense(MultilinearPoint(point), EF::from_u32(7))];
            let bindings = [TwoCommitmentWhirStatementBinding {
                public_memory_offset: 0,
                point_prefix: std::mem::take(&mut point_prefix),
            }];
            let mut execution_prefix = vec![EF::ZERO; padding];
            execution_prefix.extend([EF::ONE, EF::ONE]);
            let validate = |prefix: &[EF]| {
                validate_two_commitment_input(
                    num_variables,
                    8,
                    &statements,
                    &bindings,
                    prefix,
                    TWO_COMMITMENT_WHIR_BATCHING_POW_BITS,
                )
            };
            assert!(validate(&execution_prefix).is_ok());
            assert!(validate(&[]).is_err());
            assert!(validate(&[EF::ONE]).is_err());
            for index in 0..execution_prefix.len() {
                let mut changed = execution_prefix.clone();
                changed[index] += EF::ONE;
                assert!(validate(&changed).is_err());
            }
            assert!(validate_two_commitment_public_memory_binding(&public_memory, &statements, &bindings).is_ok());
            for index in 0..bindings[0].point_prefix.len() {
                let mut changed = statements.clone();
                changed[0].point.0[index] = EF::ONE;
                assert!(validate_two_commitment_public_memory_binding(&public_memory, &changed, &bindings).is_err());
            }
            let cap = two_commitment_fiat_shamir_domain_sep(
                &profile,
                &bytecode,
                num_variables,
                8,
                &statements,
                &bindings,
                &execution_prefix,
                TWO_COMMITMENT_WHIR_BATCHING_POW_BITS,
            );
            if let Some(previous_cap) = previous_cap {
                assert_ne!(cap, previous_cap);
            }
            previous_cap = Some(cap);
        }
    }
}
