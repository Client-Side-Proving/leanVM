// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use std::{fmt::Debug, marker::PhantomData};

use ::utils::log2_strict_usize;
use fiat_shamir::{FSVerifier, ProofError, ProofResult, try_pack_scalars_to_extension};
use field::{ExtensionField, Field, PrimeCharacteristicRing, TwoAdicField};
use koala_bear::KoalaBear;

use crate::*;

#[derive(Debug, Clone)]
pub struct ParsedCommitment<F: Field, EF: ExtensionField<F>> {
    pub num_variables: usize,
    pub root: [PF<EF>; DIGEST_ELEMS],
    pub ood_points: Vec<EF>,
    pub ood_answers: Vec<EF>,
    pub base_field: PhantomData<F>,
}

impl<F: Field, EF: ExtensionField<F>> ParsedCommitment<F, EF> {
    fn parse_root(verifier_state: &mut impl FSVerifier<EF>) -> ProofResult<[PF<EF>; DIGEST_ELEMS]>
    where
        F: TwoAdicField,
        EF: ExtensionField<F> + TwoAdicField,
        EF: KoalaBearExtension,
    {
        let root = verifier_state.next_base_scalars_vec(DIGEST_ELEMS)?.try_into().unwrap();
        if verifier_state.hash_profile() == symetric::ProofHashProfile::Keccak240
            && symetric::decode_keccak240(&root).is_none()
        {
            return Err(ProofError::InvalidProof);
        }
        Ok(root)
    }

    pub fn parse(
        verifier_state: &mut impl FSVerifier<EF>,
        num_variables: usize,
        ood_samples: usize,
    ) -> ProofResult<Self>
    where
        F: TwoAdicField,
        EF: ExtensionField<F> + TwoAdicField,
        EF: KoalaBearExtension,
    {
        let root = Self::parse_root(verifier_state)?;
        let mut ood_points = vec![];
        let ood_answers = if ood_samples > 0 {
            ood_points = verifier_state.sample_vec(ood_samples);
            verifier_state.next_extension_scalars_vec(ood_samples)?
        } else {
            Vec::new()
        };
        Ok(Self {
            num_variables,
            root,
            ood_points,
            ood_answers,
            base_field: PhantomData,
        })
    }

    /// Parses a commitment root without sampling or reading an OOD answer.
    /// This is the commitment shape used by the two-commitment batching API.
    pub fn parse_without_ood(verifier_state: &mut impl FSVerifier<EF>, num_variables: usize) -> ProofResult<Self>
    where
        F: TwoAdicField,
        EF: ExtensionField<F> + TwoAdicField,
        EF: KoalaBearExtension,
    {
        Ok(Self {
            num_variables,
            root: Self::parse_root(verifier_state)?,
            ood_points: Vec::new(),
            ood_answers: Vec::new(),
            base_field: PhantomData,
        })
    }

    pub fn oods_constraints(&self) -> Vec<SparseStatement<EF>> {
        self.ood_points
            .iter()
            .zip(&self.ood_answers)
            .map(|(&point, &eval)| {
                SparseStatement::dense(
                    MultilinearPoint::expand_from_univariate(point, self.num_variables),
                    eval,
                )
            })
            .collect()
    }
}

impl<EF> WhirConfig<EF>
where
    EF: TwoAdicField + KoalaBearExtension,
{
    pub fn parse_commitment<F: TwoAdicField>(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
    ) -> ProofResult<ParsedCommitment<F, EF>>
    where
        EF: ExtensionField<F>,
    {
        ParsedCommitment::<F, EF>::parse(verifier_state, self.num_variables, self.commitment_ood_samples)
    }

    pub fn parse_commitment_without_ood<F: TwoAdicField>(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
    ) -> ProofResult<ParsedCommitment<F, EF>>
    where
        EF: ExtensionField<F>,
    {
        ParsedCommitment::<F, EF>::parse_without_ood(verifier_state, self.num_variables)
    }
}

impl<EF> WhirConfig<EF>
where
    EF: TwoAdicField + KoalaBearExtension,
{
    #[allow(clippy::too_many_lines)]
    pub fn verify<F>(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        parsed_commitment: &ParsedCommitment<F, EF>,
        statement: Vec<SparseStatement<EF>>,
    ) -> ProofResult<MultilinearPoint<EF>>
    where
        F: TwoAdicField + ExtensionField<KoalaBear>,
        EF: ExtensionField<F>,
    {
        statement
            .iter()
            .for_each(|c| assert_eq!(c.total_num_variables, parsed_commitment.num_variables));

        // During the rounds we collect constraints, combination randomness, folding randomness
        // and we update the claimed sum of constraint evaluation.
        let mut round_constraints = Vec::new();
        let mut round_folding_randomness = Vec::new();
        let mut claimed_sum = EF::ZERO;
        let mut prev_commitment = parsed_commitment.clone();

        // Combine OODS and statement constraints to claimed_sum.
        verifier_state.duplex();
        let constraints: Vec<_> = prev_commitment
            .oods_constraints()
            .into_iter()
            .chain(statement)
            .collect();
        let combination_randomness = self.combine_constraints(verifier_state, &mut claimed_sum, &constraints, false)?;
        round_constraints.push((combination_randomness, constraints));

        // Initial sumcheck
        let folding_randomness = verify_sumcheck_rounds::<F, EF>(
            verifier_state,
            &mut claimed_sum,
            self.folding_factor.at_round(0),
            self.starting_folding_pow_bits,
        )?;
        round_folding_randomness.push(folding_randomness);

        for round_index in 0..self.n_rounds() {
            // Fetch round parameters from config
            let round_params = &self.round_parameters[round_index];

            // Receive commitment to the folded polynomial (likely encoded at higher expansion)
            let new_commitment =
                ParsedCommitment::<F, EF>::parse(verifier_state, round_params.num_variables, round_params.ood_samples)?;

            // Verify in-domain challenges on the previous commitment.
            let stir_constraints = self.verify_stir_challenges(
                verifier_state,
                round_params,
                &prev_commitment,
                round_folding_randomness.last().unwrap(),
                round_index,
            )?;

            // Add out-of-domain and in-domain constraints to claimed_sum
            let constraints: Vec<SparseStatement<EF>> = new_commitment
                .oods_constraints()
                .into_iter()
                .chain(stir_constraints)
                .collect();

            verifier_state.duplex();
            let combination_randomness =
                self.combine_constraints(verifier_state, &mut claimed_sum, &constraints, true)?;
            round_constraints.push((combination_randomness.clone(), constraints));

            let folding_randomness = verify_sumcheck_rounds::<F, EF>(
                verifier_state,
                &mut claimed_sum,
                self.folding_factor.at_round(round_index + 1),
                round_params.folding_pow_bits,
            )?;

            round_folding_randomness.push(folding_randomness);

            // Update round parameters
            prev_commitment = new_commitment;
        }

        // In the final round we receive the full polynomial instead of a commitment.
        let n_final_coeffs = 1 << self.n_vars_of_final_polynomial();
        let final_coefficients = verifier_state.next_extension_scalars_vec(n_final_coeffs)?;

        // Verify in-domain challenges on the previous commitment.
        let stir_constraints = self.verify_stir_challenges(
            verifier_state,
            &self.final_round_config(),
            &prev_commitment,
            round_folding_randomness.last().unwrap(),
            self.n_rounds(),
        )?;

        // Verify stir constraints directly on final polynomial
        stir_constraints
            .iter()
            .all(|c| verify_constraint_coeffs(c, &final_coefficients))
            .then_some(())
            .ok_or(ProofError::InvalidProof)?;

        let final_sumcheck_randomness =
            verify_sumcheck_rounds::<F, EF>(verifier_state, &mut claimed_sum, self.final_sumcheck_rounds, 0)?;
        round_folding_randomness.push(final_sumcheck_randomness.clone());

        // Compute folding randomness across all rounds.
        let folding_randomness = MultilinearPoint(
            round_folding_randomness
                .into_iter()
                .flat_map(|poly| poly.0.into_iter())
                .collect(),
        );

        let evaluation_of_weights = self.eval_constraints_poly(&round_constraints, folding_randomness.clone());

        // Check the final sumcheck evaluation (coefficient form, reversed point)
        let mut reversed_point = final_sumcheck_randomness.0.clone();
        reversed_point.reverse();
        let final_value = eval_multilinear_coeffs(&final_coefficients, &reversed_point);
        if claimed_sum != evaluation_of_weights * final_value {
            return Err(ProofError::InvalidProof);
        }

        Ok(folding_randomness)
    }

    /// Verifies two separately committed base-field polynomials through one
    /// WHIR continuation. Both roots must have been parsed without individual
    /// OOD samples. The caller must bind this proof shape, the statement
    /// layouts, and `batching_pow_bits` in its protocol domain separator.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub fn verify_two_commitments<F>(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        batching_pow_bits: usize,
        primary_commitment: &ParsedCommitment<F, EF>,
        primary_statement: Vec<SparseStatement<EF>>,
        secondary_commitment: &ParsedCommitment<F, EF>,
        secondary_statement: Vec<SparseStatement<EF>>,
    ) -> ProofResult<MultilinearPoint<EF>>
    where
        F: TwoAdicField + ExtensionField<KoalaBear>,
        EF: ExtensionField<F>,
    {
        self.verify_linear_combination::<F, 2>(
            verifier_state,
            batching_pow_bits,
            [primary_commitment, secondary_commitment],
            [primary_statement, secondary_statement],
        )
    }

    /// Verify three initial commitments followed by one shared WHIR continuation.
    /// The caller binds the exact mode, grinding budget, roots, and claim groups.
    pub fn verify_three_commitments<F>(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        batching_pow_bits: usize,
        commitments: [&ParsedCommitment<F, EF>; 3],
        statements: [Vec<SparseStatement<EF>>; 3],
    ) -> ProofResult<MultilinearPoint<EF>>
    where
        F: TwoAdicField + ExtensionField<KoalaBear>,
        EF: ExtensionField<F>,
    {
        self.verify_linear_combination::<F, 3>(verifier_state, batching_pow_bits, commitments, statements)
    }

    fn verify_linear_combination<F, const N: usize>(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        batching_pow_bits: usize,
        commitments: [&ParsedCommitment<F, EF>; N],
        statements: [Vec<SparseStatement<EF>>; N],
    ) -> ProofResult<MultilinearPoint<EF>>
    where
        F: TwoAdicField + ExtensionField<KoalaBear>,
        EF: ExtensionField<F>,
    {
        if !(2..=3).contains(&N)
            || self.num_variables != self.folding_factor.total_number(self.n_rounds()) + self.final_sumcheck_rounds
            || self.n_rounds() == 0
            || self.commitment_ood_samples == 0
            || commitments.iter().any(|commitment| {
                commitment.num_variables != self.num_variables
                    || !commitment.ood_points.is_empty()
                    || !commitment.ood_answers.is_empty()
            })
            || statements
                .iter()
                .any(|group| !valid_initial_statement(group, self.num_variables))
        {
            return Err(ProofError::InvalidProof);
        }
        verifier_state.duplex();
        let group_randomness = verifier_state.sample();
        let coefficients = statements
            .each_ref()
            .map(|group| statement_coefficients(group, group_randomness, EF::ONE));
        let cross_values = verifier_state.next_extension_scalars_vec(N * (N - 1))?;
        let mut cross_index = 0;
        let mut cross = [[EF::ZERO; N]; N];
        for i in 0..N {
            for j in 0..N {
                cross[i][j] = if i == j {
                    statement_value_sum(&statements[i], &coefficients[i])
                } else {
                    let value = cross_values[cross_index];
                    cross_index += 1;
                    value
                };
            }
        }
        verifier_state.check_pow_grinding(batching_pow_bits)?;
        verifier_state.duplex();
        let lambda: EF = verifier_state.sample();
        let polynomial_scalars = lambda.powers().collect_n(N);
        verifier_state.duplex();
        let ood_points = verifier_state.sample_vec(self.commitment_ood_samples);
        let ood_answers = verifier_state.next_extension_scalars_vec(self.commitment_ood_samples)?;
        let ood_constraints = ood_points
            .iter()
            .zip(&ood_answers)
            .map(|(&point, &value)| {
                SparseStatement::dense(
                    MultilinearPoint::expand_from_univariate(point, self.num_variables),
                    value,
                )
            })
            .collect::<Vec<_>>();
        verifier_state.duplex();
        let theta: EF = verifier_state.sample();
        let scales = theta.powers().collect_n(self.commitment_ood_samples + N);
        let mut initial_coefficients = scales[..self.commitment_ood_samples].to_vec();
        let mut claimed_sum = ood_answers
            .iter()
            .zip(&scales)
            .map(|(&answer, &coefficient)| answer * coefficient)
            .sum::<EF>();
        for i in 0..N {
            let scale = scales[self.commitment_ood_samples + i];
            initial_coefficients.extend(coefficients[i].iter().map(|&coefficient| scale * coefficient));
            claimed_sum += scale * (0..N).map(|j| polynomial_scalars[j] * cross[i][j]).sum::<EF>();
        }
        let mut initial_constraints = ood_constraints;
        for group in statements {
            initial_constraints.extend(group);
        }
        debug_assert_eq!(initial_coefficients.len(), statement_value_count(&initial_constraints));

        let mut round_constraints = vec![(initial_coefficients, initial_constraints)];
        let mut round_folding_randomness = Vec::new();

        let folding_randomness = verify_sumcheck_rounds::<F, EF>(
            verifier_state,
            &mut claimed_sum,
            self.folding_factor.at_round(0),
            self.starting_folding_pow_bits,
        )?;
        round_folding_randomness.push(folding_randomness);

        let mut prev_commitment = None;
        for round_index in 0..self.n_rounds() {
            let round_params = &self.round_parameters[round_index];
            let new_commitment =
                ParsedCommitment::<F, EF>::parse(verifier_state, round_params.num_variables, round_params.ood_samples)?;

            let stir_constraints = if round_index == 0 {
                self.verify_stir_challenges_linear_combination(
                    verifier_state,
                    round_params,
                    &commitments,
                    round_folding_randomness.last().unwrap(),
                    &polynomial_scalars,
                )?
            } else {
                self.verify_stir_challenges(
                    verifier_state,
                    round_params,
                    prev_commitment.as_ref().unwrap(),
                    round_folding_randomness.last().unwrap(),
                    round_index,
                )?
            };

            let constraints: Vec<SparseStatement<EF>> = new_commitment
                .oods_constraints()
                .into_iter()
                .chain(stir_constraints)
                .collect();

            verifier_state.duplex();
            let combination_randomness =
                self.combine_constraints(verifier_state, &mut claimed_sum, &constraints, true)?;
            round_constraints.push((combination_randomness, constraints));

            let folding_randomness = verify_sumcheck_rounds::<F, EF>(
                verifier_state,
                &mut claimed_sum,
                self.folding_factor.at_round(round_index + 1),
                round_params.folding_pow_bits,
            )?;
            round_folding_randomness.push(folding_randomness);
            prev_commitment = Some(new_commitment);
        }

        let n_final_coeffs = 1 << self.n_vars_of_final_polynomial();
        let final_coefficients = verifier_state.next_extension_scalars_vec(n_final_coeffs)?;
        let stir_constraints = self.verify_stir_challenges(
            verifier_state,
            &self.final_round_config(),
            prev_commitment.as_ref().unwrap(),
            round_folding_randomness.last().unwrap(),
            self.n_rounds(),
        )?;
        stir_constraints
            .iter()
            .all(|constraint| verify_constraint_coeffs(constraint, &final_coefficients))
            .then_some(())
            .ok_or(ProofError::InvalidProof)?;

        let final_sumcheck_randomness =
            verify_sumcheck_rounds::<F, EF>(verifier_state, &mut claimed_sum, self.final_sumcheck_rounds, 0)?;
        round_folding_randomness.push(final_sumcheck_randomness.clone());

        let folding_randomness =
            MultilinearPoint(round_folding_randomness.into_iter().flat_map(|point| point.0).collect());
        let evaluation_of_weights = self.eval_constraints_poly(&round_constraints, folding_randomness.clone());

        let mut reversed_point = final_sumcheck_randomness.0;
        reversed_point.reverse();
        let final_value = eval_multilinear_coeffs(&final_coefficients, &reversed_point);
        if claimed_sum != evaluation_of_weights * final_value {
            return Err(ProofError::InvalidProof);
        }

        Ok(folding_randomness)
    }

    pub(crate) fn combine_constraints(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        claimed_sum: &mut EF,
        constraints: &[SparseStatement<EF>],
        has_previous_sum: bool,
    ) -> ProofResult<Vec<EF>> {
        let combination_randomness_gen: EF = verifier_state.sample();
        // The carried sum already has coefficient one. Fresh constraints must
        // use distinct powers so their errors cannot cancel it identically.
        let mut combination_randomness = vec![if has_previous_sum {
            combination_randomness_gen
        } else {
            EF::ONE
        }];
        for smt in constraints {
            for e in &smt.values {
                let combination_randomness_pow = *combination_randomness.last().unwrap();
                *claimed_sum += combination_randomness_pow * e.value;
                combination_randomness.push(combination_randomness_pow * combination_randomness_gen);
            }
        }
        combination_randomness.pop().unwrap();

        Ok(combination_randomness)
    }

    fn verify_stir_challenges<F>(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        params: &RoundConfig<EF>,
        commitment: &ParsedCommitment<F, EF>,
        folding_randomness: &MultilinearPoint<EF>,
        round_index: usize,
    ) -> ProofResult<Vec<SparseStatement<EF>>>
    where
        F: Field + ExtensionField<KoalaBear>,
        EF: ExtensionField<F>,
    {
        let leafs_base_field = round_index == 0;

        verifier_state.check_pow_grinding(params.query_pow_bits)?;

        let stir_challenges_indexes = get_challenge_stir_queries(
            params.domain_size >> params.folding_factor,
            params.num_queries,
            verifier_state,
        );

        // dbg!(&stir_challenges_indexes);
        // dbg!(verifier_state.challenger().state());

        let dimensions = [Dimensions {
            height: params.domain_size >> params.folding_factor,
            width: 1 << params.folding_factor,
        }];
        let answers = self.verify_merkle_proof::<F>(
            verifier_state,
            &commitment.root,
            &stir_challenges_indexes,
            &dimensions,
            leafs_base_field,
            round_index,
            0,
        )?;

        // Compute STIR Constraints
        let folds: Vec<_> = answers
            .into_iter()
            .map(|answers| answers.evaluate(folding_randomness))
            .collect();

        let stir_constraints = stir_challenges_indexes
            .iter()
            .map(|&index| params.folded_domain_gen.exp_u64(index as u64))
            .zip(&folds)
            .map(|(point, &value)| {
                SparseStatement::dense(
                    MultilinearPoint::expand_from_univariate(EF::from(point), params.num_variables),
                    value,
                )
            })
            .collect();

        Ok(stir_constraints)
    }

    fn verify_stir_challenges_linear_combination<F>(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        params: &RoundConfig<EF>,
        commitments: &[&ParsedCommitment<F, EF>],
        folding_randomness: &MultilinearPoint<EF>,
        polynomial_scalars: &[EF],
    ) -> ProofResult<Vec<SparseStatement<EF>>>
    where
        F: Field + ExtensionField<KoalaBear>,
        EF: ExtensionField<F>,
    {
        if commitments.len() != polynomial_scalars.len() {
            return Err(ProofError::InvalidProof);
        }
        verifier_state.check_pow_grinding(params.query_pow_bits)?;
        let indexes = get_challenge_stir_queries(
            params.domain_size >> params.folding_factor,
            params.num_queries,
            verifier_state,
        );
        let dimensions = [Dimensions {
            height: params.domain_size >> params.folding_factor,
            width: 1 << params.folding_factor,
        }];
        let mut folds = vec![EF::ZERO; indexes.len()];
        // Initial batches share indices and are encoded in commitment order.
        for (commitment, &scalar) in commitments.iter().zip(polynomial_scalars) {
            let answers =
                self.verify_merkle_proof::<F>(verifier_state, &commitment.root, &indexes, &dimensions, true, 0, 0)?;
            if answers.len() != folds.len() {
                return Err(ProofError::InvalidProof);
            }
            for (fold, answer) in folds.iter_mut().zip(answers) {
                *fold += scalar * answer.evaluate(folding_randomness);
            }
        }
        Ok(indexes
            .iter()
            .map(|&index| params.folded_domain_gen.exp_u64(index as u64))
            .zip(folds)
            .map(|(point, value)| {
                SparseStatement::dense(
                    MultilinearPoint::expand_from_univariate(EF::from(point), params.num_variables),
                    value,
                )
            })
            .collect())
    }

    #[allow(clippy::too_many_arguments)]
    fn verify_merkle_proof<F>(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        root: &[PF<EF>; DIGEST_ELEMS],
        indices: &[usize],
        dimensions: &[Dimensions],
        leafs_base_field: bool,
        _round_index: usize,
        _var_shift: usize,
    ) -> ProofResult<Vec<Vec<EF>>>
    where
        F: Field + ExtensionField<KoalaBear>,
        EF: ExtensionField<F>,
    {
        let merkle_height = log2_strict_usize(dimensions[0].height);
        let leaf_len = dimensions[0].width
            * if leafs_base_field {
                1
            } else {
                <EF as field::BasedVectorSpace<F>>::DIMENSION
            };
        verifier_state.begin_merkle_opening_batch(indices, merkle_height, leaf_len)?;
        let res = if leafs_base_field {
            let mut answers = Vec::<Vec<F>>::new();
            let mut merkle_proofs = Vec::new();

            for _ in 0..indices.len() {
                let opening = verifier_state.next_merkle_opening()?;
                answers.push(
                    try_pack_scalars_to_extension::<PF<EF>, F>(&opening.leaf_data).ok_or(ProofError::InvalidProof)?,
                );
                merkle_proofs.push(opening.path);
            }

            for (i, &index) in indices.iter().enumerate() {
                if !merkle_verify::<F>(
                    *root,
                    index,
                    dimensions[0],
                    answers[i].clone(),
                    &merkle_proofs[i],
                    verifier_state.hash_profile(),
                ) {
                    return Err(ProofError::InvalidProof);
                }
            }

            answers
                .into_iter()
                .map(|inner| inner.iter().map(|&f_el| f_el.into()).collect())
                .collect()
        } else {
            let mut answers = vec![];
            let mut merkle_proofs = Vec::new();

            for _ in 0..indices.len() {
                let opening = verifier_state.next_merkle_opening()?;
                answers.push(
                    try_pack_scalars_to_extension::<PF<EF>, EF>(&opening.leaf_data).ok_or(ProofError::InvalidProof)?,
                );
                merkle_proofs.push(opening.path);
            }

            for (i, &index) in indices.iter().enumerate() {
                if !merkle_verify::<EF>(
                    *root,
                    index,
                    dimensions[0],
                    answers[i].clone(),
                    &merkle_proofs[i],
                    verifier_state.hash_profile(),
                ) {
                    return Err(ProofError::InvalidProof);
                }
            }

            answers
        };

        Ok(res)
    }

    fn eval_constraints_poly(
        &self,
        constraints: &[(Vec<EF>, Vec<SparseStatement<EF>>)],
        mut point: MultilinearPoint<EF>,
    ) -> EF {
        let mut value = EF::ZERO;

        for (round, (randomness, constraints)) in constraints.iter().enumerate() {
            if round > 0 {
                let k = self.folding_factor.at_round(round - 1);
                point = MultilinearPoint(point[k..].to_vec());
            }
            let mut i = 0;
            for smt in constraints {
                let inner_point = &point[point.len() - smt.inner_num_variables()..];
                let common_weight = if smt.is_next {
                    next_mle(&smt.point.0, inner_point)
                } else {
                    smt.point.eq_poly_outside(&MultilinearPoint(inner_point.to_vec()))
                };
                for e in &smt.values {
                    let eval = (0..smt.selector_num_variables())
                        .map(|j| {
                            if e.selector & (1 << (smt.selector_num_variables() - 1 - j)) == 0 {
                                EF::ONE - point[j]
                            } else {
                                point[j]
                            }
                        })
                        .product::<EF>()
                        * common_weight;
                    value += eval * randomness[i];
                    i += 1;
                }
            }
            assert_eq!(i, randomness.len());
        }
        value
    }
}

fn statement_value_count<EF>(statement: &[SparseStatement<EF>]) -> usize {
    statement.iter().map(|constraint| constraint.values.len()).sum()
}

fn valid_initial_statement<EF>(statement: &[SparseStatement<EF>], num_variables: usize) -> bool {
    !statement.is_empty()
        && statement.iter().all(|constraint| {
            if constraint.total_num_variables != num_variables || constraint.values.is_empty() {
                return false;
            }
            let Some(selector_variables) = num_variables.checked_sub(constraint.inner_num_variables()) else {
                return false;
            };
            let Some(selector_limit) = 1usize.checked_shl(selector_variables as u32) else {
                return false;
            };
            constraint.values.iter().all(|value| value.selector < selector_limit)
        })
}

fn statement_coefficients<EF: Field>(statement: &[SparseStatement<EF>], gamma: EF, scale: EF) -> Vec<EF> {
    gamma
        .powers()
        .map(|coefficient| scale * coefficient)
        .take(statement_value_count(statement))
        .collect()
}

fn statement_value_sum<EF: Field>(statement: &[SparseStatement<EF>], coefficients: &[EF]) -> EF {
    assert_eq!(statement_value_count(statement), coefficients.len());
    statement
        .iter()
        .flat_map(|constraint| constraint.values.iter())
        .zip(coefficients)
        .map(|(value, &coefficient)| value.value * coefficient)
        .sum()
}

fn verify_constraint_coeffs<EF: Field>(constraint: &SparseStatement<EF>, coeffs: &[EF]) -> bool {
    assert_eq!(constraint.selector_num_variables(), 0);
    if constraint.point.is_empty() {
        return coeffs.len() == 1 && constraint.values.iter().all(|evaluation| evaluation.value == coeffs[0]);
    }
    let alpha = constraint.point[0];
    // Verify the point is expand_from_univariate(alpha, n): [alpha, alpha^2, alpha^4, ...]
    assert!(
        constraint
            .point
            .iter()
            .zip(constraint.point.iter().skip(1))
            .all(|(&a, &b)| a * a == b)
    );
    let univariate_eval = coeffs.iter().rfold(EF::ZERO, |acc, &c| acc * alpha + c);
    constraint.values.iter().all(|e| univariate_eval == e.value)
}

/// The full vector of folding randomness values, in reverse round order.
type SumcheckRandomness<F> = MultilinearPoint<F>;

pub(crate) fn verify_sumcheck_rounds<F, EF>(
    verifier_state: &mut impl FSVerifier<EF>,
    claimed_sum: &mut EF,
    rounds: usize,
    pow_bits: usize,
) -> ProofResult<SumcheckRandomness<EF>>
where
    F: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField + KoalaBearExtension,
{
    // Preallocate vector to hold the randomness values
    let mut randomness = Vec::with_capacity(rounds);

    for _ in 0..rounds {
        let coeffs = verifier_state.next_sumcheck_polynomial(3, *claimed_sum, None)?;
        let poly = DensePolynomial::new(coeffs);

        verifier_state.check_pow_grinding(pow_bits)?;

        // Sample the next verifier folding randomness rᵢ
        let rand: EF = verifier_state.sample();

        // Update claimed sum using folding randomness
        *claimed_sum = poly.evaluate(rand);

        // Store this round’s randomness
        randomness.push(rand);
    }

    Ok(MultilinearPoint(randomness))
}

#[cfg(test)]
mod coefficient_tests {
    use super::*;
    use fiat_shamir::{ProverState, VerifierState};
    use koala_bear::{QuinticExtensionFieldKB, default_koalabear_poseidon1_16};

    #[test]
    fn continuation_batching_keeps_carried_and_fresh_residuals_distinct() {
        type EF = QuinticExtensionFieldKB;
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
            13,
        );
        let new_verifier = || {
            let permutation = default_koalabear_poseidon1_16();
            let capacity = [KoalaBear::ZERO; 8];
            let prover = ProverState::<EF, _>::new(permutation.clone(), capacity);
            let mut verifier = VerifierState::<EF, _>::new(prover.into_proof(), permutation, capacity).unwrap();
            verifier.duplex();
            verifier
        };
        let values = [EF::from_u32(19), EF::from_u32(23), EF::from_u32(31)];
        let constraints: Vec<_> = values
            .iter()
            .map(|&value| SparseStatement::dense(MultilinearPoint(vec![EF::ZERO; 13]), value))
            .collect();
        let carry = EF::from_u32(11);
        let error = EF::from_u32(7);
        let mut altered = constraints.clone();
        altered[0].values[0].value -= error;

        let mut initial_sum = EF::ZERO;
        let initial_coefficients = config
            .combine_constraints(&mut new_verifier(), &mut initial_sum, &constraints, false)
            .unwrap();
        assert_eq!(initial_coefficients[0], EF::ONE);
        let gamma = initial_coefficients[1];
        assert_ne!(gamma, EF::ONE);

        let mut true_sum = carry;
        let coefficients = config
            .combine_constraints(&mut new_verifier(), &mut true_sum, &constraints, true)
            .unwrap();
        assert_eq!(
            coefficients,
            gamma.powers().skip(1).take(values.len()).collect::<Vec<_>>()
        );
        let mut altered_sum = carry + error;
        let altered_coefficients = config
            .combine_constraints(&mut new_verifier(), &mut altered_sum, &altered, true)
            .unwrap();
        assert_eq!(altered_coefficients, coefficients);
        assert_eq!(altered_sum - true_sum, error * (EF::ONE - gamma));
        assert_ne!(altered_sum, true_sum);

        // Reusing the initial weights for a continuation recreates the old cancellation.
        let mut unchecked_true = carry;
        let mut unchecked_altered = carry + error;
        config
            .combine_constraints(&mut new_verifier(), &mut unchecked_true, &constraints, false)
            .unwrap();
        config
            .combine_constraints(&mut new_verifier(), &mut unchecked_altered, &altered, false)
            .unwrap();
        assert_eq!(unchecked_true, unchecked_altered);
    }

    #[test]
    fn constant_final_polynomial_checks_its_claim_and_length() {
        let statement = SparseStatement::dense(MultilinearPoint(Vec::<KoalaBear>::new()), KoalaBear::ONE);
        assert!(verify_constraint_coeffs(&statement, &[KoalaBear::ONE]));
        assert!(!verify_constraint_coeffs(&statement, &[KoalaBear::ZERO]));
        assert!(!verify_constraint_coeffs(&statement, &[]));
        assert!(!verify_constraint_coeffs(
            &statement,
            &[KoalaBear::ONE, KoalaBear::ZERO]
        ));
    }
}
