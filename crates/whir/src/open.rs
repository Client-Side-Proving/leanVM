// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use ::utils::log2_strict_usize;
use fiat_shamir::{FSProver, MerklePath, ProofResult};
use field::PrimeCharacteristicRing;
use field::{Field, TwoAdicField};
use sumcheck::{
    ProductComputation, packing_unpack_sum, run_product_sumcheck, run_product_sumcheck_from_round1,
    run_product_sumcheck_from_round2_delayed, sumcheck_prove_many_rounds,
};
use tracing::{info_span, instrument};
use zk_alloc::ArenaVec;

use crate::{config::WhirConfig, *};

impl<EF> WhirConfig<EF>
where
    EF: KoalaBearExtension,
{
    fn validate_parameters(&self) -> bool {
        self.num_variables == self.folding_factor.total_number(self.n_rounds()) + self.final_sumcheck_rounds
    }

    fn validate_statement(&self, statement: &[SparseStatement<EF>]) {
        statement.iter().for_each(|e| {
            assert_eq!(e.total_num_variables, self.num_variables);
            assert!(!e.values.is_empty());
            assert!(e.values.iter().all(|v| v.selector < 1 << e.selector_num_variables()));
        });
    }

    fn validate_witness(&self, witness: &Witness<EF>, polynomial: &MleRef<'_, EF>) -> bool {
        assert_eq!(witness.ood_points.len(), witness.ood_answers.len());
        polynomial.n_vars() == self.num_variables
    }

    #[instrument(name = "WHIR prove", skip_all)]
    pub fn prove(
        &self,
        prover_state: &mut impl FSProver<EF>,
        statement: Vec<SparseStatement<EF>>,
        witness: Witness<EF>,
        polynomial: &MleRef<'_, EF>,
    ) -> MultilinearPoint<EF> {
        assert!(self.validate_parameters());
        assert!(self.validate_witness(&witness, polynomial));
        self.validate_statement(&statement);

        let mut round_state =
            RoundState::initialize_first_round_state(self, prover_state, statement, witness, polynomial).unwrap();

        for round in 0..=self.n_rounds() {
            self.round(round, prover_state, &mut round_state).unwrap();
        }

        MultilinearPoint(round_state.randomness_vec)
    }

    /// Prove while reconstructing a discarded first-round commitment leaf only
    /// after the initial sumcheck has folded the committed polynomial.
    #[instrument(name = "WHIR prove", skip_all)]
    pub fn prove_rebuilding_commitment_leaf(
        &self,
        prover_state: &mut impl FSProver<EF>,
        statement: Vec<SparseStatement<EF>>,
        witness: Witness<EF>,
        polynomial: MleOwned<EF>,
        actual_data_len: usize,
    ) -> MultilinearPoint<EF> {
        assert!(self.validate_parameters());
        assert!(self.validate_witness(&witness, &polynomial.by_ref()));
        self.validate_statement(&statement);

        let mut round_state =
            RoundState::initialize_first_round_state(self, prover_state, statement, witness, &polynomial.by_ref())
                .unwrap();

        self.rebuild_commitment_leaf(&polynomial, actual_data_len, &mut round_state.merkle_prover_data);
        drop(polynomial);

        for round in 0..=self.n_rounds() {
            self.round(round, prover_state, &mut round_state).unwrap();
        }

        MultilinearPoint(round_state.randomness_vec)
    }

    /// Proves two separately committed base-field polynomials through one WHIR
    /// continuation. The commitment roots must already be observed without the
    /// ordinary per-commitment OOD step. The caller must bind this proof shape
    /// and `batching_pow_bits` in its protocol domain separator.
    #[instrument(name = "WHIR prove two commitments", skip_all)]
    #[allow(clippy::too_many_arguments)]
    pub fn prove_two_commitments(
        &self,
        prover_state: &mut impl FSProver<EF>,
        batching_pow_bits: usize,
        primary_statement: Vec<SparseStatement<EF>>,
        primary_witness: Witness<EF>,
        primary_polynomial: &MleRef<'_, EF>,
        secondary_statement: Vec<SparseStatement<EF>>,
        secondary_witness: Witness<EF>,
        secondary_polynomial: &MleRef<'_, EF>,
    ) -> MultilinearPoint<EF> {
        assert!(self.validate_parameters());
        assert!(
            self.n_rounds() > 0,
            "two-commitment WHIR requires an intermediate commitment round"
        );
        assert!(
            self.commitment_ood_samples > 0,
            "two-commitment WHIR requires a combined OOD check"
        );
        assert!(self.validate_witness(&primary_witness, primary_polynomial));
        assert!(self.validate_witness(&secondary_witness, secondary_polynomial));
        assert!(primary_witness.ood_points.is_empty() && primary_witness.ood_answers.is_empty());
        assert!(secondary_witness.ood_points.is_empty() && secondary_witness.ood_answers.is_empty());
        assert!(!primary_statement.is_empty() && !secondary_statement.is_empty());
        self.validate_statement(&primary_statement);
        self.validate_statement(&secondary_statement);

        prover_state.duplex();
        let group_randomness: EF = prover_state.sample();
        let primary_terms = build_lazy_combine_terms::<EF>(&primary_statement, group_randomness);
        let secondary_terms = build_lazy_combine_terms::<EF>(&secondary_statement, group_randomness);
        let primary_sum = primary_terms.combined_sum;
        let secondary_sum = secondary_terms.combined_sum;
        let primary_on_secondary = weighted_sum_base_polynomial(secondary_polynomial, &primary_terms);
        let secondary_on_primary = weighted_sum_base_polynomial(primary_polynomial, &secondary_terms);

        prover_state.add_extension_scalars(&[primary_on_secondary, secondary_on_primary]);
        prover_state.pow_grinding(batching_pow_bits);
        // The grinding predicate constrains one transcript output. Duplex before
        // lambda so its extension-field distribution is the ordinary sampler's.
        prover_state.duplex();
        let polynomial_randomness: EF = prover_state.sample();
        let combined_polynomial =
            linear_combination_base_polynomials(primary_polynomial, secondary_polynomial, polynomial_randomness);

        prover_state.duplex();
        let (combined_ood_points, combined_ood_answers) =
            sample_ood_points::<EF, _>(prover_state, self.commitment_ood_samples, self.num_variables, |point| {
                combined_polynomial.evaluate(point)
            });
        let combined_ood_statements = combined_ood_points
            .iter()
            .copied()
            .zip(combined_ood_answers.iter().copied())
            .map(|(point, evaluation)| {
                SparseStatement::dense(
                    MultilinearPoint::expand_from_univariate(point, self.num_variables),
                    evaluation,
                )
            })
            .collect::<Vec<_>>();

        prover_state.duplex();
        let statement_randomness: EF = prover_state.sample();
        let statement_scales = statement_randomness
            .powers()
            .collect_n(combined_ood_statements.len() + 2);
        let primary_scale = statement_scales[combined_ood_statements.len()];
        let secondary_scale = statement_scales[combined_ood_statements.len() + 1];
        let combined_ood_terms = build_lazy_combine_terms::<EF>(&combined_ood_statements, statement_randomness);
        let combined_weights = materialize_scaled_weights(
            &[
                (&combined_ood_terms, EF::ONE),
                (&primary_terms, primary_scale),
                (&secondary_terms, secondary_scale),
            ],
            combined_polynomial.by_ref().packed_len(),
        );
        let claimed_sum = combined_ood_terms.combined_sum
            + primary_scale * (primary_sum + polynomial_randomness * primary_on_secondary)
            + secondary_scale * (secondary_on_primary + polynomial_randomness * secondary_sum);

        let mut round_state = RoundState::initialize_linear_combination_first_round_state(
            self,
            prover_state,
            primary_witness,
            vec![(secondary_witness, polynomial_randomness)],
            &combined_polynomial.by_ref(),
            combined_weights,
            claimed_sum,
        )
        .unwrap();

        for round in 0..=self.n_rounds() {
            self.round(round, prover_state, &mut round_state).unwrap();
        }

        MultilinearPoint(round_state.randomness_vec)
    }

    /// Open three separately committed base-field polynomials through one
    /// continuation. Roots and claims must be bound before this call. The
    /// caller also binds the protocol mode and its batching grinding budget.
    #[instrument(name = "WHIR prove three commitments", skip_all)]
    pub fn prove_three_commitments(
        &self,
        prover_state: &mut impl FSProver<EF>,
        batching_pow_bits: usize,
        statements: [Vec<SparseStatement<EF>>; 3],
        witnesses: [Witness<EF>; 3],
        polynomials: [&MleRef<'_, EF>; 3],
    ) -> MultilinearPoint<EF> {
        assert!(self.validate_parameters());
        assert!(self.n_rounds() > 0 && self.commitment_ood_samples > 0);
        for i in 0..3 {
            assert!(self.validate_witness(&witnesses[i], polynomials[i]));
            assert!(witnesses[i].ood_points.is_empty() && witnesses[i].ood_answers.is_empty());
            assert!(!statements[i].is_empty());
            self.validate_statement(&statements[i]);
        }
        prover_state.duplex();
        let group_randomness = prover_state.sample();
        let terms = statements
            .each_ref()
            .map(|group| build_lazy_combine_terms::<EF>(group, group_randomness));
        let mut cross = [[EF::ZERO; 3]; 3];
        let mut cross_values = Vec::with_capacity(6);
        for i in 0..3 {
            for j in 0..3 {
                cross[i][j] = if i == j {
                    terms[i].combined_sum
                } else {
                    let value = weighted_sum_base_polynomial(polynomials[j], &terms[i]);
                    cross_values.push(value);
                    value
                };
            }
        }
        // Row-major off-diagonal L_i(P_j), fixed before polynomial batching.
        prover_state.add_extension_scalars(&cross_values);
        prover_state.pow_grinding(batching_pow_bits);
        prover_state.duplex();
        let lambda: EF = prover_state.sample();
        let scalars = [EF::ONE, lambda, lambda.square()];
        let combined_polynomial = linear_combination_three_base_polynomials(polynomials, scalars);

        prover_state.duplex();
        let (ood_points, ood_answers) =
            sample_ood_points::<EF, _>(prover_state, self.commitment_ood_samples, self.num_variables, |point| {
                combined_polynomial.evaluate(point)
            });
        let ood_statements = ood_points
            .iter()
            .zip(&ood_answers)
            .map(|(&point, &value)| {
                SparseStatement::dense(
                    MultilinearPoint::expand_from_univariate(point, self.num_variables),
                    value,
                )
            })
            .collect::<Vec<_>>();
        prover_state.duplex();
        let theta: EF = prover_state.sample();
        let scales = theta.powers().collect_n(ood_statements.len() + 3);
        let ood_terms = build_lazy_combine_terms::<EF>(&ood_statements, theta);
        let mut weighted_terms = vec![(&ood_terms, EF::ONE)];
        let mut claimed_sum = ood_terms.combined_sum;
        for i in 0..3 {
            let scale = scales[ood_statements.len() + i];
            weighted_terms.push((&terms[i], scale));
            claimed_sum += scale * (0..3).map(|j| scalars[j] * cross[i][j]).sum::<EF>();
        }
        let weights = materialize_scaled_weights(&weighted_terms, combined_polynomial.by_ref().packed_len());
        let [primary, secondary, helper] = witnesses;
        let mut round_state = RoundState::initialize_linear_combination_first_round_state(
            self,
            prover_state,
            primary,
            vec![(secondary, scalars[1]), (helper, scalars[2])],
            &combined_polynomial.by_ref(),
            weights,
            claimed_sum,
        )
        .unwrap();
        for round in 0..=self.n_rounds() {
            self.round(round, prover_state, &mut round_state).unwrap();
        }
        MultilinearPoint(round_state.randomness_vec)
    }

    fn round(
        &self,
        round_index: usize,
        prover_state: &mut impl FSProver<EF>,
        round_state: &mut RoundState<EF>,
    ) -> ProofResult<()> {
        let folded_evaluations = &round_state.sumcheck_prover.evals;
        let num_variables = self.num_variables - self.folding_factor.total_number(round_index);

        // Base case: final round reached
        if round_index == self.n_rounds() {
            return self.final_round(round_index, prover_state, round_state);
        }

        let round_params = &self.round_parameters[round_index];

        // Compute the folding factors for later use
        let folding_factor_next = self.folding_factor.at_round(round_index + 1);

        // Compute polynomial evaluations and build Merkle tree
        let domain_reduction = 1 << self.rs_reduction_factor(round_index);
        let new_domain_size = round_state.domain_size / domain_reduction;
        let inv_rate = new_domain_size >> num_variables;
        let folded_matrix = info_span!("FFT").in_scope(|| {
            reorder_and_dft(
                &folded_evaluations.by_ref(),
                folding_factor_next,
                log2_strict_usize(inv_rate),
                1 << folding_factor_next,
            )
        });

        let full = 1 << folding_factor_next;
        let (prover_data, root) = MerkleData::build(folded_matrix, full, full, prover_state.hash_profile());

        prover_state.add_base_scalars(&root);

        // Handle OOD (Out-Of-Domain) samples
        let (ood_points, ood_answers) =
            sample_ood_points::<EF, _>(prover_state, round_params.ood_samples, num_variables, |point| {
                info_span!("ood evaluation").in_scope(|| folded_evaluations.evaluate(point))
            });

        prover_state.pow_grinding(round_params.query_pow_bits);

        let (ood_challenges, stir_challenges, stir_challenges_indexes) = self.compute_stir_queries(
            prover_state,
            round_state,
            num_variables,
            round_params,
            &ood_points,
            round_index,
        )?;

        let folding_randomness = round_state.folding_randomness(
            self.folding_factor.at_round(round_index) + round_state.commitment_merkle_prover_data_b.is_some() as usize,
        );

        let stir_evaluations = if !round_state.linear_combination_merkle_prover_data.is_empty() {
            let answers_a =
                open_merkle_tree_at_challenges(&round_state.merkle_prover_data, prover_state, &stir_challenges_indexes);
            let mut values = answers_a
                .iter()
                .map(|answer| answer.evaluate(&folding_randomness))
                .collect::<Vec<_>>();
            for (data, scalar) in &round_state.linear_combination_merkle_prover_data {
                let answers = open_merkle_tree_at_challenges(data, prover_state, &stir_challenges_indexes);
                assert_eq!(values.len(), answers.len());
                for (value, answer) in values.iter_mut().zip(&answers) {
                    *value += *scalar * answer.evaluate(&folding_randomness);
                }
            }
            values
        } else if let Some(data_b) = &round_state.commitment_merkle_prover_data_b {
            let answers_a =
                open_merkle_tree_at_challenges(&round_state.merkle_prover_data, prover_state, &stir_challenges_indexes);
            let answers_b = open_merkle_tree_at_challenges(data_b, prover_state, &stir_challenges_indexes);
            let mut stir_evaluations = Vec::new();
            for (answer_a, answer_b) in answers_a.iter().zip(&answers_b) {
                let vars_a = answer_a.by_ref().n_vars();
                let vars_b = answer_b.by_ref().n_vars();
                let a_trunc = folding_randomness[1..].to_vec();
                let eval_a = answer_a.evaluate(&MultilinearPoint(a_trunc));
                let b_trunc = folding_randomness[vars_a - vars_b + 1..].to_vec();
                let eval_b = answer_b.evaluate(&MultilinearPoint(b_trunc));
                let last_fold_rand_a = folding_randomness[0];
                let last_fold_rand_b = folding_randomness[..vars_a - vars_b + 1]
                    .iter()
                    .map(|&x| EF::ONE - x)
                    .product::<EF>();
                stir_evaluations.push(eval_a * last_fold_rand_a + eval_b * last_fold_rand_b);
            }

            stir_evaluations
        } else {
            open_merkle_tree_at_challenges(&round_state.merkle_prover_data, prover_state, &stir_challenges_indexes)
                .iter()
                .map(|answer| answer.evaluate(&folding_randomness))
                .collect()
        };

        // Randomness for combination
        prover_state.duplex();
        let combination_randomness_gen: EF = prover_state.sample();
        // Reserve coefficient one for the carried sumcheck claim and weights.
        let ood_combination_randomness: Vec<_> = combination_randomness_gen
            .powers()
            .skip(1)
            .take(ood_challenges.len())
            .collect();
        round_state
            .sumcheck_prover
            .add_new_equality(&ood_challenges, &ood_answers, &ood_combination_randomness);
        let stir_combination_randomness = combination_randomness_gen
            .powers()
            .skip(ood_challenges.len() + 1)
            .take(stir_challenges.len())
            .collect::<Vec<_>>();

        round_state.sumcheck_prover.add_new_base_equality(
            &stir_challenges,
            &stir_evaluations,
            &stir_combination_randomness,
        );

        let next_folding_randomness = round_state.sumcheck_prover.run_sumcheck_many_rounds(
            None,
            prover_state,
            folding_factor_next,
            round_params.folding_pow_bits,
        );

        round_state.randomness_vec.extend_from_slice(&next_folding_randomness.0);

        // Update round state
        round_state.domain_size = new_domain_size;
        round_state.next_domain_gen =
            PF::<EF>::two_adic_generator(log2_strict_usize(new_domain_size) - folding_factor_next);
        round_state.merkle_prover_data = prover_data;
        round_state.commitment_merkle_prover_data_b = None;
        round_state.linear_combination_merkle_prover_data.clear();

        Ok(())
    }

    fn final_round(
        &self,
        round_index: usize,
        prover_state: &mut impl FSProver<EF>,
        round_state: &mut RoundState<EF>,
    ) -> ProofResult<()> {
        // Convert evaluations to coefficient form and send to the verifier.
        let mut coeffs = match &round_state.sumcheck_prover.evals {
            MleOwned::Extension(evals) => evals.clone(),
            MleOwned::ExtensionPacked(evals) => unpack_extension(evals),
            _ => unreachable!(),
        };
        evals_to_coeffs(&mut coeffs);
        prover_state.add_extension_scalars(&coeffs);

        prover_state.pow_grinding(self.final_query_pow_bits);

        // Final verifier queries and answers. The indices are over the folded domain.
        let final_challenge_indexes = get_challenge_stir_queries(
            // The size of the original domain before folding
            round_state.domain_size >> self.folding_factor.at_round(round_index),
            self.final_queries,
            prover_state,
        );

        let mut base_paths = Vec::new();
        let mut ext_paths = Vec::new();
        for challenge in final_challenge_indexes {
            let (answer, sibling_hashes) = round_state.merkle_prover_data.open(challenge);

            match answer {
                MleOwned::Base(leaf) => {
                    base_paths.push(MerklePath {
                        leaf_data: leaf.to_vec(),
                        sibling_hashes,
                        leaf_index: challenge,
                    });
                }
                MleOwned::Extension(leaf) => {
                    ext_paths.push(MerklePath {
                        leaf_data: leaf.to_vec(),
                        sibling_hashes,
                        leaf_index: challenge,
                    });
                }
                _ => unreachable!(),
            }
        }
        if !base_paths.is_empty() {
            prover_state.hint_merkle_paths_base(base_paths);
        }
        if !ext_paths.is_empty() {
            prover_state.hint_merkle_paths_extension(ext_paths);
        }

        // Run final sumcheck if required
        if self.final_sumcheck_rounds > 0 {
            let final_folding_randomness =
                round_state
                    .sumcheck_prover
                    .run_sumcheck_many_rounds(None, prover_state, self.final_sumcheck_rounds, 0);

            round_state.randomness_vec.extend(final_folding_randomness.0);
        }

        Ok(())
    }

    #[allow(clippy::type_complexity)]
    fn compute_stir_queries(
        &self,
        prover_state: &mut impl FSProver<EF>,
        round_state: &RoundState<EF>,
        num_variables: usize,
        round_params: &RoundConfig<EF>,
        ood_points: &[EF],
        round_index: usize,
    ) -> ProofResult<(Vec<MultilinearPoint<EF>>, Vec<MultilinearPoint<PF<EF>>>, Vec<usize>)> {
        let stir_challenges_indexes = get_challenge_stir_queries(
            round_state.domain_size >> self.folding_factor.at_round(round_index),
            round_params.num_queries,
            prover_state,
        );

        let domain_scaled_gen = round_state.next_domain_gen;
        let ood_challenges = ood_points
            .iter()
            .map(|univariate| MultilinearPoint::expand_from_univariate(*univariate, num_variables))
            .collect();
        let stir_challenges = stir_challenges_indexes
            .iter()
            .map(|i| MultilinearPoint::expand_from_univariate(domain_scaled_gen.exp_u64(*i as u64), num_variables))
            .collect();

        Ok((ood_challenges, stir_challenges, stir_challenges_indexes))
    }
}

fn open_merkle_tree_at_challenges<EF: KoalaBearExtension>(
    merkle_tree: &MerkleData<EF>,
    prover_state: &mut impl FSProver<EF>,
    stir_challenges_indexes: &[usize],
) -> Vec<MleOwned<EF>> {
    let mut answers = Vec::new();
    let mut base_paths = Vec::new();
    let mut ext_paths = Vec::new();

    for &challenge in stir_challenges_indexes {
        let (answer, sibling_hashes) = merkle_tree.open(challenge);

        match &answer {
            MleOwned::Base(leaf) => {
                base_paths.push(MerklePath {
                    leaf_data: leaf.to_vec(),
                    sibling_hashes,
                    leaf_index: challenge,
                });
            }
            MleOwned::Extension(leaf) => {
                ext_paths.push(MerklePath {
                    leaf_data: leaf.to_vec(),
                    sibling_hashes,
                    leaf_index: challenge,
                });
            }
            _ => unreachable!(),
        }
        answers.push(answer);
    }

    if !base_paths.is_empty() {
        prover_state.hint_merkle_paths_base(base_paths);
    }
    if !ext_paths.is_empty() {
        prover_state.hint_merkle_paths_extension(ext_paths);
    }

    answers
}

fn weighted_sum_base_polynomial<EF: KoalaBearExtension>(
    polynomial: &MleRef<'_, EF>,
    terms: &LazyCombineTerms<EF>,
) -> EF {
    let packed = polynomial.pack();
    let packed_ref = packed.by_ref();
    let evals = packed_ref
        .as_packed_base()
        .expect("two-commitment WHIR currently requires base-field polynomials");
    let mut packed_sum = parallel::map_reduce(
        evals.len(),
        || EFPacking::<EF>::ZERO,
        |index| terms.value_at(index) * evals[index],
        |left, right| left + right,
    );
    for &(index, delta) in &terms.overlay {
        packed_sum += delta * evals[index];
    }
    packing_unpack_sum::<EF>(packed_sum)
}

fn linear_combination_base_polynomials<EF: KoalaBearExtension>(
    primary: &MleRef<'_, EF>,
    secondary: &MleRef<'_, EF>,
    scalar: EF,
) -> MleOwned<EF> {
    assert_eq!(primary.n_vars(), secondary.n_vars());
    let primary_packed = primary.pack();
    let secondary_packed = secondary.pack();
    let primary_ref = primary_packed.by_ref();
    let secondary_ref = secondary_packed.by_ref();
    let primary_values = primary_ref
        .as_packed_base()
        .expect("two-commitment WHIR currently requires base-field polynomials");
    let secondary_values = secondary_ref
        .as_packed_base()
        .expect("two-commitment WHIR currently requires base-field polynomials");
    assert_eq!(primary_values.len(), secondary_values.len());
    let scalar = EFPacking::<EF>::from(scalar);
    MleOwned::ExtensionPacked(ArenaVec::par_collect(primary_values.len(), |index| {
        EFPacking::<EF>::from(primary_values[index]) + scalar * secondary_values[index]
    }))
}

fn linear_combination_three_base_polynomials<EF: KoalaBearExtension>(
    polynomials: [&MleRef<'_, EF>; 3],
    scalars: [EF; 3],
) -> MleOwned<EF> {
    assert!(polynomials.iter().all(|p| p.n_vars() == polynomials[0].n_vars()));
    let packed = polynomials.map(|polynomial| polynomial.pack());
    let refs = packed.each_ref().map(|polynomial| polynomial.by_ref());
    let values = refs
        .each_ref()
        .map(|polynomial| polynomial.as_packed_base().expect("base-field polynomial required"));
    let scalars = scalars.map(EFPacking::<EF>::from);
    MleOwned::ExtensionPacked(ArenaVec::par_collect(values[0].len(), |index| {
        (0..3).map(|j| scalars[j] * values[j][index]).sum()
    }))
}

#[derive(Debug, Clone)]
pub struct SumcheckSingle<EF: KoalaBearExtension> {
    /// Evaluations of the polynomial `p(X)`.
    pub(crate) evals: MleOwned<EF>,
    /// Evaluations of the equality polynomial used for enforcing constraints.
    pub(crate) weights: MleOwned<EF>,
    /// Accumulated sum incorporating equality constraints.
    pub(crate) sum: EF,
}

impl<EF: Field> SumcheckSingle<EF>
where
    EF: KoalaBearExtension,
{
    #[instrument(skip_all)]
    pub(crate) fn add_new_equality(
        &mut self,
        points: &[MultilinearPoint<EF>],
        evaluations: &[EF],
        combination_randomness: &[EF],
    ) {
        assert_eq!(combination_randomness.len(), points.len());
        assert_eq!(evaluations.len(), points.len());

        points
            .iter()
            .zip(combination_randomness.iter())
            .for_each(|(point, &rand)| {
                compute_eval_eq_packed::<_, true>(point, self.weights.as_extension_packed_mut().unwrap(), rand);
            });

        self.sum += combination_randomness
            .iter()
            .zip(evaluations.iter())
            .map(|(&rand, &eval)| rand * eval)
            .sum::<EF>();
    }

    #[instrument(skip_all)]
    pub(crate) fn add_new_base_equality(
        &mut self,
        points: &[MultilinearPoint<PF<EF>>],
        evaluations: &[EF],
        combination_randomness: &[EF],
    ) {
        assert_eq!(combination_randomness.len(), points.len());
        assert_eq!(evaluations.len(), points.len());

        compute_eval_eq_base_packed_batched::<PF<EF>, EF>(
            points,
            self.weights.as_extension_packed_mut().unwrap(),
            combination_randomness,
        );

        // Accumulate the weighted sum (cheap, done sequentially)
        self.sum += combination_randomness
            .iter()
            .zip(evaluations.iter())
            .map(|(&rand, &eval)| rand * eval)
            .sum::<EF>();
    }

    fn run_sumcheck_many_rounds(
        &mut self,
        prev_folding_scalar: Option<EF>,
        prover_state: &mut impl FSProver<EF>,
        n_rounds: usize,
        pow_bits: usize,
    ) -> MultilinearPoint<EF> {
        let (challenges, folds, new_sum) = sumcheck_prove_many_rounds(
            MleGroupRef::merge(&[&self.evals.by_ref(), &self.weights.by_ref()]),
            prev_folding_scalar,
            &ProductComputation {},
            &vec![],
            None,
            prover_state,
            self.sum,
            None,
            n_rounds,
            false,
            pow_bits,
        );

        self.sum = new_sum;
        [self.evals, self.weights] = folds.split().try_into().unwrap();

        challenges
    }

    #[instrument(skip_all)]
    pub(crate) fn run_initial_sumcheck_rounds(
        evals: &MleRef<'_, EF>,
        statement: &[SparseStatement<EF>],
        combination_randomness: EF,
        prover_state: &mut impl FSProver<EF>,
        folding_factor: usize,
        pow_bits: usize,
    ) -> (Self, MultilinearPoint<EF>) {
        assert_ne!(folding_factor, 0);

        let evals = evals.pack();

        let MleRef::BasePacked(ev) = evals.by_ref() else {
            unreachable!("we always commit in the base field");
        };

        let terms = info_span!("build_lazy_combine_terms")
            .in_scope(|| build_lazy_combine_terms::<EF>(statement, combination_randomness));
        let first_poly = info_span!("compute_first_round").in_scope(|| compute_first_round(ev, &terms));
        prover_state.add_sumcheck_polynomial(&first_poly.coeffs, None);
        prover_state.pow_grinding(pow_bits);
        let r1: EF = prover_state.sample();
        let sum1 = first_poly.evaluate(r1);
        let (challenges, new_sum, folded_evals, folded_weights) = if folding_factor >= 4 {
            let (second_poly, folded_weights) = info_span!("compute_second_round_and_fold_weights")
                .in_scope(|| compute_second_round_and_fold_weights(ev, &terms, r1, sum1));
            run_product_sumcheck_from_round2_delayed(
                ev,
                folded_weights,
                prover_state,
                r1,
                second_poly,
                folding_factor,
                pow_bits,
            )
        } else {
            let weights_buf = materialize_weights(&terms, ev.len());
            let weights = Mle::Owned(MleOwned::ExtensionPacked(weights_buf));
            run_product_sumcheck_from_round1(
                &evals.by_ref(),
                &weights.by_ref(),
                prover_state,
                r1,
                sum1,
                folding_factor,
                pow_bits,
            )
        };
        (
            Self {
                evals: folded_evals,
                weights: folded_weights,
                sum: new_sum,
            },
            challenges,
        )
    }

    #[instrument(skip_all)]
    fn run_initial_sumcheck_rounds_materialized(
        evals: &MleRef<'_, EF>,
        weights: MleOwned<EF>,
        claimed_sum: EF,
        prover_state: &mut impl FSProver<EF>,
        folding_factor: usize,
        pow_bits: usize,
    ) -> (Self, MultilinearPoint<EF>) {
        assert_ne!(folding_factor, 0);
        let evals = evals.pack();
        let weights = weights.pack();
        let (challenges, new_sum, folded_evals, folded_weights) = run_product_sumcheck(
            &evals.by_ref(),
            &weights.by_ref(),
            prover_state,
            claimed_sum,
            folding_factor,
            pow_bits,
        );
        (
            Self {
                evals: folded_evals,
                weights: folded_weights,
                sum: new_sum,
            },
            challenges,
        )
    }
}

#[derive(Debug)]
pub(crate) struct RoundState<EF>
where
    EF: KoalaBearExtension,
{
    domain_size: usize,
    next_domain_gen: PF<EF>,
    sumcheck_prover: SumcheckSingle<EF>,
    commitment_merkle_prover_data_b: Option<MerkleData<EF>>,
    linear_combination_merkle_prover_data: Vec<(MerkleData<EF>, EF)>,
    merkle_prover_data: MerkleData<EF>,
    randomness_vec: Vec<EF>,
}

#[allow(clippy::mismatching_type_param_order)]
impl<EF> RoundState<EF>
where
    EF: KoalaBearExtension,
{
    pub(crate) fn initialize_first_round_state(
        prover: &WhirConfig<EF>,
        prover_state: &mut impl FSProver<EF>,
        mut statement: Vec<SparseStatement<EF>>,
        witness: Witness<EF>,
        polynomial: &MleRef<'_, EF>,
    ) -> ProofResult<Self> {
        let ood_statements = witness
            .ood_points
            .into_iter()
            .zip(witness.ood_answers)
            .map(|(point, evaluation)| {
                SparseStatement::dense(
                    MultilinearPoint::expand_from_univariate(point, prover.num_variables),
                    evaluation,
                )
            })
            .collect::<Vec<_>>();

        statement.splice(0..0, ood_statements);

        prover_state.duplex();
        let combination_randomness_gen: EF = prover_state.sample();

        let (sumcheck_prover, folding_randomness) = SumcheckSingle::run_initial_sumcheck_rounds(
            polynomial,
            &statement,
            combination_randomness_gen,
            prover_state,
            prover.folding_factor.at_round(0),
            prover.starting_folding_pow_bits,
        );

        Ok(Self {
            domain_size: prover.starting_domain_size(),
            next_domain_gen: PF::<EF>::two_adic_generator(
                log2_strict_usize(prover.starting_domain_size()) - prover.folding_factor.at_round(0),
            ),
            sumcheck_prover,
            merkle_prover_data: witness.prover_data,
            commitment_merkle_prover_data_b: None,
            linear_combination_merkle_prover_data: Vec::new(),
            randomness_vec: folding_randomness.0.clone(),
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn initialize_linear_combination_first_round_state(
        prover: &WhirConfig<EF>,
        prover_state: &mut impl FSProver<EF>,
        primary_witness: Witness<EF>,
        additional_witnesses: Vec<(Witness<EF>, EF)>,
        combined_polynomial: &MleRef<'_, EF>,
        combined_weights: MleOwned<EF>,
        claimed_sum: EF,
    ) -> ProofResult<Self> {
        let (sumcheck_prover, folding_randomness) = SumcheckSingle::run_initial_sumcheck_rounds_materialized(
            combined_polynomial,
            combined_weights,
            claimed_sum,
            prover_state,
            prover.folding_factor.at_round(0),
            prover.starting_folding_pow_bits,
        );
        Ok(Self {
            domain_size: prover.starting_domain_size(),
            next_domain_gen: PF::<EF>::two_adic_generator(
                log2_strict_usize(prover.starting_domain_size()) - prover.folding_factor.at_round(0),
            ),
            sumcheck_prover,
            merkle_prover_data: primary_witness.prover_data,
            commitment_merkle_prover_data_b: None,
            linear_combination_merkle_prover_data: additional_witnesses
                .into_iter()
                .map(|(witness, scalar)| (witness.prover_data, scalar))
                .collect(),
            randomness_vec: folding_randomness.0.clone(),
        })
    }

    fn folding_randomness(&self, folding_factor: usize) -> MultilinearPoint<EF> {
        MultilinearPoint(self.randomness_vec[self.randomness_vec.len() - folding_factor..].to_vec())
    }
}

// Fused combine + round-0: evaluate each combined weight Σ_s γ^{k_s}·weight_s once, inside
// the round-0 pass, instead of materializing then.

const LAZY_OVERLAY_SPAN_MAX: usize = 8; // packed words; small blocks are pre-expanded

struct LazyFullTerm<EF: KoalaBearExtension> {
    left: ArenaVec<EF>,             // prefix eq-table, scalar folded in
    right: ArenaVec<EFPacking<EF>>, // packed suffix eq-table
    rshift: usize,                  // hi = j >> rshift, lo = j & ((1 << rshift) - 1)
}

/// scalar·eq(point,·) on the packed range [start, start + 2^ishift).
struct LazyBlock<EF: KoalaBearExtension> {
    start: usize,
    ishift: usize,
    inner_id: u32,
    scalar: EF,
}

pub(crate) struct LazyCombineTerms<EF: KoalaBearExtension> {
    full: Vec<LazyFullTerm<EF>>,
    inners: Vec<ArenaVec<EFPacking<EF>>>,
    grid_blocks: Vec<LazyBlock<EF>>,
    grid: Vec<Vec<u32>>, // packed-index >> grid_log -> covering block ids
    grid_log: usize,
    overlay: Vec<(usize, EFPacking<EF>)>, // sorted by packed index
    pub(crate) combined_sum: EF,
}

impl<EF: KoalaBearExtension> LazyCombineTerms<EF> {
    #[inline(always)]
    fn value_at(&self, j: usize) -> EFPacking<EF> {
        let mut acc = EFPacking::<EF>::ZERO;
        for t in &self.full {
            acc += t.right[j & ((1 << t.rshift) - 1)] * t.left[j >> t.rshift];
        }
        if !self.grid.is_empty() {
            for &b in &self.grid[j >> self.grid_log] {
                let blk = &self.grid_blocks[b as usize];
                // listed blocks cover the whole cell
                acc += self.inners[blk.inner_id as usize][j - blk.start] * blk.scalar;
            }
        }
        acc
    }
}

/// Builds the lazy term tables; `combined_sum` is the exact combined value.
pub(crate) fn build_lazy_combine_terms<EF>(statements: &[SparseStatement<EF>], gamma: EF) -> LazyCombineTerms<EF>
where
    EF: KoalaBearExtension,
{
    let num_variables = statements[0].total_num_variables;
    assert!(statements.iter().all(|e| e.total_num_variables == num_variables));
    let w = packing_log_width::<EF>();

    let is_full = |s: &SparseStatement<EF>| {
        !s.is_next && s.values.len() == 1 && s.values[0].selector == 0 && s.inner_num_variables() == num_variables
    };

    let mut full = Vec::new();
    let mut inners: Vec<ArenaVec<EFPacking<EF>>> = Vec::new();
    let mut blocks: Vec<LazyBlock<EF>> = Vec::new();
    let mut overlay_map: std::collections::BTreeMap<usize, EFPacking<EF>> = Default::default();
    let mut combined_sum = EF::ZERO;
    let mut gamma_pow = EF::ONE;

    let make_full = |point: &[EF], scalar: EF| {
        let a = num_variables / 2;
        let left: ArenaVec<EF> = eval_eq_scaled(&point[..a], scalar);
        let right: ArenaVec<EFPacking<EF>> = eval_eq_packed(&point[a..]);
        LazyFullTerm {
            left,
            right,
            rshift: num_variables - a - w,
        }
    };

    // Leading full statements (dense eq over all variables) use the sqrt-memory tensor split.
    let mut start_idx = 0;
    while start_idx < statements.len() && is_full(&statements[start_idx]) {
        let s = &statements[start_idx];
        combined_sum += s.values[0].value * gamma_pow;
        full.push(make_full(&s.point.0, gamma_pow));
        gamma_pow *= gamma;
        start_idx += 1;
    }

    // Remaining statements, in order; one gamma power per value either way.
    for smt in &statements[start_idx..] {
        let inner_vars = smt.inner_num_variables();
        if !smt.is_next && inner_vars < w {
            // Lane-level: each value lands within a single packed word, applied via the overlay.
            let shift = w - inner_vars;
            for ev in &smt.values {
                combined_sum += ev.value * gamma_pow;
                let mut unpacked = vec![EF::ZERO; 1usize << w];
                compute_sparse_eval_eq::<EF>(ev.selector & ((1 << shift) - 1), &smt.point.0, &mut unpacked, gamma_pow);
                let delta: Vec<EFPacking<EF>> = pack_extension(&unpacked);
                *overlay_map.entry(ev.selector >> shift).or_insert(EFPacking::<EF>::ZERO) += delta[0];
                gamma_pow *= gamma;
            }
        } else {
            // Block path: build the inner eq-table once, then one block per value.
            let mut sels = smt.values.iter().map(|e| e.selector).collect::<Vec<_>>();
            sels.sort_unstable();
            sels.dedup();
            assert_eq!(sels.len(), smt.values.len(), "Duplicate selectors in sparse statement");

            let inner: ArenaVec<EFPacking<EF>> = if smt.is_next {
                pack_extension(&matrix_next_mle_folded(&smt.point.0))
            } else {
                eval_eq_packed(&smt.point)
            };
            inners.push(inner);
            let inner_id = (inners.len() - 1) as u32;
            let ishift = inner_vars - w;
            for ev in &smt.values {
                combined_sum += ev.value * gamma_pow;
                blocks.push(LazyBlock {
                    start: ev.selector << ishift,
                    ishift,
                    inner_id,
                    scalar: gamma_pow,
                });
                gamma_pow *= gamma;
            }
        }
    }

    // small blocks → overlay, large → grid
    let mut grid_blocks: Vec<LazyBlock<EF>> = Vec::new();
    for blk in blocks {
        let span = 1usize << blk.ishift;
        if span <= LAZY_OVERLAY_SPAN_MAX {
            let inner = &inners[blk.inner_id as usize];
            let s = blk.scalar;
            for t in 0..span {
                *overlay_map.entry(blk.start + t).or_insert(EFPacking::<EF>::ZERO) += inner[t] * s;
            }
        } else {
            grid_blocks.push(blk);
        }
    }

    let (grid, grid_log) = if grid_blocks.is_empty() {
        (Vec::new(), 0)
    } else {
        let grid_log = grid_blocks.iter().map(|b| b.ishift).min().unwrap();
        let n_cells = 1usize << (num_variables - w - grid_log);
        let mut grid: Vec<Vec<u32>> = vec![Vec::new(); n_cells];
        for (id, blk) in grid_blocks.iter().enumerate() {
            let c0 = blk.start >> grid_log;
            let c1 = (blk.start + (1usize << blk.ishift)) >> grid_log;
            for cell in grid.iter_mut().take(c1).skip(c0) {
                cell.push(id as u32);
            }
        }
        (grid, grid_log)
    };

    LazyCombineTerms {
        full,
        inners,
        grid_blocks,
        grid,
        grid_log,
        overlay: overlay_map.into_iter().collect(),
        combined_sum,
    }
}

// Active terms per side fit in a stack array; overflow drops to the `value_at` fallback
// (full terms — usually 1-2 — plus the grid blocks covering the cell).
const MAX_RUN_TERMS: usize = 12;

/// Gathers the terms active over a run starting at `base` (one fold side): each is a
/// (packed slice, scalar) contributing `slice[t] * scalar` to the weight at offset t.
/// Returns the term count, or None if more than `MAX_RUN_TERMS` cover the run.
#[inline]
fn gather_run_terms<'a, EF: KoalaBearExtension>(
    terms: &'a LazyCombineTerms<EF>,
    base: usize,
    run: usize,
    out: &mut [(&'a [EFPacking<EF>], EF); MAX_RUN_TERMS],
) -> Option<usize> {
    let mut n = 0;
    for t in &terms.full {
        if n == MAX_RUN_TERMS {
            return None;
        }
        let lo = base & ((1usize << t.rshift) - 1);
        out[n] = (&t.right[lo..lo + run], t.left[base >> t.rshift]);
        n += 1;
    }
    if !terms.grid.is_empty() {
        for &b in &terms.grid[base >> terms.grid_log] {
            if n == MAX_RUN_TERMS {
                return None;
            }
            let blk = &terms.grid_blocks[b as usize];
            let o = base - blk.start;
            out[n] = (&terms.inners[blk.inner_id as usize][o..o + run], blk.scalar);
            n += 1;
        }
    }
    Some(n)
}

fn lazy_run_log<EF: KoalaBearExtension>(terms: &LazyCombineTerms<EF>, count: usize) -> usize {
    let mut run_log = ::utils::log2_strict_usize(count.max(1));
    for term in &terms.full {
        run_log = run_log.min(term.rshift);
    }
    if !terms.grid.is_empty() {
        run_log = run_log.min(terms.grid_log);
    }
    run_log
}

fn materialize_weights<EF: KoalaBearExtension>(terms: &LazyCombineTerms<EF>, len: usize) -> ArenaVec<EFPacking<EF>> {
    let mut weights = ArenaVec::par_collect(len, |i| terms.value_at(i));
    for &(index, delta) in &terms.overlay {
        weights[index] += delta;
    }
    weights
}

fn materialize_scaled_weights<EF: KoalaBearExtension>(
    groups: &[(&LazyCombineTerms<EF>, EF)],
    len: usize,
) -> MleOwned<EF> {
    let mut weights = ArenaVec::par_collect(len, |index| {
        groups.iter().fold(EFPacking::<EF>::ZERO, |sum, (terms, scale)| {
            sum + terms.value_at(index) * *scale
        })
    });
    for (terms, scale) in groups {
        for &(index, delta) in &terms.overlay {
            weights[index] += delta * *scale;
        }
    }
    MleOwned::ExtensionPacked(weights)
}

/// Computes the first product-sumcheck polynomial without materializing the
/// extension-field weight vector.
fn compute_first_round<EF>(evals: &[PFPacking<EF>], terms: &LazyCombineTerms<EF>) -> DensePolynomial<EF>
where
    EF: KoalaBearExtension,
    EFPacking<EF>: std::ops::Mul<PFPacking<EF>, Output = EFPacking<EF>> + std::ops::Mul<EF, Output = EFPacking<EF>>,
{
    let n = evals.len();
    let half = n / 2;

    // Run length keeps each term's context constant, so the inner loop can hoist it.
    let run_log = lazy_run_log(terms, half);
    let run = 1usize << run_log;
    let n_runs = half >> run_log;

    let (mut c0p, mut c2p) = parallel::map_reduce(
        n_runs,
        || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
        |run_idx| {
            let j0 = run_idx << run_log;
            let mut acc0 = EFPacking::<EF>::ZERO;
            let mut acc2 = EFPacking::<EF>::ZERO;

            let mut buf_lo: [(&[EFPacking<EF>], EF); MAX_RUN_TERMS] = [(&[], EF::ZERO); MAX_RUN_TERMS];
            let mut buf_hi: [(&[EFPacking<EF>], EF); MAX_RUN_TERMS] = [(&[], EF::ZERO); MAX_RUN_TERMS];
            let (Some(n_lo), Some(n_hi)) = (
                gather_run_terms(terms, j0, run, &mut buf_lo),
                gather_run_terms(terms, half + j0, run, &mut buf_hi),
            ) else {
                // rare fallback: evaluate each weight directly
                for t in 0..run {
                    let i = j0 + t;
                    let w0 = terms.value_at(i);
                    let w1 = terms.value_at(half + i);
                    acc0 += w0 * evals[i];
                    acc2 += (w1 - w0) * (evals[half + i] - evals[i]);
                }
                return (acc0, acc2);
            };
            let (terms_lo, terms_hi) = (&buf_lo[..n_lo], &buf_hi[..n_hi]);

            let e_lo = &evals[j0..j0 + run];
            let e_hi = &evals[half + j0..half + j0 + run];
            for t in 0..run {
                let mut w0 = EFPacking::<EF>::ZERO;
                for term in terms_lo {
                    w0 += term.0[t] * term.1;
                }
                let mut w1 = EFPacking::<EF>::ZERO;
                for term in terms_hi {
                    w1 += term.0[t] * term.1;
                }
                acc0 += w0 * e_lo[t];
                acc2 += (w1 - w0) * (e_hi[t] - e_lo[t]);
            }
            (acc0, acc2)
        },
        |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
    );

    // Apply the sparse overlay directly to the round polynomial.
    for &(idx, delta) in &terms.overlay {
        if idx < half {
            // d c0 = delta·e0 ; d c2 = -delta·(e1 - e0)
            c0p += delta * evals[idx];
            c2p += delta * (evals[idx] - evals[half + idx]);
        } else {
            // d c2 = delta·(e1 - e0)
            c2p += delta * (evals[idx] - evals[idx - half]);
        }
    }

    let c0 = packing_unpack_sum::<EF>(c0p);
    let c2 = packing_unpack_sum::<EF>(c2p);
    let c1 = terms.combined_sum - c0.double() - c2;
    DensePolynomial::new(vec![c0, c1, c2])
}

/// Computes the second product-sumcheck polynomial and writes only the weights
/// folded by the already sampled first challenge.
fn compute_second_round_and_fold_weights<EF>(
    evals: &[PFPacking<EF>],
    terms: &LazyCombineTerms<EF>,
    r1: EF,
    sum_after_r1: EF,
) -> (DensePolynomial<EF>, ArenaVec<EFPacking<EF>>)
where
    EF: KoalaBearExtension,
    EFPacking<EF>: std::ops::Mul<PFPacking<EF>, Output = EFPacking<EF>> + std::ops::Mul<EF, Output = EFPacking<EF>>,
{
    let n = evals.len();
    let half = n / 2;
    let quarter = n / 4;
    let r1p = EFPacking::<EF>::from(r1);
    let mut folded_weights = unsafe { ArenaVec::<EFPacking<EF>>::uninitialized(half) };
    let folded_ptr = parallel::SendPtr(folded_weights.as_mut_ptr());

    let run_log = lazy_run_log(terms, quarter);
    let run = 1usize << run_log;
    let n_runs = quarter >> run_log;

    type Quad<EF> = (EFPacking<EF>, EFPacking<EF>, EFPacking<EF>, EFPacking<EF>);
    type RunBuffers<'a, EF> = [[(&'a [EFPacking<EF>], EF); MAX_RUN_TERMS]; 4];
    let (mut p0, mut p1, mut s0, mut s1) = parallel::map_reduce(
        n_runs,
        || {
            (
                EFPacking::<EF>::ZERO,
                EFPacking::<EF>::ZERO,
                EFPacking::<EF>::ZERO,
                EFPacking::<EF>::ZERO,
            )
        },
        |run_index| {
            let j0 = run_index << run_log;
            let mut acc: Quad<EF> = Default::default();
            let mut buffers: RunBuffers<'_, EF> = [[(&[], EF::ZERO); MAX_RUN_TERMS]; 4];
            let counts = [
                gather_run_terms(terms, j0, run, &mut buffers[0]),
                gather_run_terms(terms, quarter + j0, run, &mut buffers[1]),
                gather_run_terms(terms, half + j0, run, &mut buffers[2]),
                gather_run_terms(terms, half + quarter + j0, run, &mut buffers[3]),
            ];

            for t in 0..run {
                let i = j0 + t;
                let mut weights = [EFPacking::<EF>::ZERO; 4];
                for quadrant in 0..4 {
                    if let Some(count) = counts[quadrant] {
                        for term in &buffers[quadrant][..count] {
                            weights[quadrant] += term.0[t] * term.1;
                        }
                    } else {
                        weights[quadrant] = terms.value_at(quadrant * quarter + i);
                    }
                }

                let y_0 = r1p * (weights[2] - weights[0]) + weights[0];
                let y_1 = r1p * (weights[3] - weights[1]) + weights[1];
                unsafe {
                    *folded_ptr.add(i) = y_0;
                    *folded_ptr.add(quarter + i) = y_1;
                }

                let e_0 = evals[i];
                let e_1 = evals[half + i];
                let e_2 = evals[quarter + i];
                let e_3 = evals[half + quarter + i];
                let dy = y_1 - y_0;
                acc.0 += y_0 * e_0;
                acc.1 += y_0 * (e_1 - e_0);
                acc.2 += dy * (e_2 - e_0);
                acc.3 += dy * ((e_3 - e_2) - (e_1 - e_0));
            }
            acc
        },
        |(a, b, c, d), (e, f, g, h)| (a + e, b + f, c + g, d + h),
    );

    // Apply sparse overlay deltas to the folded weights and polynomial.
    for &(index, delta) in &terms.overlay {
        let (folded_index, folded_delta) = if index < half {
            (index, delta * (EF::ONE - r1))
        } else {
            (index - half, delta * r1)
        };
        folded_weights[folded_index] += folded_delta;

        let low_index = folded_index % quarter;
        let e_0 = evals[low_index];
        let e_1 = evals[half + low_index];
        if folded_index < quarter {
            let e_2 = evals[quarter + low_index];
            let e_3 = evals[half + quarter + low_index];
            p0 += folded_delta * e_0;
            p1 += folded_delta * (e_1 - e_0);
            s0 -= folded_delta * (e_2 - e_0);
            s1 -= folded_delta * ((e_3 - e_2) - (e_1 - e_0));
        } else {
            let e_2 = evals[quarter + low_index];
            let e_3 = evals[half + quarter + low_index];
            s0 += folded_delta * (e_2 - e_0);
            s1 += folded_delta * ((e_3 - e_2) - (e_1 - e_0));
        }
    }

    let c0 = packing_unpack_sum::<EF>(p0) + r1 * packing_unpack_sum::<EF>(p1);
    let c2 = packing_unpack_sum::<EF>(s0) + r1 * packing_unpack_sum::<EF>(s1);
    let c1 = sum_after_r1 - c0.double() - c2;
    (DensePolynomial::new(vec![c0, c1, c2]), folded_weights)
}
