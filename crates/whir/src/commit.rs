// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use fiat_shamir::FSProver;
use field::BasedVectorSpace;
use poly::*;
use tracing::{info_span, instrument};
use zk_alloc::ArenaVec;

use crate::*;

#[derive(Debug, Clone)]
pub enum MerkleData<EF: KoalaBearExtension> {
    Base(RoundMerkleTree<PF<EF>>),
    Extension(RoundMerkleTree<PF<EF>>),
}

impl<EF: KoalaBearExtension> MerkleData<EF> {
    pub(crate) fn build(
        matrix: DftOutput<EF>,
        full_n_cols: usize,
        effective_n_cols: usize,
        hash_profile: symetric::ProofHashProfile,
    ) -> (Self, [PF<EF>; DIGEST_ELEMS]) {
        match matrix {
            DftOutput::Base(m) => {
                let (root, prover_data) = merkle_commit::<PF<EF>>(m, full_n_cols, effective_n_cols, hash_profile);
                (MerkleData::Base(prover_data), root)
            }
            DftOutput::Extension(m) => {
                let (root, prover_data) = merkle_commit::<EF>(m, full_n_cols, effective_n_cols, hash_profile);
                (MerkleData::Extension(prover_data), root)
            }
        }
    }

    pub(crate) fn open(&self, index: usize) -> (MleOwned<EF>, Vec<[PF<EF>; DIGEST_ELEMS]>) {
        match self {
            MerkleData::Base(prover_data) => {
                let (leaf, proof) = merkle_open::<PF<EF>>(prover_data, index);
                (MleOwned::Base(ArenaVec::from_slice(&leaf)), proof)
            }
            MerkleData::Extension(prover_data) => {
                let (leaf, proof) = merkle_open::<EF>(prover_data, index);
                (MleOwned::Extension(ArenaVec::from_slice(&leaf)), proof)
            }
        }
    }

    pub fn discard_leaf(&mut self) {
        match self {
            Self::Base(data) | Self::Extension(data) => data.leaf.values = ArenaVec::new(),
        }
    }

    fn restore_leaf(&mut self, matrix: DftOutput<EF>) {
        match (self, matrix) {
            (Self::Base(data), DftOutput::Base(matrix)) => data.leaf = matrix,
            (Self::Extension(data), DftOutput::Extension(matrix)) => {
                let dimension = <EF as BasedVectorSpace<PF<EF>>>::DIMENSION;
                let values = flatten_to_base_arena::<PF<EF>, EF>(matrix.values);
                data.leaf = Matrix::new(values, matrix.width * dimension);
            }
            _ => unreachable!("WHIR commitment field kind changed while rebuilding its leaf"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Witness<EF>
where
    EF: KoalaBearExtension,
{
    pub prover_data: MerkleData<EF>,
    pub ood_points: Vec<EF>,
    pub ood_answers: Vec<EF>,
}

impl<EF> WhirConfig<EF>
where
    EF: KoalaBearExtension,
{
    #[instrument(skip_all)]
    pub fn build_commitment_data(
        &self,
        polynomial: &MleOwned<EF>,
        actual_data_len: usize, // polynomial[actual_data_len..] is zero
    ) -> (MerkleData<EF>, [PF<EF>; DIGEST_ELEMS]) {
        self.build_commitment_data_with_hash_profile(polynomial, actual_data_len, symetric::ProofHashProfile::Poseidon1)
    }

    pub fn build_commitment_data_with_hash_profile(
        &self,
        polynomial: &MleOwned<EF>,
        actual_data_len: usize,
        hash_profile: symetric::ProofHashProfile,
    ) -> (MerkleData<EF>, [PF<EF>; DIGEST_ELEMS]) {
        let n_blocks = 1usize << self.folding_factor.at_round(0);
        let evals_len = 1usize << self.num_variables;
        let effective_n_cols = actual_data_len.div_ceil(evals_len / n_blocks);
        // DFT matrix width: skip as many zero columns as possible, aligned to packing (SIMD)
        let dft_n_cols = effective_n_cols.next_multiple_of(packing_width::<EF>()).min(n_blocks);

        let folded_matrix = info_span!("FFT").in_scope(|| {
            reorder_and_dft(
                &polynomial.by_ref(),
                self.folding_factor.at_round(0),
                self.starting_log_inv_rate,
                dft_n_cols,
            )
        });

        MerkleData::build(folded_matrix, n_blocks, effective_n_cols, hash_profile)
    }

    #[instrument(skip_all)]
    pub fn rebuild_commitment_leaf(
        &self,
        polynomial: &MleOwned<EF>,
        actual_data_len: usize,
        prover_data: &mut MerkleData<EF>,
    ) {
        let n_blocks = 1usize << self.folding_factor.at_round(0);
        let evals_len = 1usize << self.num_variables;
        let effective_n_cols = actual_data_len.div_ceil(evals_len / n_blocks);
        let dft_n_cols = effective_n_cols.next_multiple_of(packing_width::<EF>()).min(n_blocks);
        let folded_matrix = info_span!("FFT").in_scope(|| {
            reorder_and_dft(
                &polynomial.by_ref(),
                self.folding_factor.at_round(0),
                self.starting_log_inv_rate,
                dft_n_cols,
            )
        });
        prover_data.restore_leaf(folded_matrix);
    }

    #[instrument(skip_all)]
    pub fn commit(
        &self,
        prover_state: &mut impl FSProver<EF>,
        polynomial: &MleOwned<EF>,
        actual_data_len: usize, // polynomial[actual_data_len..] is zero
    ) -> Witness<EF> {
        let (prover_data, root) =
            self.build_commitment_data_with_hash_profile(polynomial, actual_data_len, prover_state.hash_profile());

        prover_state.add_base_scalars(&root);

        let (ood_points, ood_answers) =
            sample_ood_points::<EF, _>(prover_state, self.commitment_ood_samples, self.num_variables, |point| {
                polynomial.evaluate(point)
            });

        Witness {
            prover_data,
            ood_points,
            ood_answers,
        }
    }

    /// Commits to a polynomial and observes only its Merkle root. Protocols
    /// that batch several roots must perform their shared OOD check after the
    /// batching challenge has fixed the combined polynomial.
    #[instrument(skip_all)]
    pub fn commit_without_ood(
        &self,
        prover_state: &mut impl FSProver<EF>,
        polynomial: &MleOwned<EF>,
        actual_data_len: usize, // polynomial[actual_data_len..] is zero
    ) -> Witness<EF> {
        let (prover_data, root) =
            self.build_commitment_data_with_hash_profile(polynomial, actual_data_len, prover_state.hash_profile());

        prover_state.add_base_scalars(&root);

        Witness {
            prover_data,
            ood_points: Vec::new(),
            ood_answers: Vec::new(),
        }
    }
}
