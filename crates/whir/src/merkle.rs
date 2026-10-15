// Credits:
// - whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).
// - Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use field::BasedVectorSpace;
use field::ExtensionField;
use field::PackedValue;
use field::PrimeCharacteristicRing;
use koala_bear::{KoalaBear, default_koalabear_poseidon1_16};
use poly::*;

use symetric::merkle::unpack_array;
use tracing::instrument;
use utils::log2_ceil_usize;
use zk_alloc::ArenaVec;

use crate::Dimensions;
use crate::Matrix;
use crate::utils::flatten_to_base_arena;
pub use symetric::DIGEST_ELEMS;

pub(crate) type RoundMerkleTree<F> = WhirMerkleTree<F, DIGEST_ELEMS>;

pub(crate) fn merkle_commit<EF: ExtensionField<KoalaBear>>(
    matrix: Matrix<EF, ArenaVec<EF>>,
    full_n_cols: usize,
    effective_n_cols: usize,
    hash_profile: symetric::ProofHashProfile,
) -> ([KoalaBear; DIGEST_ELEMS], RoundMerkleTree<KoalaBear>) {
    let dim = <EF as BasedVectorSpace<KoalaBear>>::DIMENSION;
    let base_values = flatten_to_base_arena::<KoalaBear, EF>(matrix.values);
    let base_matrix = Matrix::new(base_values, matrix.width * dim);
    let tree = if hash_profile == symetric::ProofHashProfile::Keccak240 {
        build_merkle_tree_keccak240(base_matrix, full_n_cols * dim)
    } else {
        build_merkle_tree_koalabear(base_matrix, full_n_cols * dim, effective_n_cols * dim)
    };
    (tree.root(), tree)
}

fn build_merkle_tree_keccak240(
    leaf: Matrix<KoalaBear, ArenaVec<KoalaBear>>,
    full_base_width: usize,
) -> RoundMerkleTree<KoalaBear> {
    let mut first_layer = ArenaVec::filled([KoalaBear::ZERO; DIGEST_ELEMS], leaf.height());
    parallel::par_chunks_mut(&mut first_layer, 1, |index, output| {
        let mut values: Vec<_> = leaf.row(index).unwrap().collect();
        values.resize(full_base_width, KoalaBear::ZERO);
        output[0] = symetric::keccak240_leaf(&values);
    });
    let mut digest_layers = vec![first_layer];
    while digest_layers.last().unwrap().len() > 1 {
        let previous = digest_layers.last().unwrap();
        let mut next = ArenaVec::filled([KoalaBear::ZERO; DIGEST_ELEMS], previous.len() / 2);
        parallel::par_chunks_mut(&mut next, 1, |index, output| {
            output[0] = symetric::keccak240_node(&previous[2 * index], &previous[2 * index + 1])
                .expect("generated digests are canonical");
        });
        digest_layers.push(next);
    }
    WhirMerkleTree {
        leaf,
        tree: symetric::merkle::MerkleTree { digest_layers },
        full_leaf_base_width: full_base_width,
    }
}

#[instrument(name = "build merkle tree", skip_all)]
fn build_merkle_tree_koalabear(
    leaf: Matrix<KoalaBear, ArenaVec<KoalaBear>>,
    full_base_width: usize,
    effective_base_width: usize,
) -> RoundMerkleTree<KoalaBear> {
    // Leaf hashing is an overwrite sponge (raw permutation); the 2->1 tree climb is compression.
    // `perm` (Poseidon16) implements both `Permutation` and `Compression`, so it serves both roles.
    let perm = default_koalabear_poseidon1_16();
    let n_zero_suffix_rate_chunks = (full_base_width - effective_base_width) / 8;
    let iv_first = KoalaBear::from_usize(full_base_width);
    let scalar_state = symetric::precompute_zero_suffix_state::<KoalaBear, _, 16, 8, DIGEST_ELEMS>(
        &perm,
        iv_first,
        n_zero_suffix_rate_chunks,
    );
    let packed_state: [PFPacking<KoalaBear>; 16] =
        std::array::from_fn(|i| PFPacking::<KoalaBear>::from_fn(|_| scalar_state[i]));
    let first_layer = if leaf.height() < PFPacking::<KoalaBear>::WIDTH {
        first_digest_layer_with_initial_state::<KoalaBear, _, _, DIGEST_ELEMS, 16, 8>(
            &perm,
            &leaf,
            &scalar_state,
            effective_base_width,
        )
    } else {
        first_digest_layer_with_initial_state::<PFPacking<KoalaBear>, _, _, DIGEST_ELEMS, 16, 8>(
            &perm,
            &leaf,
            &packed_state,
            effective_base_width,
        )
    };
    let tree = symetric::merkle::MerkleTree::from_first_layer::<PFPacking<KoalaBear>, _, 16>(&perm, first_layer);
    WhirMerkleTree {
        leaf,
        tree,
        full_leaf_base_width: full_base_width,
    }
}

pub(crate) fn merkle_open<EF: ExtensionField<KoalaBear>>(
    merkle_tree: &RoundMerkleTree<KoalaBear>,
    index: usize,
) -> (Vec<EF>, Vec<[KoalaBear; DIGEST_ELEMS]>) {
    let (inner_leaf, proof) = merkle_tree.open(index);
    (EF::reconstitute_from_base(inner_leaf), proof)
}

pub(crate) fn merkle_verify<EF: ExtensionField<KoalaBear>>(
    merkle_root: [KoalaBear; DIGEST_ELEMS],
    index: usize,
    dimension: Dimensions,
    data: Vec<EF>,
    proof: &Vec<[KoalaBear; DIGEST_ELEMS]>,
    hash_profile: symetric::ProofHashProfile,
) -> bool {
    if hash_profile == symetric::ProofHashProfile::Keccak240 {
        if !dimension.height.is_power_of_two()
            || index >= dimension.height
            || data.len() != dimension.width
            || proof.len() != utils::log2_strict_usize(dimension.height)
            || symetric::decode_keccak240(&merkle_root).is_none()
            || proof.iter().any(|digest| symetric::decode_keccak240(digest).is_none())
        {
            return false;
        }
        let mut current = symetric::keccak240_leaf(&EF::flatten_to_base(data));
        let mut position = index;
        for sibling in proof {
            let (left, right) = if position & 1 == 0 {
                (&current, sibling)
            } else {
                (sibling, &current)
            };
            current = symetric::keccak240_node(left, right).expect("digest limbs checked");
            position >>= 1;
        }
        return current == merkle_root;
    }
    let perm = default_koalabear_poseidon1_16();
    let log_max_height = utils::log2_strict_usize(dimension.height);
    let base_data = EF::flatten_to_base(data);
    symetric::merkle::merkle_verify::<_, _, _, DIGEST_ELEMS, 16, 8>(
        &perm,
        &perm,
        &merkle_root,
        log_max_height,
        index,
        &base_data,
        proof,
    )
}

#[derive(Debug, Clone)]
pub struct WhirMerkleTree<F, const DIGEST_ELEMS: usize> {
    pub(crate) leaf: Matrix<F, ArenaVec<F>>,
    pub(crate) tree: symetric::merkle::MerkleTree<F, DIGEST_ELEMS>,
    full_leaf_base_width: usize,
}

impl<F: field::PrimeCharacteristicRing + Send + Sync, const DIGEST_ELEMS: usize> WhirMerkleTree<F, DIGEST_ELEMS> {
    #[must_use]
    pub fn root(&self) -> [F; DIGEST_ELEMS] {
        self.tree.root()
    }

    pub fn open(&self, index: usize) -> (Vec<F>, Vec<[F; DIGEST_ELEMS]>) {
        let log_height = log2_ceil_usize(self.leaf.height());
        let mut opening: Vec<F> = self.leaf.row(index).unwrap().collect();
        opening.resize(self.full_leaf_base_width, F::default());
        let proof = self.tree.open_siblings(index, log_height);
        (opening, proof)
    }
}

#[instrument(name = "first digest layer", level = "debug", skip_all)]
fn first_digest_layer_with_initial_state<
    P,
    Perm,
    LV,
    const DIGEST_ELEMS: usize,
    const WIDTH: usize,
    const RATE: usize,
>(
    perm: &Perm,
    matrix: &Matrix<P::Value, LV>,
    packed_initial_state: &[P; WIDTH],
    effective_base_width: usize,
) -> ArenaVec<[P::Value; DIGEST_ELEMS]>
where
    P: PackedValue + Default,
    LV: AsRef<[P::Value]> + Send + Sync,
    P::Value: Default + Copy + Send + Sync,
    Perm: koala_bear::symmetric::Permutation<[P::Value; WIDTH]> + koala_bear::symmetric::Permutation<[P; WIDTH]>,
{
    let width = P::WIDTH;
    let height = matrix.height();
    assert!(height.is_multiple_of(width));
    let n_pad = (RATE - effective_base_width % RATE) % RATE;

    let mut digests = unsafe { ArenaVec::uninitialized(height) };

    parallel::par_chunks_mut(&mut digests, width, |i, digests_chunk| {
        let first_row = i * width;
        let rtl_iter = matrix.vertically_packed_row_rtl::<P>(first_row, effective_base_width, n_pad);
        let packed_digest: [P; DIGEST_ELEMS] =
            symetric::hash_rtl_iter_with_initial_state::<_, _, _, WIDTH, RATE, DIGEST_ELEMS>(
                perm,
                rtl_iter,
                packed_initial_state,
            );
        for (dst, src) in digests_chunk.iter_mut().zip(unpack_array(packed_digest)) {
            *dst = src;
        }
    });

    digests
}

#[cfg(test)]
mod keccak_tests {
    use super::*;
    use symetric::ProofHashProfile;

    #[test]
    fn keccak_tree_opens_and_rejects_malformed_digests_and_paths() {
        let values = ArenaVec::from_slice(&[1u32, 2, 3, 4, 5, 6].map(KoalaBear::from_u32));
        let tree = build_merkle_tree_keccak240(Matrix::new(values, 3), 4);
        let root = tree.root();
        let (leaf, path) = tree.open(1);
        let dims = Dimensions { height: 2, width: 4 };
        assert!(merkle_verify(
            root,
            1,
            dims,
            leaf.clone(),
            &path,
            ProofHashProfile::Keccak240
        ));
        assert_eq!(leaf[3], KoalaBear::ZERO);
        assert!(!merkle_verify(
            root,
            3,
            dims,
            leaf.clone(),
            &path,
            ProofHashProfile::Keccak240
        ));
        assert!(!merkle_verify(
            root,
            1,
            dims,
            leaf[..3].to_vec(),
            &path,
            ProofHashProfile::Keccak240
        ));
        let mut invalid_root = root;
        invalid_root[0] = KoalaBear::from_u32(1 << 30);
        assert!(!merkle_verify(
            invalid_root,
            1,
            dims,
            leaf.clone(),
            &path,
            ProofHashProfile::Keccak240
        ));
        let mut invalid_path = path.clone();
        invalid_path[0][7] = KoalaBear::from_u32(1 << 30);
        assert!(!merkle_verify(
            root,
            1,
            dims,
            leaf.clone(),
            &invalid_path,
            ProofHashProfile::Keccak240
        ));
        assert!(!merkle_verify(
            root,
            1,
            dims,
            leaf.clone(),
            &vec![],
            ProofHashProfile::Keccak240
        ));
        let mut changed_leaf = leaf;
        changed_leaf[0] += KoalaBear::ONE;
        assert!(!merkle_verify(
            root,
            1,
            dims,
            changed_leaf,
            &path,
            ProofHashProfile::Keccak240
        ));
    }
}
