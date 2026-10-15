use crate::challenger::Challenger;
use crate::{
    MerkleOpening, MerklePaths, PrunedMerklePaths, RawProof,
    transcript::{DIGEST_LEN_FE, Proof},
    *,
};
use field::PrimeCharacteristicRing;
use field::PrimeField64;
use koala_bear::KoalaBearExtension;
use koala_bear::symmetric::Permutation;
use koala_bear::{KoalaBear, default_koalabear_poseidon1_16};
use std::collections::VecDeque;
use std::iter::repeat_n;
use symetric::CAPACITY;
use symetric::RATE;
use symetric::WIDTH;

pub struct VerifierState<EF: KoalaBearExtension, P> {
    challenger: Challenger<PF<EF>, P>,
    transcript: Vec<PF<EF>>,
    transcript_offset: usize,
    pending_merkle_paths: VecDeque<PrunedMerklePaths<PF<EF>, PF<EF>>>,
    merkle_openings: Vec<MerkleOpening<PF<EF>>>,
    merkle_opening_index: usize,
    raw_transcript: Vec<PF<EF>>, // reconstructed during the proof verification, it's the format that the zkVM recursion program expects (no Merkle pruning, no sumcheck optimization to send less data, etc)
}

impl<EF: KoalaBearExtension, P: Permutation<[PF<EF>; WIDTH]>> VerifierState<EF, P> {
    pub fn new(proof: Proof<PF<EF>>, permutation: P, capacity: [PF<EF>; CAPACITY]) -> Result<Self, ProofError> {
        Ok(Self {
            challenger: Challenger::new(permutation, capacity),
            transcript: proof.transcript,
            transcript_offset: 0,
            pending_merkle_paths: proof.merkle_paths.into(),
            merkle_openings: Vec::new(),
            merkle_opening_index: 0,
            raw_transcript: Vec::new(),
        })
    }

    pub fn new_with_hash_profile(
        proof: Proof<PF<EF>>,
        permutation: P,
        capacity: [PF<EF>; CAPACITY],
        profile: symetric::ProofHashProfile,
    ) -> Result<Self, ProofError> {
        let mut state = Self::new(proof, permutation.clone(), capacity)?;
        state.challenger = Challenger::new_with_hash_profile(permutation, capacity, profile);
        Ok(state)
    }

    pub fn into_raw_proof(self) -> RawProof<PF<EF>> {
        RawProof {
            transcript: self.raw_transcript,
            merkle_openings: self.merkle_openings,
        }
    }

    pub fn check_fully_consumed(&self) -> Result<(), ProofError> {
        if self.transcript_offset != self.transcript.len()
            || self.merkle_opening_index != self.merkle_openings.len()
            || !self.pending_merkle_paths.is_empty()
        {
            return Err(ProofError::InvalidProof);
        }
        Ok(())
    }

    fn absorb_and_record(&mut self, scalars: &[PF<EF>]) {
        self.challenger.observe_many(scalars);
        let total_padded = scalars.len().next_multiple_of(RATE);
        self.raw_transcript.extend_from_slice(scalars);
        self.raw_transcript
            .extend(repeat_n(PF::<EF>::ZERO, total_padded - scalars.len()));
    }

    fn read_transcript(&mut self, n: usize) -> Result<Vec<PF<EF>>, ProofError> {
        if self.transcript_offset + n > self.transcript.len() {
            return Err(ProofError::ExceededTranscript);
        }
        let scalars = self.transcript[self.transcript_offset..self.transcript_offset + n].to_vec();
        self.transcript_offset += n;
        Ok(scalars)
    }

    fn restore_merkle_paths(
        &self,
        paths: PrunedMerklePaths<KoalaBear, KoalaBear>,
        indices: &[usize],
        merkle_height: usize,
        leaf_len: usize,
    ) -> Option<Vec<MerkleOpening<KoalaBear>>> {
        if self.challenger.hash_profile() == symetric::ProofHashProfile::Keccak240 {
            if paths
                .sibling_hashes
                .iter()
                .any(|digest| symetric::decode_keccak240(digest).is_none())
            {
                return None;
            }
            let restored = paths.restore(
                indices,
                merkle_height,
                leaf_len,
                &symetric::keccak240_leaf,
                &|left, right| {
                    symetric::keccak240_node(left, right).expect("digest limbs validated before Merkle restoration")
                },
            )?;
            return Some(
                restored
                    .0
                    .into_iter()
                    .map(|path| MerkleOpening {
                        leaf_data: path.leaf_data,
                        path: path.sibling_hashes,
                    })
                    .collect(),
            );
        }
        let perm = default_koalabear_poseidon1_16();
        let hash_fn = |data: &[KoalaBear]| symetric::hash_slice_rtl::<_, _, 16, 8, DIGEST_LEN_FE>(&perm, data);
        let combine_fn = |left: &[KoalaBear; DIGEST_LEN_FE], right: &[KoalaBear; DIGEST_LEN_FE]| {
            symetric::compress(&perm, [*left, *right])
        };
        let restored: MerklePaths<KoalaBear, KoalaBear> =
            paths.restore(indices, merkle_height, leaf_len, &hash_fn, &combine_fn)?;
        let openings: Vec<MerkleOpening<KoalaBear>> = restored
            .0
            .into_iter()
            .map(|path| MerkleOpening {
                leaf_data: path.leaf_data,
                path: path.sibling_hashes,
            })
            .collect();
        Some(openings)
    }
}

impl<EF: KoalaBearExtension, P: Permutation<[PF<EF>; WIDTH]>> ChallengeSampler<EF> for VerifierState<EF, P> {
    fn sample_vec(&mut self, len: usize) -> Vec<EF> {
        sample_vec(&mut self.challenger, len)
    }
    fn sample_in_range(&mut self, bits: usize, n_samples: usize) -> Vec<usize> {
        self.challenger.sample_in_range(bits, n_samples)
    }
}

impl<EF: KoalaBearExtension, P: Permutation<[PF<EF>; WIDTH]>> FSVerifier<EF> for VerifierState<EF, P> {
    fn hash_profile(&self) -> symetric::ProofHashProfile {
        self.challenger.hash_profile()
    }
    fn state(&self) -> String {
        format!(
            "state {} (offset: {}, merkle_idx: {})",
            self.challenger
                .state
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.transcript_offset,
            self.merkle_opening_index,
        )
    }

    fn observe_scalars(&mut self, scalars: &[PF<EF>]) {
        self.challenger.observe_many(scalars);
    }

    fn duplex(&mut self) {
        self.challenger.duplex();
    }

    fn next_base_scalars_vec(&mut self, n: usize) -> Result<Vec<PF<EF>>, ProofError> {
        let scalars = self.read_transcript(n)?;
        self.absorb_and_record(&scalars);
        Ok(scalars)
    }

    fn begin_merkle_opening_batch(
        &mut self,
        indices: &[usize],
        merkle_height: usize,
        leaf_len: usize,
    ) -> Result<(), ProofError> {
        if self.merkle_opening_index != self.merkle_openings.len() {
            return Err(ProofError::InvalidProof); // Previous batch must have been fully drained
        }
        let paths = self
            .pending_merkle_paths
            .pop_front()
            .ok_or(ProofError::ExceededTranscript)?;
        let restored = self
            .restore_merkle_paths(paths, indices, merkle_height, leaf_len)
            .ok_or(ProofError::InvalidProof)?;
        self.merkle_openings.extend(restored);
        Ok(())
    }

    fn next_merkle_opening(&mut self) -> Result<MerkleOpening<PF<EF>>, ProofError> {
        if self.merkle_opening_index >= self.merkle_openings.len() {
            return Err(ProofError::ExceededTranscript);
        }
        let opening = self.merkle_openings[self.merkle_opening_index].clone();
        self.merkle_opening_index += 1;
        Ok(opening)
    }

    fn check_pow_grinding(&mut self, bits: usize) -> Result<(), ProofError> {
        if bits == 0 {
            return Ok(());
        }
        let witness = self.read_transcript(1)?[0];
        if self.challenger.hash_profile() == symetric::ProofHashProfile::Keccak240 {
            if !self.challenger.absorb_keccak_witness(bits, witness) {
                return Err(ProofError::InvalidGrindingWitness);
            }
            self.raw_transcript.push(witness);
            self.raw_transcript.extend(repeat_n(PF::<EF>::ZERO, RATE - 1));
            return Ok(());
        }
        self.challenger.observe_many(&[witness]);
        if self.challenger.state[CAPACITY].as_canonical_u64() & ((1 << bits) - 1) != 0 {
            return Err(ProofError::InvalidGrindingWitness);
        }
        // On "compressed" proofs (in Rust), we assume only the first field element is pow-grinded (the RATE-1 others are zero) -> saves a bit of proof size
        // On "raw" proofs (without Prunned merkle paths, the one used in recursion program (fiat_shamir.py) / python verifier (verifier.py) -> what's actually specified), we assume all 8 field elements are pow-grinded
        self.raw_transcript.push(witness);
        self.raw_transcript.extend(repeat_n(PF::<EF>::ZERO, RATE - 1));
        // Refresh the rate after constraining one of its words.
        self.challenger.duplex();
        Ok(())
    }

    fn next_sumcheck_polynomial(
        &mut self,
        n_coeffs: usize,
        claimed_sum: EF,
        eq_alpha: Option<EF>,
    ) -> ProofResult<Vec<EF>> {
        match eq_alpha {
            None => {
                let rest_scalars = self.read_transcript((n_coeffs - 1) * EF::DIMENSION)?;
                let rest_coeffs: Vec<EF> = pack_scalars_to_extension(&rest_scalars);
                // we use h(0) + h(1) = claimed_sum to recover the missing c0
                let c0 = (claimed_sum - rest_coeffs.iter().copied().sum::<EF>()).halve();

                let mut full_coeffs = Vec::with_capacity(n_coeffs);
                full_coeffs.push(c0);
                full_coeffs.extend_from_slice(&rest_coeffs);

                let mut all_scalars = flatten_scalars_to_base(&[c0]);
                all_scalars.extend_from_slice(&rest_scalars);
                self.absorb_and_record(&all_scalars);
                Ok(full_coeffs)
            }
            Some(alpha) => {
                let rest_scalars = self.read_transcript((n_coeffs - 2) * EF::DIMENSION)?;
                let rest_bare: Vec<EF> = pack_scalars_to_extension(&rest_scalars);
                let h0 = claimed_sum - alpha * rest_bare.iter().copied().sum::<EF>();

                let mut bare = Vec::with_capacity(n_coeffs - 1);
                bare.push(h0);
                bare.extend_from_slice(&rest_bare);

                let full_coeffs = expand_bare_to_full(&bare, alpha);
                self.absorb_and_record(&flatten_scalars_to_base(&full_coeffs));
                Ok(full_coeffs)
            }
        }
    }
}

#[cfg(test)]
mod grinding_tests {
    use super::*;
    use crate::{ChallengeSampler, FSProver, ProverState};
    use koala_bear::QuinticExtensionFieldKB;

    type EF = QuinticExtensionFieldKB;

    #[test]
    fn poseidon_grinding_refreshes_extension_and_query_samples() {
        let permutation = default_koalabear_poseidon1_16();
        let capacity = [KoalaBear::from_u32(7); CAPACITY];
        let prefix = [KoalaBear::from_u32(17), KoalaBear::from_u32(19)];
        let bits = 4;
        let mask = (1 << bits) - 1;
        let mut before_work = Challenger::new(permutation.clone(), capacity);
        before_work.observe_many(&prefix);

        // Choose a deterministic passing witness whose next, independently
        // permuted word fails the work predicate. Reusing the checked rate
        // would force both the first EF coefficient and query to have zero bits.
        let (witness, checked_word, refreshed) = (0..4096)
            .find_map(|candidate| {
                let witness = KoalaBear::from_u32(candidate);
                let mut checked = before_work.clone();
                checked.observe_many(&[witness]);
                let checked_word = checked.state[CAPACITY];
                if checked_word.as_canonical_u64() & mask != 0 {
                    return None;
                }
                let mut refreshed = checked.state;
                refreshed[CAPACITY..].fill(KoalaBear::ZERO);
                permutation.permute_mut(&mut refreshed);
                (refreshed[CAPACITY].as_canonical_u64() & mask != 0).then_some((witness, checked_word, refreshed))
            })
            .expect("deterministic work witness with distinct next sample");

        let proof = Proof {
            transcript: vec![witness],
            merkle_paths: vec![],
        };
        let mut verifier = VerifierState::<EF, _>::new(proof.clone(), permutation.clone(), capacity).unwrap();
        verifier.observe_scalars(&prefix);
        verifier.check_pow_grinding(bits).unwrap();
        assert_eq!(verifier.challenger.state, refreshed);
        let extension = flatten_scalars_to_base::<KoalaBear, EF>(&verifier.sample_vec(1));
        assert_eq!(extension, refreshed[CAPACITY..CAPACITY + 5]);
        assert_ne!(extension[0], checked_word);
        assert_ne!(extension[0].as_canonical_u64() & mask, 0);
        verifier.check_fully_consumed().unwrap();
        let raw = verifier.into_raw_proof();
        assert_eq!(raw.transcript.len(), RATE);
        assert_eq!(raw.transcript[0], witness);
        assert!(raw.transcript[1..].iter().all(|word| *word == KoalaBear::ZERO));

        let mut verifier = VerifierState::<EF, _>::new(proof, permutation, capacity).unwrap();
        verifier.observe_scalars(&prefix);
        verifier.check_pow_grinding(bits).unwrap();
        let queries = verifier.sample_in_range(bits, RATE);
        let expected: Vec<_> = refreshed[CAPACITY..]
            .iter()
            .map(|word| (word.as_canonical_u64() & mask) as usize)
            .collect();
        assert_eq!(queries, expected);
        assert_ne!(queries[0], 0);
        verifier.check_fully_consumed().unwrap();
    }

    #[test]
    fn poseidon_grinding_prover_verifier_replay() {
        let permutation = default_koalabear_poseidon1_16();
        let capacity = [KoalaBear::from_u32(11); CAPACITY];
        let prefix = [KoalaBear::from_u32(23), KoalaBear::from_u32(29)];
        let marker = [KoalaBear::from_u32(31)];
        let mut prover = ProverState::<EF, _>::new(permutation.clone(), capacity);
        prover.observe_scalars(&prefix);
        prover.pow_grinding(4);
        let extension = prover.sample_vec(1);
        prover.observe_scalars(&marker);
        prover.pow_grinding(8);
        let queries = prover.sample_in_range(12, 13);
        let proof = prover.into_proof();
        assert_eq!(proof.transcript.len(), 2);

        let mut verifier = VerifierState::<EF, _>::new(proof, permutation, capacity).unwrap();
        verifier.observe_scalars(&prefix);
        verifier.check_pow_grinding(4).unwrap();
        assert_eq!(verifier.sample_vec(1), extension);
        verifier.observe_scalars(&marker);
        verifier.check_pow_grinding(8).unwrap();
        assert_eq!(verifier.sample_in_range(12, 13), queries);
        verifier.check_fully_consumed().unwrap();
    }

    #[test]
    fn zero_grinding_preserves_poseidon_state_and_transcript() {
        let permutation = default_koalabear_poseidon1_16();
        let capacity = [KoalaBear::from_u32(13); CAPACITY];
        let prefix = [KoalaBear::from_u32(37), KoalaBear::from_u32(41)];
        let mut expected = Challenger::new(permutation.clone(), capacity);
        expected.observe_many(&prefix);
        let expected_extension = sample_vec::<KoalaBear, EF, _>(&mut expected, 1);

        let mut prover = ProverState::<EF, _>::new(permutation.clone(), capacity);
        prover.observe_scalars(&prefix);
        prover.pow_grinding(0);
        assert_eq!(prover.sample_vec(1), expected_extension);
        let proof = prover.into_proof();
        assert!(proof.transcript.is_empty());
        let mut verifier = VerifierState::<EF, _>::new(proof, permutation, capacity).unwrap();
        verifier.observe_scalars(&prefix);
        let before = verifier.challenger.state;
        verifier.check_pow_grinding(0).unwrap();
        assert_eq!(verifier.challenger.state, before);
        assert_eq!(verifier.sample_vec(1), expected_extension);
        verifier.check_fully_consumed().unwrap();
        assert!(verifier.into_raw_proof().transcript.is_empty());
    }
}

#[cfg(test)]
mod keccak_tests {
    use super::*;
    use crate::{ChallengeSampler, FSProver, ProverState};
    use koala_bear::QuinticExtensionFieldKB;
    use symetric::ProofHashProfile;
    type EF = QuinticExtensionFieldKB;

    #[test]
    fn keccak_prover_verifier_replay_and_domain_binding() {
        let permutation = default_koalabear_poseidon1_16();
        let cap = [KoalaBear::from_u32(7); 8];
        let values = [KoalaBear::ONE, KoalaBear::from_u32(100)];
        let mut prover =
            ProverState::<EF, _>::new_with_hash_profile(permutation.clone(), cap, ProofHashProfile::Keccak240);
        prover.observe_scalars(&values);
        prover.add_base_scalars(&values);
        let first = prover.sample_vec(3);
        prover.duplex();
        let indices = prover.sample_in_range(12, 13);
        prover.pow_grinding(8);
        let last = prover.sample_vec(2);
        let proof = prover.into_proof();
        let mut verifier = VerifierState::<EF, _>::new_with_hash_profile(
            proof.clone(),
            permutation.clone(),
            cap,
            ProofHashProfile::Keccak240,
        )
        .unwrap();
        verifier.observe_scalars(&values);
        assert_eq!(verifier.next_base_scalars_vec(2).unwrap(), values);
        assert_eq!(verifier.sample_vec(3), first);
        verifier.duplex();
        assert_eq!(verifier.sample_in_range(12, 13), indices);
        verifier.check_pow_grinding(8).unwrap();
        assert_eq!(verifier.sample_vec(2), last);
        verifier.check_fully_consumed().unwrap();
        let mut other = VerifierState::<EF, _>::new_with_hash_profile(
            proof,
            permutation,
            [KoalaBear::from_u32(8); 8],
            ProofHashProfile::Keccak240,
        )
        .unwrap();
        other.observe_scalars(&values);
        other.next_base_scalars_vec(2).unwrap();
        assert_ne!(other.sample_vec(3), first);
    }

    #[test]
    fn keccak_fixed_transcript_vector_and_raw_alignment() {
        let proof = Proof {
            transcript: [1, 100, 705].map(KoalaBear::from_u32).to_vec(),
            merkle_paths: vec![],
        };
        let mut verifier = VerifierState::<EF, _>::new_with_hash_profile(
            proof,
            default_koalabear_poseidon1_16(),
            [KoalaBear::from_u32(7); 8],
            ProofHashProfile::Keccak240,
        )
        .unwrap();
        verifier.observe_scalars(&[KoalaBear::ONE, KoalaBear::from_u32(100)]);
        verifier.next_base_scalars_vec(2).unwrap();
        let first = verifier.sample_vec(3);
        assert_eq!(
            flatten_scalars_to_base::<KoalaBear, EF>(&first)
                .iter()
                .map(|x| x.as_canonical_u64())
                .collect::<Vec<_>>(),
            [
                1451876070, 485106278, 173556515, 699718149, 651102997, 1085862884, 986254088, 654072649, 1149378872,
                1533631312, 1449400902, 637927793, 1784086481, 825560845, 251069914
            ]
        );
        verifier.duplex();
        assert_eq!(
            verifier.sample_in_range(12, 13),
            [
                2359, 3446, 1377, 2994, 3208, 2016, 2115, 1354, 687, 979, 1009, 2219, 1812
            ]
        );
        verifier.check_pow_grinding(8).unwrap();
        let last = verifier.sample_vec(2);
        assert_eq!(
            flatten_scalars_to_base::<KoalaBear, EF>(&last)
                .iter()
                .map(|x| x.as_canonical_u64())
                .collect::<Vec<_>>(),
            [
                1856097190, 1173918073, 1518848009, 1710059817, 1514931505, 1275236923, 1939419923, 1198722986,
                2126895393, 836866825
            ]
        );
        verifier.check_fully_consumed().unwrap();
        assert_eq!(
            verifier.into_raw_proof().transcript,
            [1, 100, 0, 0, 0, 0, 0, 0, 705, 0, 0, 0, 0, 0, 0, 0].map(KoalaBear::from_u32)
        );
    }

    #[test]
    fn keccak_pruned_restoration_rejects_noncanonical_digest() {
        let invalid = [KoalaBear::from_u32(1 << 30); 8];
        let proof = Proof {
            transcript: vec![],
            merkle_paths: vec![PrunedMerklePaths {
                leaf_data: vec![vec![KoalaBear::ONE]],
                sibling_hashes: vec![invalid],
            }],
        };
        let mut verifier = VerifierState::<EF, _>::new_with_hash_profile(
            proof,
            default_koalabear_poseidon1_16(),
            [KoalaBear::ZERO; 8],
            ProofHashProfile::Keccak240,
        )
        .unwrap();
        assert!(verifier.begin_merkle_opening_batch(&[0], 1, 1).is_err());
    }
}
