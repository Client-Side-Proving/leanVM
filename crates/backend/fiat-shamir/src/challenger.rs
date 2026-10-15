use crate::keccak_challenger::KeccakByteChallenger;
use field::PrimeField64;
use koala_bear::symmetric::Permutation;
use symetric::{CAPACITY, ProofHashProfile, RATE, WIDTH};

#[derive(Clone, Debug)]
pub struct Challenger<F, P> {
    pub permutation: P,
    pub state: [F; WIDTH],
    rate_fresh: bool,
    keccak: Option<KeccakByteChallenger>,
}

impl<F: PrimeField64, P: Permutation<[F; WIDTH]>> Challenger<F, P> {
    pub fn new(permutation: P, initial_capacity: [F; CAPACITY]) -> Self
    where
        F: Default,
    {
        let mut state = [F::ZERO; WIDTH];
        state[..CAPACITY].copy_from_slice(&initial_capacity);
        Self {
            permutation,
            state,
            rate_fresh: false,
            keccak: None,
        }
    }

    pub fn new_with_hash_profile(permutation: P, initial_capacity: [F; CAPACITY], profile: ProofHashProfile) -> Self
    where
        F: Default,
    {
        let mut challenger = Self::new(permutation, initial_capacity);
        if profile == ProofHashProfile::Keccak240 {
            let mut input = profile.id().as_bytes().to_vec();
            for scalar in initial_capacity {
                input.extend_from_slice(&(scalar.as_canonical_u64() as u32).to_le_bytes());
            }
            challenger.keccak = Some(KeccakByteChallenger::new(input));
        }
        challenger
    }

    pub fn hash_profile(&self) -> ProofHashProfile {
        if self.keccak.is_some() {
            ProofHashProfile::Keccak240
        } else {
            ProofHashProfile::Poseidon1
        }
    }

    pub fn check_keccak_witness(&self, bits: usize, witness: u32) -> bool {
        self.keccak
            .as_ref()
            .expect("Keccak profile")
            .check_witness(bits, witness)
    }

    pub fn absorb_keccak_witness(&mut self, bits: usize, witness: F) -> bool {
        let challenger = self.keccak.as_mut().expect("Keccak profile");
        challenger.observe(&(witness.as_canonical_u64() as u32).to_le_bytes());
        challenger.sample_u32() & ((1u32 << bits) - 1) == 0
    }

    pub fn sample_base_scalars(&mut self, n: usize) -> Vec<F> {
        if let Some(challenger) = self.keccak.as_mut() {
            return (0..n)
                .map(|_| {
                    loop {
                        let value = u64::from(challenger.sample_u32() & 0x7fff_ffff);
                        if value < F::ORDER_U64 {
                            break F::from_u32(value as u32);
                        }
                    }
                })
                .collect();
        }
        self.sample_many(n.div_ceil(RATE))
            .into_iter()
            .flatten()
            .take(n)
            .collect()
    }

    pub fn observe(&mut self, value: [F; RATE]) {
        if self.keccak.is_some() {
            self.observe_many(&value);
            return;
        }
        self.state[CAPACITY..].copy_from_slice(&value);
        self.permutation.permute_mut(&mut self.state);
        self.rate_fresh = true;
    }

    pub fn observe_many(&mut self, scalars: &[F]) {
        if let Some(challenger) = self.keccak.as_mut() {
            for scalar in scalars {
                challenger.observe(&(scalar.as_canonical_u64() as u32).to_le_bytes());
            }
            return;
        }
        for chunk in scalars.chunks(RATE) {
            let mut buffer = [F::ZERO; RATE];
            buffer[..chunk.len()].copy_from_slice(chunk);
            self.observe(buffer);
        }
    }

    pub fn duplex(&mut self) {
        self.observe([F::ZERO; RATE]);
    }

    pub fn sample(&mut self) -> [F; RATE] {
        if self.keccak.is_some() {
            return self.sample_base_scalars(RATE).try_into().unwrap();
        }
        assert!(self.rate_fresh, "stale rate. insert a duplex() before.");
        let out: [F; RATE] = self.state[CAPACITY..].try_into().unwrap();
        self.rate_fresh = false;
        out
    }

    pub fn sample_many(&mut self, n: usize) -> Vec<[F; RATE]> {
        if n == 0 {
            return Vec::new();
        }
        let mut out = Vec::with_capacity(n);
        out.push(self.sample());
        for _ in 1..n {
            self.duplex();
            out.push(self.sample());
        }
        out
    }

    /// Warning: not perfectly uniform
    pub fn sample_in_range(&mut self, bits: usize, n_samples: usize) -> Vec<usize> {
        assert!(bits < F::bits());
        if let Some(challenger) = self.keccak.as_mut() {
            return (0..n_samples)
                .map(|_| challenger.sample_u32() as usize & ((1 << bits) - 1))
                .collect();
        }
        let sampled_fe = self.sample_many(n_samples.div_ceil(RATE)).into_iter().flatten();
        let mut res = Vec::new();
        for fe in sampled_fe.take(n_samples) {
            let rand_usize = fe.as_canonical_u64() as usize;
            res.push(rand_usize & ((1 << bits) - 1));
        }
        res
    }
}
