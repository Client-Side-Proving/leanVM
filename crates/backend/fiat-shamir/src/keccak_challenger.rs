//! Keccak byte transcript with canonical scalar observations.
//! Observations invalidate pending output; digest bytes are sampled from the end.

use symetric::keccak256;

#[derive(Clone, Debug)]
pub(crate) struct KeccakByteChallenger {
    input: Vec<u8>,
    output: [u8; 32],
    remaining: usize,
}

impl KeccakByteChallenger {
    pub fn new(input: Vec<u8>) -> Self {
        Self {
            input,
            output: [0; 32],
            remaining: 0,
        }
    }

    pub fn observe(&mut self, values: &[u8]) {
        if !values.is_empty() {
            self.remaining = 0;
            self.input.extend_from_slice(values);
        }
    }

    fn sample_byte(&mut self) -> u8 {
        if self.remaining == 0 {
            self.output = keccak256(&[&self.input]);
            self.input.clear();
            self.input.extend_from_slice(&self.output);
            self.remaining = 32;
        }
        self.remaining -= 1;
        self.output[self.remaining]
    }

    pub fn sample_u32(&mut self) -> u32 {
        u32::from_le_bytes(std::array::from_fn(|_| self.sample_byte()))
    }

    pub fn check_witness(&self, bits: usize, witness: u32) -> bool {
        let digest = keccak256(&[&self.input, &witness.to_le_bytes()]);
        let value = u32::from_le_bytes([digest[31], digest[30], digest[29], digest[28]]);
        value & ((1u32 << bits) - 1) == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn grinding_matches_existing_standalone_keccak_vector() {
        let initial = KeccakByteChallenger::new(b"Spartan".to_vec());
        assert!(initial.check_witness(8, 64));
        assert!(!initial.check_witness(8, 63));
        let mut replay = initial;
        replay.observe(&64u32.to_le_bytes());
        assert_eq!(replay.sample_u32() & 255, 0);
    }
}
