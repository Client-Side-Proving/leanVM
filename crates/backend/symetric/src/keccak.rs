//! Keccak leaf/node encodings with explicit domain prefixes.
//! A 240-bit digest is encoded injectively as eight canonical 30-bit limbs.

use field::PrimeField64;
use sha3::{Digest, Keccak256};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ProofHashProfile {
    #[default]
    Poseidon1,
    Keccak240,
}

impl ProofHashProfile {
    pub const fn id(self) -> &'static str {
        match self {
            Self::Poseidon1 => "poseidon1",
            Self::Keccak240 => "leanvm-keccak240-v1",
        }
    }
}

pub fn keccak256(parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Keccak256::new();
    for part in parts {
        hasher.update(part);
    }
    hasher.finalize().into()
}

pub fn encode_keccak240<F: PrimeField64>(digest: &[u8; 32]) -> [F; 8] {
    let mut result = [F::ZERO; 8];
    for half in 0..2 {
        let mut bytes = [0u8; 16];
        bytes[1..].copy_from_slice(&digest[half * 15..(half + 1) * 15]);
        let packed = u128::from_be_bytes(bytes);
        for limb in 0..4 {
            result[half * 4 + limb] = F::from_u32(((packed >> ((3 - limb) * 30)) & ((1 << 30) - 1)) as u32);
        }
    }
    result
}

pub fn decode_keccak240<F: PrimeField64>(limbs: &[F; 8]) -> Option<[u8; 32]> {
    let mut digest = [0u8; 32];
    for half in 0..2 {
        let mut packed = 0u128;
        for limb in &limbs[half * 4..(half + 1) * 4] {
            let value = limb.as_canonical_u64();
            if value >= 1 << 30 {
                return None;
            }
            packed = (packed << 30) | u128::from(value);
        }
        digest[half * 15..(half + 1) * 15].copy_from_slice(&packed.to_be_bytes()[1..]);
    }
    Some(digest)
}

pub fn keccak240_leaf<F: PrimeField64>(scalars: &[F]) -> [F; 8] {
    let mut hasher = Keccak256::new();
    hasher.update([0x00]);
    for scalar in scalars {
        hasher.update((scalar.as_canonical_u64() as u32).to_be_bytes());
    }
    encode_keccak240(&hasher.finalize().into())
}

pub fn keccak240_node<F: PrimeField64>(left: &[F; 8], right: &[F; 8]) -> Option<[F; 8]> {
    let left = decode_keccak240(left)?;
    let right = decode_keccak240(right)?;
    Some(encode_keccak240(&keccak256(&[&[0x01], &left, &right])))
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::PrimeCharacteristicRing;
    use koala_bear::KoalaBear;

    #[test]
    fn keccak_uses_ethereum_padding() {
        assert_eq!(
            keccak256(&[b""]),
            [
                0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c, 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0, 0xe5,
                0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b, 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70,
            ]
        );
    }

    #[test]
    fn digest_encoding_preserves_all_240_bits_and_rejects_extra_bits() {
        let original = std::array::from_fn(|i| i as u8 * 7 + 3);
        let encoded = encode_keccak240::<KoalaBear>(&original);
        let decoded = decode_keccak240(&encoded).unwrap();
        assert_eq!(&decoded[..30], &original[..30]);
        assert_eq!(&decoded[30..], &[0, 0]);
        let mut invalid = encoded;
        invalid[3] = KoalaBear::from_u32(1 << 30);
        assert!(decode_keccak240(&invalid).is_none());
        assert!(keccak240_node(&encoded, &invalid).is_none());
    }

    #[test]
    fn leaf_and_node_encodings_are_domain_separated() {
        let leaf = keccak240_leaf(&[KoalaBear::from_u32(0x01020304)]);
        let expected = encode_keccak240(&keccak256(&[&[0, 1, 2, 3, 4]]));
        assert_eq!(leaf, expected);
        let digest = decode_keccak240(&leaf).unwrap();
        assert_eq!(
            keccak240_node(&leaf, &leaf).unwrap(),
            encode_keccak240(&keccak256(&[&[1], &digest, &digest]))
        );
    }

    #[test]
    fn keccak_merkle_vectors_match_independent_reference() {
        let left = keccak240_leaf(&std::array::from_fn::<_, 8, _>(|i| KoalaBear::from_usize(i)));
        let right = keccak240_leaf(&std::array::from_fn::<_, 8, _>(|i| KoalaBear::from_usize(i + 8)));
        assert_eq!(
            left.map(|x| x.as_canonical_u64()),
            [
                767845451, 316274549, 822290521, 694784522, 1003385732, 888782743, 570097107, 833051967
            ]
        );
        assert_eq!(
            right.map(|x| x.as_canonical_u64()),
            [
                1042418221, 340136717, 1014038459, 516515936, 90680752, 1010989489, 936432453, 950099671
            ]
        );
        assert_eq!(
            keccak240_node(&left, &right).unwrap().map(|x| x.as_canonical_u64()),
            [
                675110709, 72503284, 948112723, 22471718, 704598758, 1007750487, 156448890, 237370740
            ]
        );
    }
}
