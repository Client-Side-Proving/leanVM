#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use std::fmt::Display;

mod grouped_execution;
mod profile;
pub use grouped_execution::{GROUPED_BATCHING_POW_BITS, grouped_logup_mode_observation};
pub mod prove_execution;
mod public_memory;
pub use profile::{
    TWO_COMMITMENT_WHIR_BATCHING_POW_BITS, TWO_COMMITMENT_WHIR_MODE_TAG, TWO_COMMITMENT_WHIR_STATEMENT_TAG,
    TwoCommitmentWhirPreprocessedCommitment, TwoCommitmentWhirProverInput, TwoCommitmentWhirStatementBinding,
    TwoCommitmentWhirVerifierInput, WhirExecutionProfile, two_commitment_fiat_shamir_domain_sep,
    two_commitment_fiat_shamir_static_descriptor, two_commitment_statement_observation,
};
pub use public_memory::PublicMemoryRegion;
mod trace_gen;
pub mod verify_execution;

use backend::*;
use lean_vm::*;
#[cfg(test)]
mod test_zkvm;

pub use trace_gen::{ExecutionTrace, get_execution_trace};

// Right now, hash digests = 8 koala-bear (p = 2^31 - 2^24 + 1, i.e. ≈ 31 bits per field element)
pub const SECURITY_BITS: usize = 121;

pub const GRINDING_BITS: usize = 16;
pub const MAX_NUM_VARIABLES_TO_SEND_COEFFS: usize = 8;
pub const WHIR_INITIAL_FOLDING_FACTOR: usize = 9;
pub const WHIR_SUBSEQUENT_FOLDING_FACTOR: usize = 5;
pub const RS_DOMAIN_INITIAL_REDUCTION_FACTOR: usize = 5;

pub const SNARK_DOMAIN_SEP: [F; 8] = F::new_array([
    130704175, 1303721200, 493664240, 1035493700, 2063844858, 1410214009, 1938905908, 1696767928,
]);

pub fn fiat_shamir_domain_sep(bytecode: &Bytecode) -> [F; 8] {
    poseidon16_compress_pair(bytecode.hash(), &SNARK_DOMAIN_SEP)
}

pub fn default_whir_config(starting_log_inv_rate: usize) -> WhirConfigBuilder {
    assert!(0 < starting_log_inv_rate);
    assert!(starting_log_inv_rate <= MAX_WHIR_LOG_INV_RATE);
    WhirConfigBuilder {
        folding_factor: FoldingFactor::new(WHIR_INITIAL_FOLDING_FACTOR, WHIR_SUBSEQUENT_FOLDING_FACTOR),
        soundness_type: if cfg!(feature = "prox-gaps-conjecture") {
            SecurityAssumption::CapacityBound // TODO update formula with State of the Art Conjecture
        } else {
            SecurityAssumption::JohnsonBound
        },
        pow_bits: GRINDING_BITS,
        max_num_variables_to_send_coeffs: MAX_NUM_VARIABLES_TO_SEND_COEFFS,
        rs_domain_initial_reduction_factor: RS_DOMAIN_INITIAL_REDUCTION_FACTOR,
        security_level: SECURITY_BITS,
        starting_log_inv_rate,
    }
}

pub(crate) fn check_rate(log_inv_rate: usize) -> Result<(), ProofError> {
    if (MIN_WHIR_LOG_INV_RATE..=MAX_WHIR_LOG_INV_RATE).contains(&log_inv_rate) {
        Ok(())
    } else {
        Err(ProofError::InvalidRate)
    }
}

#[derive(Debug, Clone)]
pub enum ProverError {
    TooBigTable(TooBigTableError),
    Runner(RunnerError),
    InvalidRate,
    InvalidGroupedLogup(&'static str),
    InvalidWhirProfile(&'static str),
    InvalidPublicMemory(&'static str),
    InvalidTwoCommitmentWhir(&'static str),
}

impl From<TooBigTableError> for ProverError {
    fn from(err: TooBigTableError) -> Self {
        Self::TooBigTable(err)
    }
}

impl From<RunnerError> for ProverError {
    fn from(err: RunnerError) -> Self {
        Self::Runner(err)
    }
}

impl Display for ProverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooBigTable(e) => write!(f, "{}", e),
            Self::Runner(e) => write!(f, "{}", e),
            Self::InvalidWhirProfile(reason) => {
                write!(f, "Invalid WHIR execution profile: {reason}")
            }
            Self::InvalidPublicMemory(reason) => {
                write!(f, "Invalid public memory region: {reason}")
            }
            Self::InvalidTwoCommitmentWhir(reason) => {
                write!(f, "Invalid two-commitment WHIR input: {reason}")
            }
            Self::InvalidGroupedLogup(reason) => write!(f, "Invalid grouped LogUp input: {reason}"),
            Self::InvalidRate => write!(
                f,
                "LeanVM supports rate 1/2, 1/4, 1/8 and 1/16 (log_inv_rate in {{1, 2, 3, 4}})"
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use backend::{PrimeCharacteristicRing, default_koalabear_poseidon1_16, hash_slice_rtl, poseidon16_compress_pair};
    use lean_vm::F;
    use rec_aggregation::{get_aggregation_bytecode, init_aggregation_bytecode};

    #[test]
    fn compute_snark_domain_sep() {
        init_aggregation_bytecode();
        let recursion_bytecode_hash = get_aggregation_bytecode().hash();
        let name_fe = "leanVM-0.6.0"
            .as_bytes()
            .iter()
            .map(|b| F::from_u8(*b))
            .collect::<Vec<_>>();
        let mut prefix_free_name_fe = vec![F::ZERO; 8];
        let len = name_fe.len();
        prefix_free_name_fe.extend(name_fe);
        while prefix_free_name_fe.len() % 8 != 7 {
            prefix_free_name_fe.push(F::ZERO);
        }
        prefix_free_name_fe.push(F::from_u64(len as u64));
        let comp = default_koalabear_poseidon1_16();
        let name_hash = hash_slice_rtl::<_, _, _, 8, 8>(&comp, &prefix_free_name_fe);

        // We incorporate the recursion program hash, containing all the verifier logic, into fiat shamir domain separator
        // (likely not necessary but why not, is there a cleaner approach?)
        let domain_sep = poseidon16_compress_pair(&name_hash, recursion_bytecode_hash);

        println!("Computed SNARK_DOMAIN_SEP: {:?}", domain_sep); // We dont assert equality here to avoid the pain of having to update the hardcoded SNARK_DOMAIN_SEP every time we change the recursion program
    }
}
