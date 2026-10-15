//! Native WHIR parameter enumeration. Work counts are screening estimates.
use std::{collections::HashSet, error::Error};

use backend::{WhirConfig, WhirConfigBuilder};
use lean_prover::WhirExecutionProfile;
use lean_vm::EF;
use serde_json::json;

fn main() -> Result<(), Box<dyn Error>> {
    let n_vars: usize = std::env::args()
        .nth(1)
        .ok_or("expected polynomial variable count")?
        .parse()?;
    let mut seen = HashSet::new();
    for first in 3..=9 {
        for subsequent in 3..=6 {
            for reduction in 1..=first {
                for log_inv_rate in 1..=6 {
                    for threshold in subsequent - 1..=8 {
                        for grinding_bits in [16, 20, 22, 24, 25, 26, 27, 28] {
                            let profile = WhirExecutionProfile {
                                security_bits: 100,
                                grinding_bits,
                                first_folding_factor: first,
                                subsequent_folding_factor: subsequent,
                                rs_domain_initial_reduction_factor: reduction,
                                max_num_variables_to_send_coeffs: threshold,
                                log_inv_rate,
                            };
                            if profile.validate_for_n_vars(n_vars).is_err() {
                                continue;
                            }
                            let builder: WhirConfigBuilder = profile.whir_config();
                            let config = WhirConfig::<EF>::new(&builder, n_vars);
                            let mut rounds = config.round_parameters.clone();
                            rounds.push(config.final_round_config());
                            let signature = format!(
                                "{first}/{subsequent}/{reduction}/{log_inv_rate}/{grinding_bits}/{}",
                                config.final_sumcheck_rounds
                            );
                            if !seen.insert(signature) {
                                continue;
                            }
                            let folding_terms: usize =
                                rounds.iter().map(|r| r.num_queries * (1 << r.folding_factor)).sum();
                            let hash_calls: usize = rounds
                                .iter()
                                .enumerate()
                                .map(|(i, r)| {
                                    let leaf_chunks =
                                        ((1usize << r.folding_factor) * if i == 0 { 1 } else { 5 }).div_ceil(8);
                                    r.num_queries * (leaf_chunks + r.domain_size.ilog2() as usize - r.folding_factor)
                                })
                                .sum();
                            let grinding_trials: u64 = (1u64 << config.starting_folding_pow_bits) * first as u64
                                + config
                                    .round_parameters
                                    .iter()
                                    .map(|r| {
                                        (1u64 << r.query_pow_bits) + (1u64 << r.folding_pow_bits) * subsequent as u64
                                    })
                                    .sum::<u64>()
                                + (1u64 << config.final_query_pow_bits);
                            let final_terms = config.final_queries * (1usize << config.final_sumcheck_rounds);
                            println!(
                                "{}",
                                json!({
                                    "profile": profile,
                                "n_vars": n_vars,
                                "initial_encoded_base_fields": 1u64 << (n_vars + log_inv_rate),
                                "initial_merkle_leaves": 1u64 << (n_vars + log_inv_rate - first),
                                    "measurement": "native parameter derivation; workload estimates only",
                                    "queries": rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>(),
                                    "query_grinding": rounds.iter().map(|r| r.query_pow_bits).collect::<Vec<_>>(),
                                    "folding_grinding": std::iter::once(config.starting_folding_pow_bits).chain(config.round_parameters.iter().map(|r| r.folding_pow_bits)).collect::<Vec<_>>(),
                                    "folding_factors": rounds.iter().map(|r| r.folding_factor).collect::<Vec<_>>(),
                                    "path_heights": rounds.iter().map(|r| r.domain_size.ilog2() as usize-r.folding_factor).collect::<Vec<_>>(),
                                    "final_n_vars": config.final_sumcheck_rounds,
                                    "folding_terms": folding_terms,
                                    "final_evaluation_terms": final_terms,
                                    "independent_path_hash_calls": hash_calls,
                                    "expected_grinding_trials": grinding_trials,
                                    "screening_score": folding_terms + final_terms + 8 * hash_calls,
                                })
                            );
                        }
                    }
                }
            }
        }
    }
    Ok(())
}
