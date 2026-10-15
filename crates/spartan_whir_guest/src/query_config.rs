use serde_json::Value;

use crate::GuestError;

fn integer(value: &Value, name: &str) -> Result<u64, GuestError> {
    value[name]
        .as_u64()
        .ok_or_else(|| GuestError::Fixture(format!("missing or invalid query parameter: {name}")))
}

fn round_positions(round: &Value) -> Result<usize, GuestError> {
    let requested = integer(round, "num_queries")?;
    let domain = integer(round, "domain_size")?;
    let folding = integer(round, "folding_factor")?;
    if !domain.is_power_of_two() || folding >= u64::BITS as u64 || domain >> folding == 0 {
        return Err(GuestError::Fixture("invalid folded query domain".to_string()));
    }
    let expected = requested.min(domain >> folding);
    let exported = integer(round, "query_positions")?;
    if exported != expected {
        return Err(GuestError::Fixture(
            "exported query positions do not match the capped native request".to_string(),
        ));
    }
    usize::try_from(exported).map_err(|_| GuestError::Fixture("query positions exceed the host range".to_string()))
}

pub(crate) fn positions(config: &Value) -> Result<Vec<usize>, GuestError> {
    let rounds = config["rounds"]
        .as_array()
        .ok_or_else(|| GuestError::Fixture("missing WHIR rounds".to_string()))?;
    let mut result = rounds.iter().map(round_positions).collect::<Result<Vec<_>, _>>()?;
    let final_round = &config["final_round"];
    if integer(config, "final_queries")? != integer(final_round, "num_queries")? {
        return Err(GuestError::Fixture(
            "final query request disagrees with its round configuration".to_string(),
        ));
    }
    result.push(round_positions(final_round)?);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::round_positions;
    use serde_json::json;

    #[test]
    fn capped_positions_are_checked_for_every_domain_width() {
        for bits in [1, 2, 7, 14, 15, 18, 24] {
            let domain = 1u64 << bits;
            for requested in [domain - 1, domain, domain + 1] {
                let mut round = json!({
                    "num_queries": requested,
                    "query_positions": requested.min(domain),
                    "domain_size": domain * 8,
                    "folding_factor": 3,
                });
                assert_eq!(round_positions(&round).unwrap(), requested.min(domain) as usize);
                round["query_positions"] = json!(requested.min(domain) + 1);
                assert!(round_positions(&round).is_err());
                round.as_object_mut().unwrap().remove("query_positions");
                assert!(round_positions(&round).is_err());
            }
        }
        for (domain, folding) in [(0, 0), (3, 0), (128, 8), (128, 64)] {
            let round =
                json!({"num_queries": 1, "query_positions": 1, "domain_size": domain, "folding_factor": folding});
            assert!(round_positions(&round).is_err());
        }
    }
}
