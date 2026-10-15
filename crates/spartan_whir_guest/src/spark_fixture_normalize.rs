use serde_json::{Value, json};

use crate::{FULL_ZK_SPARK_POSEIDON1_WORDS, GuestError, SparkGuestFixture};

impl SparkGuestFixture {
    /// Reserve a fixed capacity for every Merkle sibling vector. The actual
    /// sibling count remains in the input and controls verification. Unused
    /// capacity is transport padding and is never observed by Fiat-Shamir.
    /// Capacities depend only on the configured query count and tree height.
    pub fn with_fixed_sibling_storage(mut self) -> Result<Self, GuestError> {
        if self.layout["fixed_sibling_storage"] == true {
            return Ok(self);
        }
        let original = self.layout["entries"].clone();
        let entries = original.as_object().ok_or_else(|| invalid("missing layout entries"))?;
        let total = number(&self.layout["total_words"])?;
        if total > self.words.len() {
            return Err(invalid("canonical input exceeds supplied words"));
        }
        let mut ordered = entries.iter().collect::<Vec<_>>();
        ordered.sort_by_key(|(_, entry)| {
            (
                entry["offset"].as_u64().unwrap_or(u64::MAX),
                entry["words"].as_u64().unwrap_or(u64::MAX),
            )
        });
        let mut words = Vec::new();
        let mut previous_end = 0;
        let mut updated = serde_json::Map::new();
        for (name, entry) in ordered {
            let start = number(&entry["offset"])?;
            let len = number(&entry["words"])?;
            let end = start.checked_add(len).ok_or_else(|| invalid("layout overflow"))?;
            if start < previous_end || end > total {
                return Err(invalid("overlapping or out-of-bounds layout entries"));
            }
            words.extend_from_slice(&self.words[previous_end..start]);
            let offset = words.len();
            words.extend_from_slice(&self.words[start..end]);
            let width = if let Some(opening) = name.strip_suffix(".siblings") {
                let (queries, height) = opening_geometry(&self.constants, opening)?;
                let count = |suffix: &str| -> Result<usize, GuestError> {
                    let at = number(&original[format!("{opening}.{suffix}")]["offset"])?;
                    self.words
                        .get(at)
                        .map(|v| *v as usize)
                        .ok_or_else(|| invalid("count outside input"))
                };
                let capacity = sibling_capacity(queries, height)?
                    .checked_mul(8)
                    .ok_or_else(|| invalid("sibling capacity overflow"))?;
                if count("rows_count")? != queries || count("siblings_count")?.checked_mul(8) != Some(len) {
                    return Err(invalid("Merkle opening counts disagree with the configured geometry"));
                }
                if len > capacity {
                    return Err(invalid("Merkle sibling count exceeds the pruned binary tree bound"));
                }
                if offset
                    .checked_add(capacity)
                    .is_none_or(|end| end > FULL_ZK_SPARK_POSEIDON1_WORDS)
                {
                    return Err(invalid("fixed sibling storage exceeds the guest input capacity"));
                }
                words.resize(offset + capacity, 0);
                capacity
            } else {
                len
            };
            updated.insert(name.clone(), json!({"offset": offset, "words": width}));
            previous_end = end;
        }
        words.extend_from_slice(&self.words[previous_end..total]);
        let new_total = words.len();
        if new_total > FULL_ZK_SPARK_POSEIDON1_WORDS {
            return Err(invalid("fixed sibling storage exceeds the guest input capacity"));
        }
        *words.get_mut(8).ok_or_else(|| invalid("missing input header"))? = new_total as u32;
        words.resize(FULL_ZK_SPARK_POSEIDON1_WORDS, 0);
        self.words = words;
        self.layout["entries"] = Value::Object(updated);
        self.layout["original_entries"] = original;
        self.layout["total_words"] = json!(new_total);
        self.layout["fixed_sibling_storage"] = json!(true);
        Ok(self)
    }

    /// Translate a mutation offset from the exported canonical input into the
    /// fixed-capacity input. Existing non-normalized fixtures use identity.
    pub fn normalized_offset(&self, original_offset: usize) -> Result<usize, GuestError> {
        let Some(entries) = self.layout["original_entries"].as_object() else {
            return Ok(original_offset);
        };
        for (name, entry) in entries {
            let start = number(&entry["offset"])?;
            let len = number(&entry["words"])?;
            if (start..start + len).contains(&original_offset) {
                return Ok(number(&self.layout["entries"][name]["offset"])? + original_offset - start);
            }
        }
        Err(invalid("mutation offset is outside the canonical layout"))
    }
}

fn invalid(message: &str) -> GuestError {
    GuestError::Fixture(message.to_owned())
}

/// Maximum number of siblings for at most `queries` leaves of a binary tree.
/// With d distinct leaves, the frontier has at most min(d, 2^level) nodes at
/// each level. Summing absent siblings gives 2^ceil(log2(d))+(h-ceil(log2(d))-1)*d.
/// This increases up to half of the leaves, which also covers duplicate queries.
fn sibling_capacity(queries: usize, height: usize) -> Result<usize, GuestError> {
    let leaves = 1usize
        .checked_shl(u32::try_from(height).map_err(|_| invalid("Merkle height overflow"))?)
        .ok_or_else(|| invalid("Merkle height overflow"))?;
    if queries == 0 || queries > leaves {
        return Err(invalid("query count outside the Merkle domain"));
    }
    if height == 0 {
        return Ok(0);
    }
    let distinct = queries.min(leaves / 2);
    let width = distinct.next_power_of_two();
    let depth = width.ilog2() as usize;
    (height - depth - 1)
        .checked_mul(distinct)
        .and_then(|n| n.checked_add(width))
        .ok_or_else(|| invalid("sibling capacity overflow"))
}

fn number(value: &Value) -> Result<usize, GuestError> {
    value
        .as_u64()
        .and_then(|v| usize::try_from(v).ok())
        .ok_or_else(|| invalid("invalid geometry integer"))
}

fn log_domain(value: &Value) -> Result<usize, GuestError> {
    let domain = number(value)?;
    if !domain.is_power_of_two() {
        return Err(invalid("Merkle domain must be a power of two"));
    }
    Ok(domain.ilog2() as usize)
}

fn indexed<'a>(path: &'a str, prefix: &str) -> Option<(usize, &'a str)> {
    let suffix = path.strip_prefix(prefix)?;
    let (index, remainder) = suffix.split_once(']')?;
    Some((index.parse().ok()?, remainder))
}

fn round_geometry(config: &Value, suffix: &str) -> Result<(usize, usize), GuestError> {
    let round = if suffix == ".final_openings" {
        &config["final_round"]
    } else if let Some((round, ".openings")) = indexed(suffix, ".rounds[") {
        &config["rounds"][round]
    } else {
        return Err(invalid("unsupported WHIR opening layout"));
    };
    let height = log_domain(&round["domain_size"])?
        .checked_sub(number(&round["folding_factor"])?)
        .ok_or_else(|| invalid("folding exceeds the Merkle domain"))?;
    Ok((number(&round["query_positions"])?, height))
}

fn opening_geometry(constants: &Value, path: &str) -> Result<(usize, usize), GuestError> {
    if let Some(suffix) = path.strip_prefix("proof.spark.fixed.value_proof") {
        return round_geometry(&constants["fixed_value_whir"], suffix);
    }
    if let Some((group, suffix)) = indexed(path, "proof.spark.read.groups[") {
        return round_geometry(
            &constants["read_whir"][group],
            suffix
                .strip_prefix(".proof")
                .ok_or_else(|| invalid("invalid read opening layout"))?,
        );
    }
    let common = &constants["common"];
    if let Some(suffix) = path.strip_prefix("proof.pcs")
        && suffix.starts_with(".rounds[")
    {
        return round_geometry(common, suffix);
    }
    let base = path
        .strip_prefix("proof.pcs.base_case.")
        .ok_or_else(|| invalid("unrecognized Merkle opening layout"))?;
    if matches!(base, "source_openings" | "fresh_main_openings") {
        return Ok((
            number(&common["final_round"]["query_positions"])?,
            log_domain(&common["source_code"]["domain_size"])?,
        ));
    }
    let groups = common["base_case_mask_groups"]
        .as_array()
        .ok_or_else(|| invalid("missing mask groups"))?;
    let group = if let Some((group, "")) = indexed(base, "carried_mask_openings[") {
        group
    } else if let Some((batch, "")) = indexed(base, "fresh_mask_openings[") {
        if common["fresh_mask_batching"] == "same_height" {
            let mut heights = Vec::new();
            let mut first_groups = Vec::new();
            for (index, group) in groups.iter().enumerate() {
                let height = log_domain(&group["shape"]["domain_size"])?;
                if !heights.contains(&height) {
                    heights.push(height);
                    first_groups.push(index);
                }
            }
            *first_groups
                .get(batch)
                .ok_or_else(|| invalid("fresh mask batch outside geometry"))?
        } else {
            batch
        }
    } else {
        return Err(invalid("unsupported base-case opening layout"));
    };
    let group = groups
        .get(group)
        .ok_or_else(|| invalid("mask group outside geometry"))?;
    Ok((
        number(&common["mask_queries"])?,
        log_domain(&group["shape"]["domain_size"])?,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(siblings: usize) -> SparkGuestFixture {
        let total = 13 + siblings * 8;
        let mut words = vec![0; FULL_ZK_SPARK_POSEIDON1_WORDS];
        words[8] = total as u32;
        words[9] = 2;
        words[10] = siblings as u32;
        for (i, value) in words[11..11 + siblings * 8].iter_mut().enumerate() {
            *value = i as u32 + 100;
        }
        words[11 + siblings * 8] = 12345;
        words[12 + siblings * 8] = 67890;
        SparkGuestFixture {
            constants: json!({"fixed_value_whir":{"final_round":{"domain_size":16,"folding_factor":1,"query_positions":2}}}),
            statement: json!({}),
            layout: json!({"total_words":total,"entries":{
                "header":{"offset":0,"words":9},
                "proof.spark.fixed.value_proof.final_openings.rows_count":{"offset":9,"words":1},
                "proof.spark.fixed.value_proof.final_openings.siblings_count":{"offset":10,"words":1},
                "proof.spark.fixed.value_proof.final_openings.siblings":{"offset":11,"words":siblings*8},
                "tail":{"offset":11+siblings*8,"words":2}
            }}),
            words,
        }
    }

    #[test]
    fn sibling_lengths_share_layout_and_preserve_actual_contents() {
        let a = fixture(2).with_fixed_sibling_storage().unwrap();
        let b = fixture(3).with_fixed_sibling_storage().unwrap();
        assert_eq!(a.layout["entries"], b.layout["entries"]);
        assert_eq!(a.layout["total_words"], b.layout["total_words"]);
        assert_eq!(a.words[10], 2);
        assert_eq!(b.words[10], 3);
        assert_eq!(&a.words[11..27], &fixture(2).words[11..27]);
        assert!(a.words[27..43].iter().all(|v| *v == 0));
        assert_eq!(&a.words[43..45], &[12345, 67890]);
        assert_eq!(a.normalized_offset(27).unwrap(), 43);
        assert_eq!(b.normalized_offset(35).unwrap(), 43);
    }

    #[test]
    fn rejects_sibling_overflow_and_inconsistent_counts() {
        assert!(fixture(5).with_fixed_sibling_storage().is_err());
        let mut bad = fixture(2);
        bad.words[10] = 1;
        assert!(bad.with_fixed_sibling_storage().is_err());
        let mut bad = fixture(2);
        bad.words[9] = 3;
        assert!(bad.with_fixed_sibling_storage().is_err());
    }

    #[test]
    fn sibling_bound_matches_all_small_binary_tree_frontiers() {
        for height in 0..=4 {
            let leaves = 1usize << height;
            let mut maxima = vec![0; leaves + 1];
            for subset in 1usize..1usize << leaves {
                let distinct = subset.count_ones() as usize;
                let mut frontier = subset;
                let mut siblings = 0;
                for level in 0..height {
                    let mut parents = 0;
                    for pair in 0..(leaves >> (level + 1)) {
                        let children = (frontier >> (pair * 2)) & 3;
                        siblings += usize::from(children == 1 || children == 2);
                        parents |= usize::from(children != 0) << pair;
                    }
                    frontier = parents;
                }
                maxima[distinct] = maxima[distinct].max(siblings);
            }
            for queries in 1..=leaves {
                assert_eq!(
                    sibling_capacity(queries, height).unwrap(),
                    *maxima[1..=queries].iter().max().unwrap()
                );
            }
        }
        assert!(sibling_capacity(0, 3).is_err());
        assert!(sibling_capacity(9, 3).is_err());
        assert!(sibling_capacity(1, usize::MAX).is_err());
    }
}
