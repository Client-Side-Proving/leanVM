use std::collections::BTreeMap;

use crate::GuestError;

fn invalid() -> GuestError {
    GuestError::Fixture("full-ZK Direct opening has an invalid fixed layout".to_string())
}

struct Layout<'a> {
    words: &'a [u32],
    cursor: usize,
    constants: Vec<String>,
    checks: Vec<String>,
}

impl Layout<'_> {
    fn check_word(&mut self, expected: usize) -> Result<(), GuestError> {
        if self.words.get(self.cursor).copied().map(|word| word as usize) != Some(expected) {
            return Err(invalid());
        }
        self.checks.push(format!("assert proof[{}] == {expected}", self.cursor));
        self.cursor += 1;
        Ok(())
    }

    fn opening(
        &mut self,
        name: &str,
        queries: usize,
        width: usize,
        degree: usize,
        height: usize,
    ) -> Result<(), GuestError> {
        self.check_word(queries)?;
        self.constants.push(format!("{name}_FIRST_ROW = {}", self.cursor + 1));
        for _ in 0..queries {
            if self.words.get(self.cursor).copied().map(|word| word as usize) != Some(width) {
                return Err(invalid());
            }
            // opening_rows emits every row-width assertion in the guest.
            self.cursor += 1 + width * degree;
        }
        let siblings = self.words.get(self.cursor).copied().ok_or_else(invalid)? as usize;
        if siblings > queries * height {
            return Err(invalid());
        }
        self.check_word(siblings)?;
        self.constants.push(format!("{name}_SIBLINGS = {}", self.cursor));
        self.constants.push(format!("{name}_SIBLING_COUNT = {siblings}"));
        self.cursor += siblings * 8;
        if self.cursor > self.words.len() {
            return Err(invalid());
        }
        Ok(())
    }
}

pub(crate) fn replacements(words: &[u32]) -> Result<BTreeMap<String, String>, GuestError> {
    if words.get(8).copied().map(|word| word as usize) != Some(words.len()) {
        return Err(invalid());
    }
    // The fixed Direct profile reaches its final openings after all blinded
    // messages and randomness. Merkle sibling counts depend on the transcript.
    let mut layout = Layout {
        words,
        cursor: 2754,
        constants: Vec::new(),
        checks: Vec::new(),
    };
    layout.opening("SOURCE_CARRIED", 18, 2, 1, 10)?;
    layout.opening("SOURCE_FRESH", 18, 1, 5, 10)?;
    layout.check_word(3)?;
    for (group, width) in [8, 4, 1].into_iter().enumerate() {
        layout.opening(&format!("MASK_{group}_CARRIED"), 30, width, 5, 9)?;
        layout.opening(&format!("MASK_{group}_FRESH"), 30, width, 5, 9)?;
    }
    if layout.cursor != words.len() {
        return Err(invalid());
    }
    Ok(BTreeMap::from([
        ("FULL_ZK_WORDS_PLACEHOLDER".to_string(), words.len().to_string()),
        (
            "FULL_ZK_LAYOUT_CONSTANTS_PLACEHOLDER".to_string(),
            layout.constants.join("\n"),
        ),
        (
            "FULL_ZK_OPENING_COUNTS_PLACEHOLDER".to_string(),
            layout.checks.join("\n    "),
        ),
    ]))
}

#[cfg(test)]
mod tests {
    use super::replacements;
    use crate::{full_zk_direct_poseidon1_words, full_zk_direct_poseidon2_words};

    #[test]
    fn direct_layout_accepts_both_profiles_and_rejects_malformed_boundaries() {
        for words in [
            full_zk_direct_poseidon1_words().unwrap(),
            full_zk_direct_poseidon2_words().unwrap(),
        ] {
            let result = replacements(&words).unwrap();
            assert_eq!(result["FULL_ZK_WORDS_PLACEHOLDER"], words.len().to_string());
            assert_eq!(result["FULL_ZK_OPENING_COUNTS_PLACEHOLDER"].lines().count(), 17);
            for (offset, value) in [(2754, 17), (2755, 3), (2809, u32::MAX)] {
                let mut changed = words.clone();
                changed[offset] = value;
                assert!(replacements(&changed).is_err());
            }
            let mut truncated = words[..words.len() - 1].to_vec();
            truncated[8] = truncated.len() as u32;
            assert!(replacements(&truncated).is_err());
            let mut trailing = words.clone();
            trailing.push(0);
            trailing[8] = trailing.len() as u32;
            assert!(replacements(&trailing).is_err());
        }
    }
}
