use super::*;
use backend::{Field, PrimeField32, TwoAdicField};
use std::ops::Range;
use std::path::Path;

/// Circuit-specific verifier data exported after native key authentication.
/// Offsets come from the canonical word layout; batch membership comes from the fixed mask geometry.
#[derive(Clone, Debug)]
pub struct SparkGuestFixture {
    pub constants: Value,
    pub statement: Value,
    pub layout: Value,
    pub words: Vec<u32>,
}

impl SparkGuestFixture {
    pub fn embedded() -> Result<&'static Self, GuestError> {
        static FIXTURE: std::sync::OnceLock<Result<SparkGuestFixture, String>> = std::sync::OnceLock::new();
        FIXTURE
            .get_or_init(|| {
                Self::parse(
                    FULL_ZK_SPARK_POSEIDON1_CONSTANTS_JSON,
                    FULL_ZK_SPARK_POSEIDON1_STATEMENT_JSON,
                    include_str!("../testdata/full_zk_spark_poseidon1/full_zk_spark_guest_layout.json"),
                    FULL_ZK_SPARK_POSEIDON1_WORD_BYTES,
                )
                .map_err(|error| error.to_string())
            })
            .as_ref()
            .map_err(|error| GuestError::Fixture(error.clone()))
    }

    pub fn from_directory(directory: &Path) -> Result<Self, GuestError> {
        let read =
            |name: &str| std::fs::read(directory.join(name)).map_err(|error| GuestError::Fixture(error.to_string()));
        let constants = read("full_zk_spark_guest_constants.json")?;
        let statement = read("full_zk_spark_statement.json")?;
        let layout = read("full_zk_spark_guest_layout.json")?;
        let parse =
            |bytes: &[u8]| serde_json::from_slice(bytes).map_err(|error| GuestError::Fixture(error.to_string()));
        let result = Self {
            constants: parse(&constants)?,
            statement: parse(&statement)?,
            layout: parse(&layout)?,
            words: decode_word_bytes(&read("full_zk_spark_guest_input.words")?)?,
        };
        result.validate()?;
        Ok(result)
    }

    fn parse(constants: &str, statement: &str, layout: &str, words: &[u8]) -> Result<Self, GuestError> {
        let parse = |text: &str| serde_json::from_str(text).map_err(|error| GuestError::Fixture(error.to_string()));
        let result = Self {
            constants: parse(constants)?,
            statement: parse(statement)?,
            layout: parse(layout)?,
            words: decode_word_bytes(words)?,
        };
        result.validate()?;
        Ok(result)
    }

    pub fn canonical_words(&self) -> usize {
        self.layout["total_words"].as_u64().unwrap() as usize
    }

    fn validate(&self) -> Result<(), GuestError> {
        let total = self.layout["total_words"]
            .as_u64()
            .ok_or_else(|| GuestError::Fixture("missing canonical word count".into()))? as usize;
        if total > FULL_ZK_SPARK_POSEIDON1_WORDS
            || self.words.len() != FULL_ZK_SPARK_POSEIDON1_WORDS
            || self.words[8] as usize != total
        {
            return Err(GuestError::Fixture("inconsistent canonical SPARK word count".into()));
        }
        let entries = self.layout["entries"]
            .as_object()
            .ok_or_else(|| GuestError::Fixture("missing layout entries".into()))?;
        for (name, entry) in entries {
            let start = entry["offset"]
                .as_u64()
                .ok_or_else(|| GuestError::Fixture(format!("invalid offset: {name}")))?;
            let len = entry["words"]
                .as_u64()
                .ok_or_else(|| GuestError::Fixture(format!("invalid width: {name}")))?;
            if start.checked_add(len).is_none_or(|end| end > total as u64) {
                return Err(GuestError::Fixture(format!(
                    "layout entry outside canonical input: {name}"
                )));
            }
        }
        self.validate_protocol_geometry()?;
        self.validate_mask_geometry()?;
        self.validate_query_positions()?;
        Ok(())
    }

    fn validate_query_positions(&self) -> Result<(), GuestError> {
        query_config::positions(&self.constants["common"])?;
        for config in std::iter::once(&self.constants["fixed_value_whir"]).chain(
            self.constants["read_whir"]
                .as_array()
                .ok_or_else(|| GuestError::Fixture("missing read WHIR configurations".into()))?,
        ) {
            query_config::positions(config)?;
        }
        // Audit columns share the fixed-value commitment in this guest. Its
        // separate exported configuration still requires a valid capped count.
        query_config::positions(&self.constants["fixed_audit_whir"])?;
        Ok(())
    }

    fn validate_protocol_geometry(&self) -> Result<(), GuestError> {
        let common = &self.constants["common"];
        let shape = &common["canonical_shape"];
        let number = |value: &Value, name: &str| -> Result<usize, GuestError> {
            value[name]
                .as_u64()
                .and_then(|n| usize::try_from(n).ok())
                .ok_or_else(|| GuestError::Fixture(format!("invalid SPARK geometry field: {name}")))
        };
        let constraints = number(shape, "constraints")?;
        let variables = number(shape, "variables")?;
        let public_inputs = number(shape, "public_inputs")?;
        if !constraints.is_power_of_two()
            || !variables.is_power_of_two()
            || public_inputs == 0
            || public_inputs >= variables
            || number(common, "num_outer_rounds")? != constraints.ilog2() as usize
            || number(common, "num_inner_rounds")? != variables.ilog2() as usize + 1
            || number(common, "ell_zk")? != 3
            || number(&common["sumcheck_mask"], "message_len")? != 3
            || self.layout["entries"]["instance.public_inputs.values"]["words"] != public_inputs
        {
            return Err(GuestError::Fixture("inconsistent Spartan application geometry".into()));
        }
        let folding = common["folding_schedule"]
            .as_array()
            .ok_or_else(|| GuestError::Fixture("missing relation folding schedule".into()))?;
        let rounds = common["rounds"]
            .as_array()
            .ok_or_else(|| GuestError::Fixture("missing hiding-WHIR rounds".into()))?;
        let switches = common["switch_masks"]
            .as_array()
            .ok_or_else(|| GuestError::Fixture("missing hiding-WHIR switch masks".into()))?;
        // The source opening is over an extension-field commitment introduced
        // by a switch. Configurations with no switch need a base-field opening.
        if rounds.is_empty() || folding.len() != rounds.len() + 1 || switches.len() != rounds.len() {
            return Err(GuestError::Fixture("unsupported hiding-WHIR switch geometry".into()));
        }
        for (round, mask) in rounds.iter().zip(switches) {
            if number(mask, "message_len")? != number(round, "num_queries")? + number(round, "ood_samples")? {
                return Err(GuestError::Fixture(
                    "switch mask disagrees with query and OOD budgets".into(),
                ));
            }
        }
        let source_variables = number(&common["final_round"], "num_variables")?;
        if source_variables > 16 || number(&common["source_code"], "message_len")? != 1 << source_variables {
            return Err(GuestError::Fixture("inconsistent hiding-WHIR source geometry".into()));
        }
        let metadata = &self.constants["table_metadata"];
        let values = number(metadata, "value_domain_size")?;
        if metadata["layout"] != "SharedUnion"
            || number(metadata, "row_memory_size")? != constraints
            || number(metadata, "col_memory_size")? != variables * 2
            || constraints > 2 * variables
            || !values.is_power_of_two()
            || values < 4 * variables
            || number(metadata, "matrix_nnz_padded")? != values
        {
            return Err(GuestError::Fixture(
                "unsupported SPARK table geometry or separate audit".into(),
            ));
        }
        let reads = self.constants["read_whir"]
            .as_array()
            .ok_or_else(|| GuestError::Fixture("missing read configurations".into()))?;
        if reads.len() != 2
            || reads[0] != self.constants["fixed_value_whir"]
            || number(&reads[0], "num_variables")? != values.ilog2() as usize + 3
            || number(&reads[1], "num_variables")? != values.ilog2() as usize + 1
        {
            return Err(GuestError::Fixture("unsupported SPARK read grouping".into()));
        }
        for (config, initial_variables) in std::iter::once((common, variables.ilog2() as usize))
            .chain(std::iter::once((
                &self.constants["fixed_value_whir"],
                values.ilog2() as usize + 3,
            )))
            .chain(
                reads
                    .iter()
                    .map(|config| (config, config["num_variables"].as_u64().unwrap_or(0) as usize)),
            )
        {
            if config.get("num_variables").is_some() && !(1..=4).contains(&number(config, "commitment_ood_samples")?) {
                return Err(GuestError::Fixture("unsupported initial WHIR OOD count".into()));
            }
            let rounds = config["rounds"]
                .as_array()
                .ok_or_else(|| GuestError::Fixture("missing WHIR rounds".into()))?;
            let factors = config["folding_schedule"]
                .as_array()
                .ok_or_else(|| GuestError::Fixture("missing folding factors".into()))?;
            if factors.len() != rounds.len() + 1 {
                return Err(GuestError::Fixture("folding count mismatch".into()));
            }
            let mut remaining = initial_variables;
            for (index, round) in rounds.iter().chain(std::iter::once(&config["final_round"])).enumerate() {
                let factor = number(round, "folding_factor")?;
                let domain = number(round, "domain_size")?;
                if factors[index] != factor
                    || factor == 0
                    || factor > remaining
                    || !domain.is_power_of_two()
                    || factor >= domain.ilog2() as usize
                    || domain.ilog2() as usize - factor > 24
                {
                    return Err(GuestError::Fixture("invalid WHIR folded domain".into()));
                }
                remaining -= factor;
                let bits = domain.ilog2() as usize - factor;
                if number(round, "num_variables")? != remaining
                    || number(round, "folded_domain_generator")?
                        != F::two_adic_generator(bits).as_canonical_u32() as usize
                    || (index == rounds.len() && number(round, "ood_samples")? != 0)
                    || (index < rounds.len() && !(1..=4).contains(&number(round, "ood_samples")?))
                {
                    return Err(GuestError::Fixture("inconsistent WHIR round geometry".into()));
                }
            }
        }
        let source = &common["source_code"];
        let final_round = &common["final_round"];
        if number(source, "domain_size")?
            != number(final_round, "domain_size")? >> number(final_round, "folding_factor")?
            || number(source, "randomness_len")? != number(common, "final_queries")?
            || number(source, "domain_generator")? != number(final_round, "folded_domain_generator")?
        {
            return Err(GuestError::Fixture(
                "source code disagrees with terminal WHIR domain".into(),
            ));
        }
        Ok(())
    }

    fn structured_rows_supported(&self) -> bool {
        let metadata = &self.constants["table_metadata"];
        metadata["row_memory_size"] == (1usize << 20)
            && metadata["col_memory_size"] == (1usize << 21)
            && metadata["value_domain_size"] == (1usize << 22)
            && self.constants["fixed_value_whir"]["folding_schedule"][0] == 8
    }

    fn packing(&self) -> Result<(bool, bool, bool), GuestError> {
        match self.constants["common"]["mask_packing"].as_str().unwrap_or("off") {
            "off" => Ok((false, false, false)),
            "application" => Ok((true, false, false)),
            "all" => Ok((true, true, false)),
            "application_free_basis" => Ok((true, false, true)),
            "all_free_basis" => Ok((true, true, true)),
            _ => Err(GuestError::Fixture("unsupported mask packing configuration".into())),
        }
    }

    fn validate_mask_geometry(&self) -> Result<(), GuestError> {
        let (application, sumchecks, free_basis) = self.packing()?;
        let common = &self.constants["common"];
        let groups = common["base_case_mask_groups"]
            .as_array()
            .ok_or_else(|| GuestError::Fixture("missing mask groups".into()))?;
        let outer = common["num_outer_rounds"].as_u64().unwrap() as usize;
        let inner = common["num_inner_rounds"].as_u64().unwrap() as usize;
        let folding: Vec<usize> = common["folding_schedule"]
            .as_array()
            .unwrap()
            .iter()
            .map(|value| value.as_u64().unwrap() as usize)
            .collect();
        let sumcheck_message = common["sumcheck_mask"]["message_len"].as_u64().unwrap() as usize;
        // The application mask protocol pads cubic inner masks to the outer degree-seven length.
        let application_message = 8;
        let mut logical_widths = vec![4 * outer, inner];
        let mut logical_messages = vec![application_message, sumcheck_message];
        for (batch, &factor) in folding.iter().enumerate() {
            logical_widths.push(factor);
            logical_messages.push(sumcheck_message);
            if batch + 1 < folding.len() {
                logical_widths.push(1);
                logical_messages.push(common["switch_masks"][batch]["message_len"].as_u64().unwrap() as usize);
            }
        }
        if groups.len() != logical_widths.len() {
            return Err(GuestError::Fixture("unsupported mask group count".into()));
        }
        for (index, group) in groups.iter().enumerate() {
            let packed = (index == 0 && application) || ((index == 1 || (index >= 2 && index % 2 == 0)) && sumchecks);
            let width = if packed { 1 } else { logical_widths[index] };
            let message_len = if index == 0 && free_basis {
                outer * (3 * 2 + application_message)
            } else if packed {
                logical_widths[index] * logical_messages[index]
            } else {
                logical_messages[index]
            };
            let randomness_len = common["mask_queries"].as_u64().unwrap() as usize;
            let domain =
                (message_len + randomness_len).next_power_of_two() << common["mask_log_inv_rate"].as_u64().unwrap();
            let generator = F::two_adic_generator(domain.ilog2() as usize).as_canonical_u32();
            if group["width"] != width
                || group["shape"]["message_len"] != message_len
                || group["shape"]["randomness_len"] != randomness_len
                || group["shape"]["domain_size"] != domain
                || group["shape"]["domain_generator"] != serde_json::json!([generator, 0, 0, 0, 0])
            {
                return Err(GuestError::Fixture(format!("unsupported mask geometry: group {index}")));
            }
        }
        if common["external_mask_groups"] != Value::Array(groups[..2].to_vec()) {
            return Err(GuestError::Fixture(
                "external mask geometry disagrees with base case".into(),
            ));
        }
        Ok(())
    }

    pub fn public_input(&self) -> Result<[F; PUBLIC_INPUT_LEN], GuestError> {
        public_input_from_statement(&self.statement.to_string())
    }

    pub fn offset(&self, name: &str) -> Result<usize, GuestError> {
        self.layout["entries"][name]["offset"]
            .as_u64()
            .map(|n| n as usize)
            .ok_or_else(|| GuestError::Fixture(format!("missing layout offset: {name}")))
    }

    pub fn retained_ranges(&self, options: &SparkGuestOptimizations) -> Result<Vec<Range<usize>>, GuestError> {
        let mut omitted = Vec::new();
        for (name, entry) in self.layout["entries"].as_object().unwrap() {
            let start = entry["offset"].as_u64().unwrap() as usize;
            let length = entry["words"].as_u64().unwrap() as usize;
            if options.row_counts && name.contains(".rows[") && name.ends_with(".count") {
                omitted.push(start..start + length);
            }
            if options.derived_fields
                && (name == "proof.spark.products.beta"
                    || name == "proof.spark.products.gamma"
                    || name.starts_with("proof.spark.matrix_evals[")
                    || name == "proof.spark.proof_ops.product_roots.values"
                    || name == "proof.spark.proof_mem.product_roots.values")
            {
                omitted.push(start..start + length);
            }
            if !name.contains(".rows[") || !name.ends_with(".values") {
                continue;
            }
            if options.fresh_rows && name.contains("fresh") {
                omitted.push(start..start + length);
            }
            if options.structured_rows
                && self.structured_rows_supported()
                && name.starts_with("proof.spark.")
                && name.contains(".rounds[0].openings.rows[")
            {
                if length != 256 {
                    return Err(GuestError::Fixture(format!("unsupported structured row width: {name}")));
                }
                if name.contains("fixed.value_proof") {
                    for block in 0..5 {
                        omitted.push(start + 25 + block * 32..start + 32 + block * 32);
                    }
                    omitted.extend([
                        start + 229..start + 240,
                        start + 245..start + 248,
                        start + 249..start + 256,
                    ]);
                } else {
                    omitted.push(start + 200..start + 256);
                }
            }
        }
        omitted.sort_by_key(|range| range.start);
        let mut ranges = Vec::new();
        let mut cursor = 0;
        for range in omitted {
            if range.start < cursor {
                return Err(GuestError::Fixture("overlapping omitted fields".into()));
            }
            if cursor < range.start {
                ranges.push(cursor..range.start);
            }
            cursor = range.end;
        }
        if cursor < self.canonical_words() {
            ranges.push(cursor..self.canonical_words());
        }
        Ok(ranges)
    }

    pub fn compact_words(&self, options: &SparkGuestOptimizations) -> Result<Vec<u32>, GuestError> {
        if !options.uses_compact_input() {
            return Ok(self.words.clone());
        }
        Ok(self
            .retained_ranges(options)?
            .into_iter()
            .flat_map(|range| self.words[range].iter().copied())
            .collect())
    }

    pub fn compact_offset(
        &self,
        offset: usize,
        options: &SparkGuestOptimizations,
    ) -> Result<Option<usize>, GuestError> {
        if !options.uses_compact_input() {
            return Ok((offset < self.words.len()).then_some(offset));
        }
        let mut cursor = 0;
        for range in self.retained_ranges(options)? {
            if range.contains(&offset) {
                return Ok(Some(cursor + offset - range.start));
            }
            cursor += range.len();
        }
        Ok(None)
    }

    pub fn execution_witness(
        &self,
        bytecode: &Bytecode,
        words: &[u32],
        options: &SparkGuestOptimizations,
    ) -> Result<ExecutionWitness, GuestError> {
        if !options.uses_compact_input() {
            return execution_witness_with_hint(
                bytecode,
                "full_zk_spark_words",
                words,
                FULL_ZK_SPARK_POSEIDON1_WORDS,
                FULL_ZK_SPARK_POSEIDON1_PREAMBLE_MEMORY_LEN,
            );
        }
        let ranges = self.retained_ranges(options)?;
        let expected = ranges.iter().map(Range::len).sum();
        if words.len() != expected {
            return Err(GuestError::InvalidWordCount {
                expected,
                actual: words.len(),
            });
        }
        let mut entries = ArenaVec::new();
        let mut cursor = 0;
        for range in ranges {
            let mut fields = ArenaVec::with_capacity(range.len());
            for (offset, &value) in words[cursor..cursor + range.len()].iter().enumerate() {
                let index = cursor + offset;
                fields.push(F::from_canonical_checked(value).ok_or(GuestError::NonCanonicalWord { index, value })?);
            }
            cursor += range.len();
            entries.push(fields);
        }
        let mut hints = Hints::default();
        hints.insert(bytecode, "full_zk_spark_words", entries);
        Ok(ExecutionWitness {
            preamble_memory_len: FULL_ZK_SPARK_POSEIDON1_PREAMBLE_MEMORY_LEN,
            hints,
            min_table_log_n_rows: BTreeMap::new(),
        })
    }

    pub fn compile(&self, options: &SparkGuestOptimizations) -> Result<CompileResult, GuestError> {
        compile_spark_fixture(self, options)
    }

    pub fn validate_words(
        &self,
        bytecode: &Bytecode,
        words: &[u32],
        options: &SparkGuestOptimizations,
    ) -> Result<(), GuestError> {
        let witness = self.execution_witness(bytecode, words, options)?;
        try_execute_bytecode(bytecode, &self.public_input()?, &witness, false)
            .map_err(|error| GuestError::Vm(error.to_string()))?;
        Ok(())
    }

    pub fn execute_report(
        &self,
        bytecode: &Bytecode,
        words: &[u32],
        options: &SparkGuestOptimizations,
        profiling: bool,
    ) -> Result<ExecutionReport, GuestError> {
        let witness = self.execution_witness(bytecode, words, options)?;
        let result = try_execute_bytecode(bytecode, &self.public_input()?, &witness, profiling)
            .map_err(|error| GuestError::Vm(error.to_string()))?;
        let trace = get_execution_trace(bytecode, result, &witness.min_table_log_n_rows);
        let tables = trace
            .traces
            .iter()
            .map(|(table, trace)| TableMetrics {
                name: table.name(),
                non_padded_rows: trace.non_padded_n_rows,
                log_n_rows: trace.log_n_rows,
                padded_rows: 1usize << trace.log_n_rows,
            })
            .collect();
        Ok(ExecutionReport {
            metadata: trace.metadata,
            padded_memory_cells: trace.memory.len(),
            tables,
        })
    }

    pub fn prove(
        &self,
        bytecode: &Bytecode,
        words: &[u32],
        options: &SparkGuestOptimizations,
    ) -> Result<RootProofResult, GuestError> {
        let witness = self.execution_witness(bytecode, words, options)?;
        let public_input = self.public_input()?;
        let start = Instant::now();
        let proof = prove_execution(
            bytecode,
            &public_input,
            &witness,
            &default_whir_config(FULL_ZK_SPARK_POSEIDON1_ROOT_LOG_INV_RATE),
            false,
        )
        .map_err(|error| GuestError::Proof(error.to_string()))?;
        let proving_elapsed = start.elapsed();
        let serialized_proof_bytes = postcard::to_allocvec(&proof.proof)
            .map_err(|error| GuestError::Proof(error.to_string()))?
            .len();
        let start = Instant::now();
        verify_execution(bytecode, &public_input, proof.proof.clone())
            .map_err(|error| GuestError::Proof(error.to_string()))?;
        Ok(RootProofResult {
            proof,
            proving_elapsed,
            verification_elapsed: start.elapsed(),
            serialized_proof_bytes,
        })
    }

    fn insert_protocol_replacements(&self, replacements: &mut BTreeMap<String, String>) -> Result<(), GuestError> {
        let common = &self.constants["common"];
        let shape = &common["canonical_shape"];
        let metadata = &self.constants["table_metadata"];
        let integer = |value: &Value, key: &str| value[key].as_u64().unwrap() as usize;
        let rows = integer(metadata, "row_memory_size");
        let columns = integer(metadata, "col_memory_size");
        let values = integer(metadata, "value_domain_size");
        let outer = integer(common, "num_outer_rounds");
        let inner = integer(common, "num_inner_rounds");
        let public = integer(shape, "public_inputs");
        let source = &common["source_code"];
        for (name, value) in [
            ("SPARK_ROW_MEMORY_SIZE_VALUE", rows),
            ("SPARK_COL_MEMORY_SIZE_VALUE", columns),
            ("SPARK_VALUE_DOMAIN_SIZE_VALUE", values),
            ("SPARK_MATRIX_NNZ_PADDED_VALUE", integer(metadata, "matrix_nnz_padded")),
            ("SPARK_OUTER_ROUNDS_VALUE", outer),
            ("SPARK_INNER_ROUNDS_VALUE", inner),
            ("SPARK_PUBLIC_INPUTS_VALUE", public),
            (
                "SPARK_PUBLIC_HALF_ACTIVE_BITS_VALUE",
                (public + 1).next_power_of_two().ilog2() as usize,
            ),
            ("SPARK_ROW_BITS_VALUE", rows.ilog2() as usize),
            ("SPARK_COL_BITS_VALUE", columns.ilog2() as usize),
            ("SPARK_VALUE_BITS_VALUE", values.ilog2() as usize),
            ("SPARK_FIXED_BITS_VALUE", values.ilog2() as usize + 3),
            ("SPARK_READ1_BITS_VALUE", values.ilog2() as usize + 1),
            (
                "SPARK_INNER_INV_POWER_VALUE",
                F::from_usize(1 << inner).inverse().as_canonical_u32() as usize,
            ),
            (
                "PLAIN_STRUCTURED_ROWS_VALUE",
                usize::from(self.structured_rows_supported()),
            ),
            (
                "OPT_FIXED_SIBLING_STORAGE_VALUE",
                usize::from(self.layout["fixed_sibling_storage"].as_bool().unwrap_or(false)),
            ),
            ("RELATION_MASK_QUERIES_VALUE", integer(common, "mask_queries")),
            ("RELATION_SOURCE_QUERIES_VALUE", integer(source, "randomness_len")),
            (
                "RELATION_SOURCE_DOMAIN_BITS_VALUE",
                integer(source, "domain_size").ilog2() as usize,
            ),
            ("RELATION_SOURCE_GENERATOR_VALUE", integer(source, "domain_generator")),
            ("RELATION_SOURCE_MESSAGE_LEN_VALUE", integer(source, "message_len")),
            (
                "RELATION_SOURCE_VARIABLES_VALUE",
                integer(&common["final_round"], "num_variables"),
            ),
            (
                "RELATION_SOURCE_FOLDING_VALUE",
                integer(&common["final_round"], "folding_factor"),
            ),
            (
                "RELATION_SOURCE_ENCODED_LEN_VALUE",
                integer(source, "message_len") + integer(source, "randomness_len"),
            ),
            ("RELATION_FINAL_POW_BITS_VALUE", integer(common, "final_pow_bits")),
        ] {
            replacements.insert(name.into(), value.to_string());
        }
        let rounds = common["rounds"].as_array().unwrap();
        let factors: Vec<usize> = common["folding_schedule"]
            .as_array()
            .unwrap()
            .iter()
            .map(|n| n.as_u64().unwrap() as usize)
            .collect();
        let mut prefixes = vec![0];
        for factor in &factors {
            prefixes.push(prefixes.last().unwrap() + factor);
        }
        let after_folding = prefixes[1..]
            .iter()
            .map(|prefix| inner - 1 - prefix)
            .collect::<Vec<_>>();
        let relation_positions = query_config::positions(common)?;
        let mut folding_pow = vec![integer(common, "starting_folding_pow_bits")];
        folding_pow.extend(rounds.iter().map(|round| integer(round, "folding_pow_bits")));
        for (name, value) in [
            ("RELATION_FOLDING_FACTORS_VALUE", factors.clone()),
            ("RELATION_FOLD_PREFIXES_VALUE", prefixes),
            ("RELATION_AFTER_FOLD_VARIABLES_VALUE", after_folding),
            (
                "RELATION_ROUND_BASE_ROWS_VALUE",
                (0..rounds.len()).map(|index| usize::from(index == 0)).collect(),
            ),
            (
                "RELATION_ROUND_OOD_COUNTS_VALUE",
                rounds.iter().map(|round| integer(round, "ood_samples")).collect(),
            ),
            ("RELATION_FOLDING_POW_BITS_VALUE", folding_pow),
            (
                "RELATION_FOLDING_INV_POWERS_VALUE",
                factors
                    .iter()
                    .map(|factor| F::from_usize(1 << factor).inverse().as_canonical_u32() as usize)
                    .collect(),
            ),
            (
                "RELATION_MAX_DRAWS_VALUE",
                relation_positions[..rounds.len()]
                    .iter()
                    .map(|count| count + 64)
                    .collect(),
            ),
            (
                "RELATION_DOMAIN_BITS_VALUE",
                rounds
                    .iter()
                    .map(|round| integer(round, "domain_size").ilog2() as usize - integer(round, "folding_factor"))
                    .collect(),
            ),
            ("RELATION_ROUND_FOLDING_VALUE", factors[..rounds.len()].to_vec()),
            (
                "RELATION_GENERATORS_VALUE",
                rounds
                    .iter()
                    .map(|round| integer(round, "folded_domain_generator"))
                    .collect(),
            ),
            (
                "RELATION_POW_BITS_VALUE",
                rounds.iter().map(|round| integer(round, "pow_bits")).collect(),
            ),
            (
                "RELATION_VARIABLES_VALUE",
                rounds.iter().map(|round| integer(round, "num_variables")).collect(),
            ),
        ] {
            replacements.insert(name.into(), serde_json::to_string(&value).unwrap());
        }
        for (token, path, count) in [
            ("RELATION_SUMCHECK_STARTS_VALUE", "sumchecks[{}].ell_zk", factors.len()),
            (
                "RELATION_SUMCHECK_COMMITMENTS_VALUE",
                "sumcheck_commitments[{}].roots",
                factors.len(),
            ),
            (
                "RELATION_ROUND_COMMITMENTS_VALUE",
                "rounds[{}].commitment.roots",
                rounds.len(),
            ),
            (
                "RELATION_ROUND_MASK_COMMITMENTS_VALUE",
                "rounds[{}].mask_commitment.roots",
                rounds.len(),
            ),
            (
                "RELATION_ROUND_OOD_ANSWERS_VALUE",
                "rounds[{}].ood_answers.values",
                rounds.len(),
            ),
            (
                "RELATION_ROUND_POW_WITNESSES_VALUE",
                "rounds[{}].pow_witness",
                rounds.len(),
            ),
            (
                "RELATION_ROUND_OPENING_STARTS_VALUE",
                "rounds[{}].openings.tag",
                rounds.len(),
            ),
        ] {
            let offsets = (0..count)
                .map(|index| self.offset(&format!("proof.pcs.{}", path.replace("{}", &index.to_string()))))
                .collect::<Result<Vec<_>, _>>()?;
            replacements.insert(token.into(), serde_json::to_string(&offsets).unwrap());
        }
        let configs = [&self.constants["fixed_value_whir"], &self.constants["read_whir"][1]];
        for (name, key) in [
            ("PLAIN_NUM_VARIABLES_VALUE", "num_variables"),
            ("PLAIN_INITIAL_OOD_COUNTS_VALUE", "commitment_ood_samples"),
            ("PLAIN_STARTING_POW_BITS_VALUE", "starting_folding_pow_bits"),
        ] {
            replacements.insert(
                name.into(),
                serde_json::to_string(&configs.map(|config| integer(config, key))).unwrap(),
            );
        }
        for (name, key) in [
            ("PLAIN_ROUND_NUM_VARIABLES_VALUE", "num_variables"),
            ("PLAIN_ROUND_OOD_COUNTS_VALUE", "ood_samples"),
            ("PLAIN_ROUND_GENERATORS_VALUE", "folded_domain_generator"),
            ("PLAIN_ROUND_FOLDING_POW_BITS_VALUE", "folding_pow_bits"),
            ("PLAIN_ROUND_POW_BITS_VALUE", "pow_bits"),
        ] {
            let arrays: Vec<Vec<usize>> = configs
                .iter()
                .map(|config| {
                    config["rounds"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|round| integer(round, key))
                        .collect()
                })
                .collect();
            replacements.insert(name.into(), serde_json::to_string(&arrays).unwrap());
        }
        let domains: Vec<Vec<usize>> = configs
            .iter()
            .map(|config| {
                config["rounds"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|round| integer(round, "domain_size").ilog2() as usize - integer(round, "folding_factor"))
                    .collect()
            })
            .collect();
        replacements.insert(
            "PLAIN_ROUND_DOMAIN_BITS_VALUE".into(),
            serde_json::to_string(&domains).unwrap(),
        );
        replacements.insert(
            "PLAIN_FOLDING_FACTORS_VALUE".into(),
            serde_json::to_string(&configs.map(|config| &config["folding_schedule"])).unwrap(),
        );
        let positions: Vec<Vec<usize>> = configs
            .iter()
            .map(|config| query_config::positions(config))
            .collect::<Result<_, _>>()?;
        replacements.insert(
            "PLAIN_QUERY_POSITIONS_VALUE".into(),
            serde_json::to_string(
                &positions
                    .iter()
                    .map(|positions| &positions[..positions.len() - 1])
                    .collect::<Vec<_>>(),
            )
            .unwrap(),
        );
        replacements.insert(
            "PLAIN_FINAL_QUERY_POSITIONS_VALUE".into(),
            serde_json::to_string(
                &positions
                    .iter()
                    .map(|positions| *positions.last().unwrap())
                    .collect::<Vec<_>>(),
            )
            .unwrap(),
        );
        for (name, key) in [
            ("PLAIN_FINAL_NUM_VARIABLES_VALUE", "num_variables"),
            ("PLAIN_FINAL_GENERATORS_VALUE", "folded_domain_generator"),
            ("PLAIN_FINAL_POW_BITS_VALUE", "pow_bits"),
        ] {
            replacements.insert(
                name.into(),
                serde_json::to_string(&configs.map(|config| integer(&config["final_round"], key))).unwrap(),
            );
        }
        replacements.insert(
            "PLAIN_FINAL_DOMAIN_BITS_VALUE".into(),
            serde_json::to_string(&configs.map(|config| {
                let round = &config["final_round"];
                integer(round, "domain_size").ilog2() as usize - integer(round, "folding_factor")
            }))
            .unwrap(),
        );
        replacements.insert(
            "PLAIN_FINAL_FOLDING_POW_BITS_VALUE".into(),
            serde_json::to_string(&configs.map(|config| integer(config, "final_folding_pow_bits"))).unwrap(),
        );
        Ok(())
    }

    pub(super) fn insert_layout_replacements(
        &self,
        replacements: &mut BTreeMap<String, String>,
    ) -> Result<(), GuestError> {
        self.validate()?;
        self.insert_protocol_replacements(replacements)?;
        let relation_queries = query_config::positions(&self.constants["common"])?;
        let plain_queries = query_config::positions(&self.constants["fixed_value_whir"])?;
        replacements.insert(
            "RELATION_QUERY_POSITIONS_PLACEHOLDER".into(),
            serde_json::to_string(&relation_queries[..relation_queries.len() - 1]).unwrap(),
        );
        let _ = plain_queries;
        let names: BTreeMap<String, String> = serde_json::from_str(include_str!("spark_offset_names.json")).unwrap();
        for (token, name) in names {
            replacements.insert(token, self.offset(&name)?.to_string());
        }
        replacements.insert("SPARK_CANONICAL_WORDS_VALUE".into(), self.canonical_words().to_string());
        let prefix = "proof.pcs.base_case";
        let separate_vectors = self.layout["entries"]
            .get(format!("{prefix}.carried_mask_openings_count"))
            .is_some();
        let same_height = match self.constants["common"]["fresh_mask_batching"]
            .as_str()
            .unwrap_or("separate")
        {
            "separate" => false,
            "same_height" => true,
            _ => {
                return Err(GuestError::Fixture(
                    "unsupported fresh mask batching configuration".into(),
                ));
            }
        };
        let groups = self.constants["common"]["base_case_mask_groups"].as_array().unwrap();
        let mut batches: Vec<Vec<usize>> = Vec::new();
        for (group, shape) in groups.iter().enumerate() {
            let existing = same_height
                .then(|| {
                    batches
                        .iter()
                        .position(|batch| groups[batch[0]]["shape"]["domain_size"] == shape["shape"]["domain_size"])
                })
                .flatten();
            if let Some(batch) = existing {
                batches[batch].push(group);
            } else {
                batches.push(vec![group]);
            }
        }
        let count = batches.len();
        if count < groups.len() && !separate_vectors {
            return Err(GuestError::Fixture(
                "grouped fresh masks require separate opening vectors".into(),
            ));
        }
        replacements.insert(
            "SPARK_GUEST_VERSION_VALUE".into(),
            (1 + usize::from(batches.len() < groups.len())).to_string(),
        );
        let widths: Vec<usize> = groups.iter().map(|g| g["width"].as_u64().unwrap() as usize).collect();
        let heights: Vec<usize> = groups
            .iter()
            .map(|g| g["shape"]["domain_size"].as_u64().unwrap().ilog2() as usize)
            .collect();
        let messages: Vec<usize> = groups
            .iter()
            .map(|g| g["shape"]["message_len"].as_u64().unwrap() as usize)
            .collect();
        let randomness: Vec<usize> = groups
            .iter()
            .map(|g| g["shape"]["randomness_len"].as_u64().unwrap() as usize)
            .collect();
        let generators: Vec<usize> = groups
            .iter()
            .map(|g| g["shape"]["domain_generator"][0].as_u64().unwrap() as usize)
            .collect();
        let mut mask_offsets = vec![0];
        let mut covector_offsets = vec![0];
        let source = &self.constants["common"]["source_code"];
        let mut reveal_offsets =
            vec![(source["message_len"].as_u64().unwrap() + source["randomness_len"].as_u64().unwrap()) as usize];
        for group in 0..groups.len() {
            mask_offsets.push(mask_offsets[group] + widths[group]);
            covector_offsets.push(covector_offsets[group] + widths[group] * messages[group]);
            reveal_offsets.push(reveal_offsets[group] + widths[group] * (messages[group] + randomness[group]));
        }
        let blinded_messages = mask_offsets[..groups.len()]
            .iter()
            .map(|mask| self.offset(&format!("{prefix}.blinded_masks[{mask}].message.values")))
            .collect::<Result<Vec<_>, _>>()?;
        let reveal_len = *reveal_offsets.last().unwrap();
        let reveal_leaf_count = reveal_len.div_ceil(2);
        replacements.insert(
            "SPARK_MASK_REVEAL_LEAF_COUNT_VALUE".into(),
            reveal_leaf_count.to_string(),
        );
        let mut reveal_layers = vec![if reveal_leaf_count > 1 {
            reveal_leaf_count.next_multiple_of(2)
        } else {
            1
        }];
        while *reveal_layers.last().unwrap() > 1 {
            let parents = reveal_layers.last().unwrap().div_ceil(2);
            reveal_layers.push(if parents > 1 { parents.next_multiple_of(2) } else { 1 });
        }
        for (name, value) in [
            ("GROUP_WIDTHS", widths.clone()),
            ("GROUP_HEIGHTS", heights.clone()),
            ("GROUP_GENERATORS", generators),
            ("GROUP_MESSAGE_LENGTHS", messages),
            ("GROUP_RANDOMNESS_LENGTHS", randomness),
            ("GROUP_OFFSETS", mask_offsets),
            ("GROUP_COVECTOR_OFFSETS", covector_offsets),
            ("GROUP_REVEAL_OFFSETS", reveal_offsets),
            ("BLINDED_MESSAGES", blinded_messages),
            ("REVEAL_LAYER_COUNTS", reveal_layers),
        ] {
            replacements.insert(
                format!("SPARK_MASK_{name}_VALUE"),
                serde_json::to_string(&value).unwrap(),
            );
        }
        replacements.insert(
            "SPARK_MASK_APPLICATION_FREE_BASIS_VALUE".into(),
            usize::from(self.packing()?.2).to_string(),
        );
        replacements.insert(
            "SPARK_MASK_OUTER_ROUNDS_VALUE".into(),
            self.constants["common"]["num_outer_rounds"].to_string(),
        );
        replacements.insert(
            "SPARK_MASK_INNER_ROUNDS_VALUE".into(),
            self.constants["common"]["num_inner_rounds"].to_string(),
        );
        let mut carried_root_names = vec![
            "proof.application_mask_commitment.roots".to_owned(),
            "proof.inner_sumcheck_mask_commitment.roots".to_owned(),
        ];
        let sumcheck_count = self.constants["common"]["folding_schedule"].as_array().unwrap().len();
        for batch in 0..sumcheck_count {
            carried_root_names.push(format!("proof.pcs.sumcheck_commitments[{batch}].roots"));
            if batch + 1 < sumcheck_count {
                carried_root_names.push(format!("proof.pcs.rounds[{batch}].mask_commitment.roots"));
            }
        }
        let mut starts = vec![0];
        let mut members = vec![];
        let mut batch_widths = vec![];
        let mut batch_heights = vec![];
        let mut columns = vec![];
        for batch in &batches {
            let mut width = 0;
            for &group in batch {
                members.push(group);
                columns.push(width);
                width += widths[group];
            }
            starts.push(members.len());
            batch_widths.push(width);
            batch_heights.push(heights[batch[0]]);
        }
        let carried_name = |group: usize| {
            if separate_vectors {
                format!("{prefix}.carried_mask_openings[{group}]")
            } else {
                format!("{prefix}.mask_openings[{group}].carried")
            }
        };
        let fresh_name = |batch: usize| {
            if separate_vectors {
                format!("{prefix}.fresh_mask_openings[{batch}]")
            } else {
                format!("{prefix}.mask_openings[{batch}].fresh")
            }
        };
        let fresh_roots = (0..count)
            .map(|i| self.offset(&format!("{prefix}.fresh_mask_commitments[{i}].roots")))
            .collect::<Result<Vec<_>, _>>()?;
        let fresh_rows = (0..count)
            .map(|i| self.offset(&format!("{}.rows[0].values", fresh_name(i))))
            .collect::<Result<Vec<_>, _>>()?;
        let fresh_siblings = (0..count)
            .map(|i| self.offset(&format!("{}.siblings_count", fresh_name(i))))
            .collect::<Result<Vec<_>, _>>()?;
        let carried_rows = (0..groups.len())
            .map(|i| self.offset(&format!("{}.rows[0].values", carried_name(i))))
            .collect::<Result<Vec<_>, _>>()?;
        let carried_siblings = (0..groups.len())
            .map(|i| self.offset(&format!("{}.siblings_count", carried_name(i))))
            .collect::<Result<Vec<_>, _>>()?;
        let carried_roots = carried_root_names
            .iter()
            .map(|name| self.offset(name))
            .collect::<Result<Vec<_>, _>>()?;
        for (name, value) in [
            ("STARTS", starts),
            ("MEMBERS", members),
            ("WIDTHS", batch_widths),
            ("HEIGHTS", batch_heights),
            ("COLUMN_OFFSETS", columns),
        ] {
            replacements.insert(
                format!("SPARK_MASK_BATCH_{name}_VALUE"),
                serde_json::to_string(&value).unwrap(),
            );
        }
        for (name, value) in [
            ("FRESH_ROOTS", fresh_roots),
            ("FRESH_ROWS", fresh_rows),
            ("FRESH_SIBLINGS", fresh_siblings),
            ("CARRIED_ROOTS", carried_roots),
            ("CARRIED_ROWS", carried_rows),
            ("CARRIED_SIBLINGS", carried_siblings),
        ] {
            replacements.insert(
                format!("SPARK_MASK_{name}_VALUE"),
                serde_json::to_string(&value).unwrap(),
            );
        }
        replacements.insert(
            "SPARK_MASK_SEPARATE_OPENING_VECTORS_VALUE".into(),
            usize::from(separate_vectors).to_string(),
        );
        replacements.insert(
            "SPARK_MASK_CARRIED_COUNT_VALUE".into(),
            self.offset(&format!(
                "{prefix}.{}",
                if separate_vectors {
                    "carried_mask_openings_count"
                } else {
                    "mask_openings_count"
                }
            ))?
            .to_string(),
        );
        replacements.insert(
            "SPARK_MASK_FRESH_COUNT_VALUE".into(),
            if separate_vectors {
                self.offset(&format!("{prefix}.fresh_mask_openings_count"))?
            } else {
                0
            }
            .to_string(),
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn malformed_fixture_geometry_and_offsets_are_rejected() {
        let mut fixture = SparkGuestFixture::embedded().unwrap().clone();
        fixture.constants["common"]["base_case_mask_groups"][0]["width"] = Value::from(81);
        assert!(fixture.validate().is_err());
        let mut fixture = SparkGuestFixture::embedded().unwrap().clone();
        fixture.layout["entries"]["proof.pcs.base_case.masked_claim"]["offset"] =
            Value::from(fixture.canonical_words());
        assert!(fixture.validate().is_err());
    }

    #[test]
    fn exported_query_caps_are_checked_for_all_configurations() {
        let fixture = SparkGuestFixture::embedded().unwrap().clone();
        assert_eq!(fixture.constants["fixed_audit_whir"]["final_round"]["num_queries"], 266);
        assert_eq!(
            fixture.constants["fixed_audit_whir"]["final_round"]["query_positions"],
            128
        );
        for name in ["fixed_value_whir", "fixed_audit_whir"] {
            let mut changed = fixture.clone();
            changed.constants[name]["final_round"]["query_positions"] = Value::from(1);
            assert!(changed.validate().is_err());
        }
        let mut changed = fixture;
        changed.constants["read_whir"][0]["rounds"][0]["query_positions"] = Value::from(1);
        assert!(changed.validate().is_err());
    }

    #[test]
    fn configured_batches_determine_membership_and_column_order() {
        let mut fixture = SparkGuestFixture::embedded().unwrap().clone();
        fixture.constants["common"]["fresh_mask_batching"] = Value::from("same_height");
        let prefix = "proof.pcs.base_case";
        let entries = fixture.layout["entries"].as_object_mut().unwrap();
        let old_entries = entries.clone();
        for (name, value) in &old_entries {
            for group in 0..7 {
                if let Some(suffix) = name.strip_prefix(&format!("{prefix}.mask_openings[{group}].carried")) {
                    entries.insert(
                        format!("{prefix}.carried_mask_openings[{group}]{suffix}"),
                        value.clone(),
                    );
                }
            }
            for (batch, group) in [0, 3, 5].into_iter().enumerate() {
                if let Some(suffix) = name.strip_prefix(&format!("{prefix}.mask_openings[{group}].fresh")) {
                    entries.insert(format!("{prefix}.fresh_mask_openings[{batch}]{suffix}"), value.clone());
                }
            }
        }
        let count = old_entries
            .get(&format!("{prefix}.mask_openings_count"))
            .or_else(|| old_entries.get(&format!("{prefix}.carried_mask_openings_count")))
            .unwrap()
            .clone();
        entries.insert(format!("{prefix}.carried_mask_openings_count"), count.clone());
        entries.insert(format!("{prefix}.fresh_mask_openings_count"), count);
        let mut replacements = BTreeMap::new();
        fixture.insert_layout_replacements(&mut replacements).unwrap();
        assert_eq!(replacements["SPARK_MASK_BATCH_STARTS_VALUE"], "[0,2,4,7]");
        assert_eq!(replacements["SPARK_MASK_BATCH_MEMBERS_VALUE"], "[0,3,1,5,2,4,6]");
        assert_eq!(replacements["SPARK_MASK_BATCH_WIDTHS_VALUE"], "[2,2,3]");
        assert_eq!(replacements["SPARK_MASK_BATCH_HEIGHTS_VALUE"], "[12,11,10]");
        assert_eq!(replacements["SPARK_MASK_BATCH_COLUMN_OFFSETS_VALUE"], "[0,1,0,1,0,1,2]");
        // A prover-supplied count cannot choose the verifier's group mapping.
        let count_offset = fixture
            .offset(&format!("{prefix}.fresh_mask_commitments_count"))
            .unwrap();
        fixture.words[count_offset] = 7;
        let mut changed = BTreeMap::new();
        fixture.insert_layout_replacements(&mut changed).unwrap();
        assert_eq!(changed, replacements);
    }
}
