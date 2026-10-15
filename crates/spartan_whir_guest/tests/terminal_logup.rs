use std::collections::BTreeMap;

use backend::*;
use lean_vm::{ALL_TABLES, BusData, BusMultiplicity, EF, F, LOGUP_MEMORY_DOMAINSEP, Table, TableT, TableTrace};
use serde_json::json;
use sub_protocols::{prove_generic_logup, verify_generic_logup, verify_gkr_quotient};

fn coordinates(value: EF) -> Vec<u32> {
    let coefficients: &[F] = value.as_basis_coefficients_slice();
    coefficients.iter().map(PrimeField32::as_canonical_u32).collect()
}

fn extensions(values: &[EF]) -> Vec<Vec<u32>> {
    values.iter().copied().map(coordinates).collect()
}

fn transcript_hex(raw: &RawProof<F>) -> String {
    let mut result = String::from("0x");
    for field in &raw.transcript {
        for byte in field.as_canonical_u32().to_le_bytes() {
            use std::fmt::Write;
            write!(result, "{byte:02x}").unwrap();
        }
    }
    result
}

#[test]
#[ignore = "exports small native LogUp proofs to LEANVM_LOGUP_EXPORT_DIR for terminal differential tests"]
fn export_terminal_logup_vectors() {
    let destination = std::path::PathBuf::from(std::env::var("LEANVM_LOGUP_EXPORT_DIR").expect("set export directory"));
    std::fs::create_dir_all(&destination).unwrap();
    let mut cases = Vec::new();
    for (case, (memory_log, bytecode_log, heights)) in [
        (9usize, 8usize, [8usize, 8usize, 8usize]),
        (10, 8, [8, 9, 8]),
        (10, 8, [10, 8, 9]),
        (10, 9, [8, 8, 8]),
    ]
    .into_iter()
    .enumerate()
    {
        let capacity = std::array::from_fn(|i| F::from_usize(17 + case * 11 + i));
        let memory: Vec<F> = (0..1 << memory_log).map(|i| F::from_usize(i * 19 + 7 + case)).collect();
        let mut memory_acc = vec![F::ZERO; memory.len()];
        let mut bytecode = vec![F::ZERO; 16 << bytecode_log];
        for (i, value) in bytecode[..12].iter_mut().enumerate() {
            *value = F::from_usize(101 + 17 * i + case);
        }
        let mut bytecode_acc = vec![F::ZERO; 1 << bytecode_log];
        bytecode_acc[0] = F::from_usize(1 << heights[0]);
        let mut traces = BTreeMap::new();
        for (table_index, table) in ALL_TABLES.into_iter().enumerate() {
            let rows = 1 << heights[table_index];
            let mut columns: Vec<ArenaVec<F>> = (0..table.n_columns_total())
                .map(|_| ArenaVec::from_slice(&vec![F::ZERO; rows]))
                .collect();
            if table_index == 0 {
                for i in 0..12 {
                    columns[8 + i].fill(bytecode[i]);
                }
            }
            let buses = table.bus_interactions();
            // Nonzero precompile multiplicities balance execution against extension.
            // These are standalone LogUp traces; AIR validity is checked separately.
            if table_index < 2 {
                let BusMultiplicity::Column(column) = buses[0].multiplicity else {
                    unreachable!()
                };
                columns[column].fill(F::from_usize(1 << heights[1 - table_index]));
                let BusData::Column(domain) = buses[0].domainsep else {
                    unreachable!()
                };
                columns[domain].fill(bytecode[11]);
            }
            for bus in buses {
                if !matches!(bus.domainsep, BusData::Constant(LOGUP_MEMORY_DOMAINSEP)) {
                    continue;
                }
                let BusData::ColumnPlusConstant(address_column, offset) = bus.data[0] else {
                    unreachable!()
                };
                let BusData::Column(value_column) = bus.data[1] else {
                    unreachable!()
                };
                assert_eq!(columns[address_column][0], F::ZERO);
                columns[value_column].fill(memory[offset]);
                memory_acc[offset] += F::from_usize(rows);
            }
            traces.insert(
                table,
                TableTrace {
                    columns,
                    non_padded_n_rows: rows,
                    log_n_rows: heights[table_index],
                },
            );
        }
        let table_heights: BTreeMap<Table, usize> = ALL_TABLES.into_iter().zip(heights).collect();
        let permutation = default_koalabear_poseidon1_16();
        let mut prover =
            ProverState::<EF, _>::new_with_hash_profile(permutation.clone(), capacity, ProofHashProfile::Keccak240);
        let gamma = prover.sample();
        prover.duplex();
        let beta = prover.sample_vec(4);
        let beta_eq = eval_eq_sequential(&beta);
        let proved = prove_generic_logup(
            &mut prover,
            gamma,
            &beta,
            &beta_eq,
            &memory,
            &memory_acc,
            &bytecode,
            &bytecode_acc,
            &traces,
        );
        let proof = prover.into_proof();

        let mut verifier = VerifierState::<EF, _>::new_with_hash_profile(
            proof.clone(),
            permutation.clone(),
            capacity,
            ProofHashProfile::Keccak240,
        )
        .unwrap();
        assert_eq!(gamma, verifier.sample());
        verifier.duplex();
        assert_eq!(beta, verifier.sample_vec(4));
        let verified = verify_generic_logup(
            &mut verifier,
            gamma,
            &beta,
            &beta_eq,
            memory_log,
            &bytecode,
            &table_heights,
        )
        .unwrap();
        assert_eq!(proved.gkr_point, verified.gkr_point);
        assert_eq!(proved.columns_values, verified.columns_values);
        assert_eq!(proved.bytecode_evaluation, verified.bytecode_evaluation);
        let post_logup_sample = verifier.sample();
        let raw = verifier.into_raw_proof();

        let mut verifier =
            VerifierState::<EF, _>::new_with_hash_profile(proof, permutation, capacity, ProofHashProfile::Keccak240)
                .unwrap();
        assert_eq!(gamma, verifier.sample());
        verifier.duplex();
        assert_eq!(beta, verifier.sample_vec(4));
        let (quotient, point, numerator, denominator) =
            verify_gkr_quotient(&mut verifier, verified.total_gkr_n_vars).unwrap();
        assert_eq!(quotient, EF::ZERO);
        assert_eq!(point.0, verified.gkr_point);
        let post_gkr_sample = verifier.sample();
        let gkr_raw = verifier.into_raw_proof();
        let bytecode_evaluation = verified.bytecode_evaluation.as_ref().unwrap();
        let column_indices: Vec<Vec<usize>> = ALL_TABLES
            .iter()
            .map(|t| verified.columns_values[t].keys().copied().collect())
            .collect();
        let column_values: Vec<Vec<Vec<u32>>> = ALL_TABLES
            .iter()
            .map(|t| verified.columns_values[t].values().copied().map(coordinates).collect())
            .collect();
        cases.push(json!({
            "id": format!("native-{case}"), "memory_log":memory_log, "bytecode_log":bytecode_log, "heights":heights,
            "capacity": capacity.map(|f|f.as_canonical_u32()), "gamma":coordinates(gamma), "beta":extensions(&beta),
            "bytecode":bytecode.iter().map(PrimeField32::as_canonical_u32).collect::<Vec<_>>(),
            "transcript":transcript_hex(&raw), "gkr_transcript":transcript_hex(&gkr_raw),
            "gkr_n_vars":verified.total_gkr_n_vars, "gkr_point":extensions(&point.0),
            "gkr_quotient":coordinates(quotient), "gkr_numerator":coordinates(numerator), "gkr_denominator":coordinates(denominator),
            "post_gkr_sample":coordinates(post_gkr_sample), "post_logup_sample":coordinates(post_logup_sample),
            "memory_acc":coordinates(verified.value_memory_acc), "memory_value":coordinates(verified.value_memory),
            "value_bytecode_acc":coordinates(verified.value_bytecode_acc), "fixed_bytecode_value":coordinates(bytecode_evaluation.value),
            "fixed_bytecode_point":extensions(&bytecode_evaluation.point.0),
            "numerators":ALL_TABLES.map(|t|coordinates(verified.bus_numerators_values[&t])),
            "denominators":ALL_TABLES.map(|t|coordinates(verified.bus_denominators_values[&t])),
            "column_indices":column_indices, "columns":column_values,
        }));
    }
    let document = json!({"format":"leanvm-logup-keccak240-v1", "vectors":cases});
    std::fs::write(
        destination.join("vectors.json"),
        serde_json::to_string_pretty(&document).unwrap() + "\n",
    )
    .unwrap();
}
