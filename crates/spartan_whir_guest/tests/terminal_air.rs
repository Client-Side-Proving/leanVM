use backend::{Air, BasedVectorSpace, ConstraintFolder, KoalaBear, PrimeCharacteristicRing, QuinticExtensionFieldKB};
use lean_vm::{ExecutionTable, ExtensionOpPrecompile, ExtraDataForBuses, Poseidon16Precompile};
use serde::Deserialize;

type EF = QuinticExtensionFieldKB;

#[derive(Deserialize)]
struct Document {
    vectors: Vec<Vector>,
}

#[derive(Deserialize)]
struct Vector {
    id: String,
    table: String,
    flat: Vec<[u32; 5]>,
    shift: Vec<[u32; 5]>,
    alphas: Vec<[u32; 5]>,
    beta_eq: Vec<[u32; 5]>,
    expected: [u32; 5],
}

fn ef(value: [u32; 5]) -> EF {
    EF::from_basis_coefficients_fn(|i| KoalaBear::from_u32(value[i]))
}

#[test]
#[ignore = "requires LEANVM_AIR_VECTORS pointing to the terminal Solidity AIR differential vectors"]
fn terminal_air_vectors_match_native_constraints() {
    let path = std::env::var("LEANVM_AIR_VECTORS").expect("set LEANVM_AIR_VECTORS");
    let document: Document = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    assert!(!document.vectors.is_empty());
    for vector in document.vectors {
        let flat: Vec<_> = vector.flat.into_iter().map(ef).collect();
        let shift: Vec<_> = vector.shift.into_iter().map(ef).collect();
        let alphas: Vec<_> = vector.alphas.into_iter().map(ef).collect();
        let beta: Vec<_> = vector.beta_eq.into_iter().map(ef).collect();
        let extra = ExtraDataForBuses::new(&beta, alphas);
        let mut evaluator = ConstraintFolder::new(&flat, &shift, &extra);
        match vector.table.as_str() {
            "execution" => ExecutionTable::<true>.eval(&mut evaluator, &extra),
            "extension" => ExtensionOpPrecompile::<true>.eval(&mut evaluator, &extra),
            "poseidon" => Poseidon16Precompile::<true>.eval(&mut evaluator, &extra),
            table => panic!("unknown table {table}"),
        }
        assert_eq!(
            evaluator.constraint_index,
            extra.alpha_powers.len(),
            "{}:{}",
            vector.table,
            vector.id
        );
        assert_eq!(
            evaluator.accumulator,
            ef(vector.expected),
            "{}:{}",
            vector.table,
            vector.id
        );
    }
}
