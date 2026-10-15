//! Bus expressions evaluated from committed columns, including at non-Boolean points.
use crate::*;
use backend::*;

/// Reconstruct temporary bus columns as polynomial expressions of the committed
/// columns. Their multilinear interpolants are different polynomials and must
/// not be substituted for these expressions at a sumcheck point.
pub fn reconstruct_bus_columns<R: PrimeCharacteristicRing + Copy>(table: Table, flat: &[R]) -> Vec<R> {
    assert_eq!(flat.len(), table.n_columns());
    let mut columns = flat.to_vec();
    match table {
        Table::Execution(_) => {
            let nu = |operand, flag, fp_flag, value| {
                flat[flag] * flat[operand]
                    + (R::ONE - flat[flag] - flat[fp_flag]) * flat[value]
                    + flat[fp_flag] * (flat[EXEC_COL_FP] + flat[operand])
            };
            let aux = flat[EXEC_COL_AUX_1];
            let add = aux.double() - aux.square();
            let deref = (aux * (aux - R::ONE)).halve();
            columns.extend([
                R::ONE - add - flat[EXEC_COL_FLAG_MUL] - deref - flat[EXEC_COL_FLAG_JUMP],
                nu(
                    EXEC_COL_OPERAND_A,
                    EXEC_COL_FLAG_A,
                    EXEC_COL_FLAG_AB_FP,
                    EXEC_COL_VALUE_A,
                ),
                nu(
                    EXEC_COL_OPERAND_B,
                    EXEC_COL_FLAG_B,
                    EXEC_COL_FLAG_AB_FP,
                    EXEC_COL_VALUE_B,
                ),
                nu(
                    EXEC_COL_OPERAND_C,
                    EXEC_COL_FLAG_C,
                    EXEC_COL_FLAG_C_FP,
                    EXEC_COL_VALUE_C,
                ),
            ]);
        }
        Table::ExtensionOp(_) => {
            // Column positions follow the extension operation AIR.
            columns.extend([
                flat[1] * (flat[3] + flat[4] + flat[5]),
                flat[0] * R::from_usize(EXT_OP_FLAG_BE)
                    + flat[3] * R::from_usize(EXT_OP_FLAG_ADD)
                    + flat[4] * R::from_usize(EXT_OP_FLAG_DOT_PRODUCT)
                    + flat[5] * R::from_usize(EXT_OP_FLAG_EQ)
                    + flat[2] * R::from_usize(EXT_OP_LEN_MULTIPLIER),
            ]);
        }
        Table::Poseidon16(_) => {
            columns.extend([
                flat[POSEIDON_COL_ADDR_LEFT_HI]
                    - (R::ONE - flat[POSEIDON_COL_FLAG_LEFT]) * R::from_usize(HALF_DIGEST_LEN),
                R::from_usize(POSEIDON_DOMAINSEP_BASE)
                    + flat[POSEIDON_COL_FLAG_PERMUTE] * R::from_usize(POSEIDON_FLAG_PERMUTE_SHIFT)
                    + flat[POSEIDON_COL_FLAG_OUT8] * R::from_usize(POSEIDON_FLAG_OUT8_SHIFT)
                    + flat[POSEIDON_COL_FLAG_LEFT] * R::from_usize(POSEIDON_FLAG_LEFT_SHIFT)
                    + flat[POSEIDON_COL_FLAG_LEFT]
                        * flat[POSEIDON_COL_OFFSET_LEFT]
                        * R::from_usize(POSEIDON_OFFSET_LEFT_SHIFT),
            ]);
        }
    }
    assert_eq!(columns.len(), table.n_columns_total());
    columns
}

pub fn resolve_bus_data<R: PrimeCharacteristicRing + Copy>(entry: BusData, columns: &[R]) -> R {
    match entry {
        BusData::Column(index) => columns[index],
        BusData::ColumnPlusConstant(index, offset) => columns[index] + R::from_usize(offset),
        BusData::Constant(value) => R::from_usize(value),
    }
}
