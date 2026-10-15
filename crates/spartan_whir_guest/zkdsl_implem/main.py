from snark_lib import *
from transcript import *
from verifier import *


PUBLIC_INPUT_LEN = 8
ZERO_PTR = PUBLIC_INPUT_LEN
ZERO_LEN = 16
ONE_EF_PTR = ZERO_PTR + ZERO_LEN
CONTROL_WORDS = CONTROL_WORDS_PLACEHOLDER
STATEMENT_PREFIX = STATEMENT_PREFIX_PLACEHOLDER


def build_preamble():
    zero_ptr = ZERO_PTR
    for i in unroll(0, ZERO_LEN):
        zero_ptr[i] = 0
    one_ef_ptr = ONE_EF_PTR
    one_ef_ptr[0] = 1
    for i in unroll(1, 5):
        one_ef_ptr[i] = 0
    return


def main():
    build_preamble()
    public_input = 0
    proof = Array(CONTROL_WORDS)
    hint_witness("proof_words", proof)

    assert proof[0] == 76
    assert proof[1] == 86
    assert proof[2] == 83
    assert proof[3] == 87
    assert proof[4] == 1
    assert proof[5] == 1
    assert proof[6] == 1
    assert proof[7] == 1
    assert proof[9] == 1
    assert proof[18] == 2
    assert proof[19] == 1
    assert proof[50] == 3
    assert proof[86] == 3
    assert proof[87] == 1
    assert proof[93] == 1
    assert proof[104] == 0
    assert proof[105] == 0
    assert proof[106] == 1
    assert proof[107] == 2
    assert proof[118] == 0
    assert proof[119] == 0
    assert proof[120] == 14
    for i in unroll(0, 14):
        assert proof[121 + i * 3] == 2
    assert proof[163] == WHIR_SIBLING_COUNT
    assert proof[WHIR_FINAL_SUMCHECK_OFFSET] == 1
    assert proof[WHIR_FINAL_SUMCHECK_OFFSET + 1] == 1
    assert proof[WHIR_FINAL_SUMCHECK_OFFSET + 12] == 0
    assert proof[WHIR_FINAL_SUMCHECK_OFFSET + 13] == 4

    statement_fs: Mut = fs_new()
    for i in unroll(0, len(STATEMENT_PREFIX)):
        statement_fs = fs_observe_one(statement_fs, STATEMENT_PREFIX[i])
    statement_fs = fs_observe_one(statement_fs, proof[8])
    digest = fs_finalize(statement_fs)
    for i in unroll(0, PUBLIC_INPUT_LEN):
        assert digest[i] == public_input[i]
    verify_control_proof(proof)
    return
