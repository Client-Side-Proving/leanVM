from recursion import *

LEAF_INFO_DOMAIN = 1279677489  # "LFT1"
BYTECODE_CLAIM_OFFSET = DIGEST_LEN
BYTECODE_CLAIM_NUM_CHUNKS = BYTECODE_CLAIM_SIZE_PADDED / DIGEST_LEN
INITIAL_FIAT_SHAMIR_CAP_OFFSET = BYTECODE_CLAIM_OFFSET + BYTECODE_CLAIM_SIZE_PADDED
APPLICATION_DIGEST_OFFSET = INITIAL_FIAT_SHAMIR_CAP_OFFSET + DIGEST_LEN
LEAF_INFO_SIZE = APPLICATION_DIGEST_OFFSET + DIGEST_LEN
LEAF_INFO_NUM_CHUNKS = LEAF_INFO_SIZE / DIGEST_LEN
BYTECODE_SUMCHECK_PROOF_SIZE = BYTECODE_SUMCHECK_PROOF_SIZE_PLACEHOLDER
EXPECTED_CHILD_CAP = EXPECTED_CHILD_CAP_PLACEHOLDER


def main():
    pub_mem = 0
    build_preamble_memory()

    leaf_info = Array(LEAF_INFO_SIZE)
    hint_witness("leaf_info", leaf_info)
    leaf_info[0] = LEAF_INFO_DOMAIN
    leaf_info[1] = 1
    set_to_6_zeros(leaf_info + 2)

    for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
        leaf_info[BYTECODE_CLAIM_OFFSET + k] = 0

    child_cap = leaf_info + INITIAL_FIAT_SHAMIR_CAP_OFFSET
    for k in unroll(0, DIGEST_LEN):
        child_cap[k] = EXPECTED_CHILD_CAP[k]

    application_digest = leaf_info + APPLICATION_DIGEST_OFFSET
    child_bytecode_claim = recursion(application_digest, child_cap)
    claims = Array(1)
    claims[0] = child_bytecode_claim
    reduce_bytecode_claims(claims, 1, leaf_info + BYTECODE_CLAIM_OFFSET, child_cap)

    slice_hash(leaf_info, LEAF_INFO_NUM_CHUNKS, pub_mem)
    return


def reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output, initial_fiat_shamir_cap):
    debug_assert(n_bytecode_claims != 0)
    bytecode_sumcheck_proof = Array(BYTECODE_SUMCHECK_PROOF_SIZE)
    hint_witness("bytecode_sumcheck_proof", bytecode_sumcheck_proof)
    reduction_capacity = Array(DIGEST_LEN)
    reduction_capacity[0] = initial_fiat_shamir_cap[0] + 1
    for i in unroll(1, DIGEST_LEN):
        reduction_capacity[i] = initial_fiat_shamir_cap[i]

    count_block = Array(DIGEST_LEN)
    count_block[0] = n_bytecode_claims
    for k in unroll(1, DIGEST_LEN):
        count_block[k] = 0
    rc_buf = Array(n_bytecode_claims)
    rc_buf[0] = slice_hash_continue(reduction_capacity, count_block, 1)

    for i in range(0, n_bytecode_claims - 1):
        running_capacity: Mut = rc_buf[i]
        claim_ptr = bytecode_claims[i]
        for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
            assert claim_ptr[k] == 0
        running_capacity = slice_hash_continue(running_capacity, claim_ptr, BYTECODE_CLAIM_NUM_CHUNKS)
        rc_buf[i + 1] = running_capacity

    running_capacity: Mut = rc_buf[n_bytecode_claims - 1]
    last_claim = bytecode_claims[n_bytecode_claims - 1]
    for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
        assert last_claim[k] == 0
    running_capacity = slice_hash_continue(running_capacity, last_claim, BYTECODE_CLAIM_NUM_CHUNKS - 1)
    reduction_fs: Mut = fs_new(bytecode_sumcheck_proof, running_capacity)
    reduction_fs = fs_observe_chunks(reduction_fs, last_claim + (BYTECODE_CLAIM_NUM_CHUNKS - 1) * DIGEST_LEN, 1)
    reduction_fs, alpha = fs_sample_ef(reduction_fs)
    alpha_powers = powers(alpha, n_bytecode_claims)

    all_values = Array(n_bytecode_claims * DIM)
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        copy_ef(claim_ptr + BYTECODE_POINT_N_VARS * DIM, all_values + i * DIM)

    claimed_sum = Array(DIM)
    dot_product_ee_dynamic(all_values, alpha_powers, claimed_sum, n_bytecode_claims)
    reduction_fs, challenges, final_eval = sumcheck_verify(
        reduction_fs, BYTECODE_POINT_N_VARS, claimed_sum, 2
    )

    eq_evals = Array(n_bytecode_claims * DIM)
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        poly_eq_ee(claim_ptr, challenges, eq_evals + i * DIM, BYTECODE_POINT_N_VARS)
    w_r = Array(DIM)
    dot_product_ee_dynamic(eq_evals, alpha_powers, w_r, n_bytecode_claims)
    bytecode_value_at_r = div_extension_ret(final_eval, w_r)

    copy_many_ef(challenges, bytecode_claim_output, BYTECODE_POINT_N_VARS)
    copy_ef(bytecode_value_at_r, bytecode_claim_output + BYTECODE_POINT_N_VARS * DIM)
    return
