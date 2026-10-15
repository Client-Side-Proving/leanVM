from recursion import *

LEAF_INFO_DOMAIN = 1279677489  # "LFT1"
NODE_INFO_DOMAIN = 1313817649  # "NOD1"
BYTECODE_CLAIM_OFFSET = DIGEST_LEN
BYTECODE_CLAIM_NUM_CHUNKS = BYTECODE_CLAIM_SIZE_PADDED / DIGEST_LEN
INITIAL_FIAT_SHAMIR_CAP_OFFSET = BYTECODE_CLAIM_OFFSET + BYTECODE_CLAIM_SIZE_PADDED
ORIGINAL_BYTECODE_POINT_N_VARS = ORIGINAL_POINT_N_VARS_PLACEHOLDER
ORIGINAL_BYTECODE_CLAIM_SIZE = ORIGINAL_CLAIM_SIZE_PLACEHOLDER
ORIGINAL_BYTECODE_CLAIM_SIZE_PADDED = ORIGINAL_CLAIM_SIZE_PADDED_PLACEHOLDER
ORIGINAL_BYTECODE_CLAIM_NUM_CHUNKS = ORIGINAL_BYTECODE_CLAIM_SIZE_PADDED / DIGEST_LEN
ORIGINAL_BYTECODE_SUMCHECK_PROOF_SIZE = ORIGINAL_SUMCHECK_SIZE_PLACEHOLDER
ORIGINAL_REDUCTION_CAP = ORIGINAL_REDUCTION_CAP_PLACEHOLDER
ORIGINAL_CLAIM_OFFSET = INITIAL_FIAT_SHAMIR_CAP_OFFSET + DIGEST_LEN
APPLICATION_ROOT_OFFSET = ORIGINAL_CLAIM_OFFSET + ORIGINAL_BYTECODE_CLAIM_SIZE_PADDED
NODE_INFO_SIZE = APPLICATION_ROOT_OFFSET + DIGEST_LEN
NODE_INFO_NUM_CHUNKS = NODE_INFO_SIZE / DIGEST_LEN
BYTECODE_SUMCHECK_PROOF_SIZE = BYTECODE_SUMCHECK_PROOF_SIZE_PLACEHOLDER
EXPECTED_CHILD_CAP = EXPECTED_CHILD_CAP_PLACEHOLDER

LIFTED_INFO_SIZE = LIFTED_INFO_SIZE_PLACEHOLDER
LIFTED_INFO_NUM_CHUNKS = LIFTED_INFO_NUM_CHUNKS_PLACEHOLDER
LIFTED_APPLICATION_DIGEST_OFFSET = LIFTED_APPLICATION_DIGEST_OFFSET_PLACEHOLDER

NODE_INFO_ADDRESS_FUNCTION_PLACEHOLDER


def main():
    pub_mem = 0
    build_preamble_memory()

    node_info = NODE_INFO_ALLOCATION_PLACEHOLDER
    hint_witness("node_info", node_info)
    node_info[0] = NODE_INFO_DOMAIN
    node_info[1] = 2
    set_to_6_zeros(node_info + 2)
    for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
        node_info[BYTECODE_CLAIM_OFFSET + k] = 0

    child_cap = node_info + INITIAL_FIAT_SHAMIR_CAP_OFFSET
    for k in unroll(0, DIGEST_LEN):
        child_cap[k] = EXPECTED_CHILD_CAP[k]

    lifted_infos = Array(2)
    child_public_inputs = Array(2)
    child_bytecode_claims = Array(2)
    original_bytecode_claims = Array(2)
    for i in unroll(0, 2):
        lifted_info = Array(LIFTED_INFO_SIZE)
        hint_witness("lifted_info", lifted_info)
        lifted_info[0] = LEAF_INFO_DOMAIN
        lifted_info[1] = 1
        set_to_6_zeros(lifted_info + 2)
        child_public_input = Array(DIGEST_LEN)
        slice_hash(lifted_info, LIFTED_INFO_NUM_CHUNKS, child_public_input)
        lifted_infos[i] = lifted_info
        original_bytecode_claims[i] = lifted_info + DIGEST_LEN
        child_public_inputs[i] = child_public_input
        child_bytecode_claims[i] = recursion(child_public_input, child_cap)

    reduce_bytecode_claims(
        child_bytecode_claims,
        2,
        node_info + BYTECODE_CLAIM_OFFSET,
        child_cap,
    )

    original_cap = Array(DIGEST_LEN)
    for k in unroll(0, DIGEST_LEN):
        original_cap[k] = ORIGINAL_REDUCTION_CAP[k]
    for k in unroll(ORIGINAL_BYTECODE_CLAIM_SIZE, ORIGINAL_BYTECODE_CLAIM_SIZE_PADDED):
        node_info[ORIGINAL_CLAIM_OFFSET + k] = 0
    reduce_original_bytecode_claims(
        original_bytecode_claims,
        2,
        node_info + ORIGINAL_CLAIM_OFFSET,
        original_cap,
    )

    application_preimage = Array(3 * DIGEST_LEN)
    application_preimage[0] = NODE_INFO_DOMAIN
    application_preimage[1] = 2
    set_to_6_zeros(application_preimage + 2)
    copy_8(
        lifted_infos[0] + LIFTED_APPLICATION_DIGEST_OFFSET,
        application_preimage + DIGEST_LEN,
    )
    copy_8(
        lifted_infos[1] + LIFTED_APPLICATION_DIGEST_OFFSET,
        application_preimage + 2 * DIGEST_LEN,
    )
    computed_root = slice_hash_ret(application_preimage, 3)
    copy_8(computed_root, node_info + APPLICATION_ROOT_OFFSET)

    NODE_INFO_PUBLIC_OUTPUT_PLACEHOLDER
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


def reduce_original_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output, initial_fiat_shamir_cap):
    debug_assert(n_bytecode_claims != 0)
    bytecode_sumcheck_proof = Array(ORIGINAL_BYTECODE_SUMCHECK_PROOF_SIZE)
    hint_witness("original_bytecode_sumcheck_proof", bytecode_sumcheck_proof)
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
        for k in unroll(ORIGINAL_BYTECODE_CLAIM_SIZE, ORIGINAL_BYTECODE_CLAIM_SIZE_PADDED):
            assert claim_ptr[k] == 0
        running_capacity = slice_hash_continue(running_capacity, claim_ptr, ORIGINAL_BYTECODE_CLAIM_NUM_CHUNKS)
        rc_buf[i + 1] = running_capacity

    running_capacity: Mut = rc_buf[n_bytecode_claims - 1]
    last_claim = bytecode_claims[n_bytecode_claims - 1]
    for k in unroll(ORIGINAL_BYTECODE_CLAIM_SIZE, ORIGINAL_BYTECODE_CLAIM_SIZE_PADDED):
        assert last_claim[k] == 0
    running_capacity = slice_hash_continue(running_capacity, last_claim, ORIGINAL_BYTECODE_CLAIM_NUM_CHUNKS - 1)
    reduction_fs: Mut = fs_new(bytecode_sumcheck_proof, running_capacity)
    reduction_fs = fs_observe_chunks(reduction_fs, last_claim + (ORIGINAL_BYTECODE_CLAIM_NUM_CHUNKS - 1) * DIGEST_LEN, 1)
    reduction_fs, alpha = fs_sample_ef(reduction_fs)
    alpha_powers = powers(alpha, n_bytecode_claims)

    all_values = Array(n_bytecode_claims * DIM)
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        copy_ef(claim_ptr + ORIGINAL_BYTECODE_POINT_N_VARS * DIM, all_values + i * DIM)
    claimed_sum = Array(DIM)
    dot_product_ee_dynamic(all_values, alpha_powers, claimed_sum, n_bytecode_claims)
    reduction_fs, challenges, final_eval = sumcheck_verify(
        reduction_fs, ORIGINAL_BYTECODE_POINT_N_VARS, claimed_sum, 2
    )

    eq_evals = Array(n_bytecode_claims * DIM)
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        poly_eq_ee(claim_ptr, challenges, eq_evals + i * DIM, ORIGINAL_BYTECODE_POINT_N_VARS)
    w_r = Array(DIM)
    dot_product_ee_dynamic(eq_evals, alpha_powers, w_r, n_bytecode_claims)
    bytecode_value_at_r = div_extension_ret(final_eval, w_r)

    copy_many_ef(challenges, bytecode_claim_output, ORIGINAL_BYTECODE_POINT_N_VARS)
    copy_ef(bytecode_value_at_r, bytecode_claim_output + ORIGINAL_BYTECODE_POINT_N_VARS * DIM)
    return
