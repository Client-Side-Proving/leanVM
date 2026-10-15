from snark_lib import *


OPT_EXTENSION_ARITHMETIC = OPT_EXTENSION_ARITHMETIC_VALUE
DIM = 5
INV_TWO = 1065353217
INV_SIX = 355117739


@inline
def ef_zero():
    result = Array(DIM)
    for i in unroll(0, DIM):
        result[i] = 0
    return result


@inline
def ef_one():
    result = Array(DIM)
    result[0] = 1
    for i in unroll(1, DIM):
        result[i] = 0
    return result


@inline
def ef_from_base(value):
    result = Array(DIM)
    result[0] = value
    for i in unroll(1, DIM):
        result[i] = 0
    return result


@inline
def ef_copy(value):
    result = Array(DIM)
    for i in unroll(0, DIM):
        result[i] = value[i]
    return result


@inline
def ef_add(a, b):
    result = Array(DIM)
    if OPT_EXTENSION_ARITHMETIC == 1:
        add_ee(a, b, result)
    else:
        for i in unroll(0, DIM):
            result[i] = a[i] + b[i]
    return result


@inline
def ef_sub(a, b):
    result = Array(DIM)
    if OPT_EXTENSION_ARITHMETIC == 1:
        add_ee(b, result, a)
    else:
        for i in unroll(0, DIM):
            result[i] = a[i] - b[i]
    return result


@inline
def ef_scale(value, scalar):
    result = Array(DIM)
    if OPT_EXTENSION_ARITHMETIC == 1:
        scalar_ptr = Array(1)
        scalar_ptr[0] = scalar
        dot_product_be(scalar_ptr, value, result, 1)
    else:
        for i in unroll(0, DIM):
            result[i] = value[i] * scalar
    return result


@inline
def ef_mul(a, b):
    result = Array(DIM)
    dot_product_ee(a, b, result)
    return result


@inline
def ef_square(value):
    return ef_mul(value, value)


@inline
def ef_one_minus(value):
    result = Array(DIM)
    if OPT_EXTENSION_ARITHMETIC == 1:
        add_ee(value, result, ef_one())
    else:
        result[0] = 1 - value[0]
        for i in unroll(1, DIM):
            result[i] = 0 - value[i]
    return result


@inline
def ef_sub_base(value, scalar):
    result = Array(DIM)
    if OPT_EXTENSION_ARITHMETIC == 1:
        add_ee(ef_from_base(scalar), result, value)
    else:
        result[0] = value[0] - scalar
        for i in unroll(1, DIM):
            result[i] = value[i]
    return result


@inline
def ef_assert_equal(a, b):
    for i in unroll(0, DIM):
        assert a[i] == b[i]
    return


def evaluate_cubic_compact(h0, h2, h3, claim, challenge):
    h1 = ef_sub(claim, h0)
    d1 = ef_sub(h1, h0)
    d2 = ef_add(ef_sub(h2, ef_scale(h1, 2)), h0)
    d3 = ef_sub(ef_add(ef_sub(h3, ef_scale(h2, 3)), ef_scale(h1, 3)), h0)

    challenge_minus_one = ef_sub_base(challenge, 1)
    challenge_minus_two = ef_sub_base(challenge, 2)
    choose_two = ef_scale(ef_mul(challenge, challenge_minus_one), INV_TWO)
    choose_three = ef_scale(ef_mul(ef_mul(challenge, challenge_minus_one), challenge_minus_two), INV_SIX)

    return ef_add(
        ef_add(h0, ef_mul(challenge, d1)),
        ef_add(ef_mul(choose_two, d2), ef_mul(choose_three, d3)),
    )


def evaluate_quadratic_compact(h0, h2, claim, challenge):
    h1 = ef_sub(claim, h0)
    d1 = ef_sub(h1, h0)
    d2 = ef_add(ef_sub(h2, ef_scale(h1, 2)), h0)
    choose_two = ef_scale(ef_mul(challenge, ef_sub_base(challenge, 1)), INV_TWO)
    return ef_add(ef_add(h0, ef_mul(challenge, d1)), ef_mul(choose_two, d2))


def extrapolate_01inf(c0, c1, c_inf, challenge):
    linear = ef_add(ef_mul(c0, ef_one_minus(challenge)), ef_mul(c1, challenge))
    infinity_weight = ef_mul(challenge, ef_sub_base(challenge, 1))
    return ef_add(linear, ef_mul(c_inf, infinity_weight))


def eq_points(a, b, length: Const):
    result: Mut = ef_one()
    for i in unroll(0, length):
        equal_zero = ef_mul(ef_one_minus(a + i * DIM), ef_one_minus(b + i * DIM))
        equal_one = ef_mul(a + i * DIM, b + i * DIM)
        result = ef_mul(result, ef_add(equal_zero, equal_one))
    return result


def eq_table(point, length: Const):
    table = Array(DIM * (2**length))
    for index in unroll(0, 2**length):
        value: Mut = ef_one()
        for coordinate in unroll(0, length):
            bit = div_floor(index, 2 ** (length - 1 - coordinate)) % 2
            factor: Imm
            if bit == 1:
                factor = point + coordinate * DIM
            else:
                factor = ef_one_minus(point + coordinate * DIM)
            value = ef_mul(value, factor)
        for coefficient in unroll(0, DIM):
            table[index * DIM + coefficient] = value[coefficient]
    return table
