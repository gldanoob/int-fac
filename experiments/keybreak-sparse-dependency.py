"""Find one verified F2 dependency using an exact sparse Wiedemann probe."""

from itertools import product
from operator import index
from random import Random


def multiply(a, b, modulus):
    value = 0
    top = 1 << (modulus.bit_length() - 1)
    while b:
        if b & 1:
            value ^= a
        a <<= 1
        if a & top:
            a ^= modulus
        b >>= 1
    return value


def polynomial_gcd(a, b):
    while b:
        while a.bit_length() >= b.bit_length():
            a ^= b << (a.bit_length() - b.bit_length())
        a, b = b, a
    return a


def irreducible(degree):
    top = 1 << degree
    for modulus in range(top + 1, 2 * top, 2):
        power = 2
        # A reducible candidate has a factor of degree at most half its own.
        for _ in range(degree // 2):
            power = multiply(power, power, modulus)
            if polynomial_gcd(power ^ 2, modulus) != 1:
                break
        else:
            return modulus
    raise ArithmeticError("no irreducible binary polynomial found")


def inverse(value, modulus):
    power = (1 << (modulus.bit_length() - 1)) - 2
    result = 1
    while power:
        if power & 1:
            result = multiply(result, value, modulus)
        value = multiply(value, value, modulus)
        power >>= 1
    return result


def berlekamp_massey(sequence, modulus):
    """Return the monic recurrence polynomial in increasing power order."""
    connection = [1] + [0] * len(sequence)
    backup = connection.copy()
    length, lag, previous_inverse = 0, 1, 1
    for t, value in enumerate(sequence):
        discrepancy = value
        for j in range(1, length + 1):
            discrepancy ^= multiply(connection[j], sequence[t - j], modulus)
        if not discrepancy:
            lag += 1
            continue
        saved = connection.copy()
        scale = multiply(discrepancy, previous_inverse, modulus)
        for j in range(len(connection) - lag):
            connection[j + lag] ^= multiply(scale, backup[j], modulus)
        if 2 * length <= t:
            length = t + 1 - length
            backup = saved
            previous_inverse = inverse(discrepancy, modulus)
            lag = 1
        else:
            lag += 1
    return connection[:length + 1][::-1]


def dot(left, right, modulus):
    value = 0
    for a, b in zip(left, right):
        value ^= multiply(a, b, modulus)
    return value


def apply(rows, vector):
    output = []
    for row in rows:
        value = 0
        for column in row:
            value ^= vector[column]
        output.append(value)
    return output + [0]


def dependency(rows, *, rng=None, attempts=8, field_degree=None):
    """Return a nonempty tuple of dependent columns, or None after the probe budget.

    For C rows the columns are numbered 0 through C. Repeated indices in a
    row contribute modulo two. An optional RNG with getrandbits makes a
    run reproducible.
    """
    rows = tuple(tuple(map(index, row)) for row in rows)
    n = len(rows) + 1
    if any(j < 0 or j >= n for row in rows for j in row):
        raise ValueError("column index outside the C-by-(C+1) matrix")
    degree = (4 * n).bit_length() if field_degree is None else index(field_degree)
    attempts = index(attempts)
    if attempts < 1 or degree < 1:
        raise ValueError("expected positive probe budget and field degree")
    modulus = irreducible(degree)
    rng = Random() if rng is None else rng

    for _ in range(attempts):
        u = [rng.getrandbits(degree) for _ in range(n)]
        v = [rng.getrandbits(degree) for _ in range(n)]
        term, sequence = v, []
        for _ in range(2 * n):
            sequence.append(dot(u, term, modulus))
            term = apply(rows, term)
        polynomial = berlekamp_massey(sequence, modulus)
        if polynomial[0]:
            continue

        # Horner evaluation of (polynomial / t)(M) v.
        vector = [0] * n
        for coefficient in reversed(polynomial[1:]):
            vector = [
                entry ^ multiply(coefficient, start, modulus)
                for entry, start in zip(apply(rows, vector), v)
            ]
        if not any(vector) or any(apply(rows, vector)):
            continue
        word = next(entry for entry in vector if entry)
        bit = word & -word
        selected = tuple(j for j, entry in enumerate(vector) if entry & bit)
        selected_set = set(selected)
        if selected and all(sum(j in selected_set for j in row) % 2 == 0 for row in rows):
            return selected
    return None


def replay():
    rng = Random(2625)
    assert berlekamp_massey([0, 0, 1, 0, 0, 0], irreducible(4)) == [0, 0, 0, 1]
    assert dependency(((1,), (2,), (3,)), rng=rng) == (0,)
    assert dependency(((), (), ()), rng=rng)
    assert dependency(((0, 1), (2,), (0, 1)), rng=rng)
    assert dependency(((0, 1), (1, 2), (2, 3)), rng=rng) == (0, 1, 2, 3)
    for masks in product(range(8), repeat=2):
        rows = tuple(tuple(j for j in range(3) if mask >> j & 1) for mask in masks)
        chosen = dependency(rows, rng=rng, field_degree=4)
        assert chosen and all(sum(j in chosen for j in row) % 2 == 0 for row in rows)
    print("Verified sparse dependencies for 64 binary matrices and four structural fixtures.")


if __name__ == "__main__":
    replay()
