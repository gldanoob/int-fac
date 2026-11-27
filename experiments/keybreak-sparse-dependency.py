"""Find verified binary dependencies using exact sparse Wiedemann probes."""

from math import gcd, isqrt, prod
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


def apply_rows(rows, vector):
    output = []
    for row in rows:
        value = 0
        for column in row:
            value ^= vector[column]
        output.append(value)
    return output


def apply(rows, vector):
    return apply_rows(rows, vector) + [0]


def krylov_null_vector(operator, n, modulus, rng):
    degree = modulus.bit_length() - 1
    u = [rng.getrandbits(degree) for _ in range(n)]
    v = [rng.getrandbits(degree) for _ in range(n)]
    term, sequence = v, []
    for _ in range(2 * n):
        sequence.append(dot(u, term, modulus))
        term = operator(term)
    polynomial = berlekamp_massey(sequence, modulus)
    if polynomial[0]:
        return None

    # Horner evaluation of (polynomial / t)(M) v.
    vector = [0] * n
    for coefficient in reversed(polynomial[1:]):
        vector = [
            entry ^ multiply(coefficient, start, modulus)
            for entry, start in zip(operator(vector), v)
        ]
    return vector if any(vector) and not any(operator(vector)) else None


def binary_component(rows, vector, tags=None):
    if vector is None or any(apply_rows(rows, vector)):
        return None
    tagged = vector if tags is None else apply_rows(tags, vector)
    word = next((entry for entry in tagged if entry), 0)
    if not word:
        return None
    bit = word & -word
    binary = [int(bool(entry & bit)) for entry in vector]
    if any(apply_rows(rows, binary)) or (tags is not None and not any(apply_rows(tags, binary))):
        return None
    return tuple(j for j, entry in enumerate(binary) if entry)


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
        vector = krylov_null_vector(lambda term: apply(rows, term), n, modulus, rng)
        selected = binary_component(rows, vector)
        if selected:
            return selected
    return None


def marked_dependency(rows, tags, columns, *, rng=None, attempts=8, field_degree=None):
    """Return columns killed by rows but having a nonzero tag, or None.

    Both binary matrices use sparse rows with column indices in range(columns).
    Each attempt uses fresh random diagonals and scalar probes.
    """
    columns = index(columns)
    rows = tuple(tuple(map(index, row)) for row in rows)
    tags = tuple(tuple(map(index, row)) for row in tags)
    if columns < 1 or any(j < 0 or j >= columns for row in rows + tags for j in row):
        raise ValueError("expected positive column count and in-range column indices")
    degree = (8 * columns).bit_length() if field_degree is None else index(field_degree)
    attempts = index(attempts)
    if attempts < 1 or degree < 1:
        raise ValueError("expected positive probe budget and field degree")
    if not any(tags):
        return None
    modulus = irreducible(degree)
    rng = Random() if rng is None else rng

    for _ in range(attempts):
        row_weights = [rng.getrandbits(degree) for _ in rows]
        column_weights = [rng.getrandbits(degree) for _ in range(columns)]

        def operator(vector):
            # Apply E Mᵀ D M with two sparse passes through M.
            output = [0] * columns
            for row, value, weight in zip(rows, apply_rows(rows, vector), row_weights):
                weighted = multiply(value, weight, modulus)
                for j in row:
                    output[j] ^= weighted
            return [multiply(entry, weight, modulus) for entry, weight in zip(output, column_weights)]

        vector = krylov_null_vector(operator, columns, modulus, rng)
        selected = binary_component(rows, vector, tags)
        if selected:
            return selected
    return None



def check_hidden_root_split(modulus, a, b, fiber_size, rng):
    # The first six public columns have four independent duplicate relations.
    # The last column is the only hidden label. Each row enforces one parity.
    values = (a, a, a, b, b, b, a*b)
    selected = marked_dependency(((0, 1, 2, 6), (3, 4, 5, 6)), ((6,),), len(values), rng=rng)
    assert selected and 6 in selected
    product = prod(values[i] for i in selected)
    rational_root = isqrt(product)
    assert rational_root**2 == product

    def roots(value):
        return [x for x in range(1, modulus) if x*x % modulus == value]

    root_a, root_b = min(roots(a)), min(roots(b))
    public = prod(root_a if i < 3 else root_b for i in selected if i < 6)
    hidden = roots(a*b)
    assert len(hidden) == fiber_size
    splits = 0
    for root in hidden:
        assert (public*root)**2 % modulus == product % modulus
        divisor = gcd(public*root-rational_root, modulus)
        splits += 1 < divisor < modulus
    assert splits == fiber_size - 2


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

    rows = tuple((2 * j, 2 * j + 1) for j in range(21))
    chosen = marked_dependency(rows, ((0, 2),), 42, rng=rng)
    assert chosen and (0 in chosen) != (2 in chosen)
    assert all(sum(j in chosen for j in row) % 2 == 0 for row in rows)
    assert marked_dependency(rows, ((), ()), 42, rng=rng) is None
    assert marked_dependency(rows, ((0, 1),), 42, rng=rng) is None
    assert 3 in marked_dependency((), ((3,),), 5, rng=rng)
    print("Verified marked extraction with 20 unmarked dimensions, zero tags, and zero constraints.")
    for modulus, a, b, size in ((143, 3, 14, 4), (1573, 3, 14, 4), (2431, 38, 42, 8)):
        check_hidden_root_split(modulus, a, b, size, rng)
    print("Verified proper integer gcds for 2/4, 2/4 and 6/8 hidden roots.")


if __name__ == "__main__":
    replay()
