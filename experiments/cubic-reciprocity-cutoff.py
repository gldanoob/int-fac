"""Exact Eisenstein cubic residue checks with no third-party dependencies."""

from collections import Counter
from itertools import combinations, product
from math import gcd, isqrt

UNITS = ((1, 0), (0, 1), (-1, -1))


def multiply(z, w, modulus):
    a, b = z
    c, d = w
    return (a*c-b*d) % modulus, (a*d+b*c-b*d) % modulus


def exponentiate(z, exponent, modulus):
    out = (1, 0)
    while exponent:
        if exponent & 1:
            out = multiply(out, z, modulus)
        z = multiply(z, z, modulus)
        exponent //= 2
    return out


def norm(z):
    a, b = z
    return a*a-a*b+b*b


def conjugate(z):
    a, b = z
    return a-b, -b


def primes(bound):
    return [p for p in range(2, bound+1)
            if all(p % t for t in range(2, isqrt(p)+1))]


def primary_split(p):
    """The prime above p with b>0 and a+bω ≡ 2 mod 3."""
    radius = isqrt(2*p)
    for a, b in product(range(-radius, radius+1), range(3, radius+1, 3)):
        if a % 3 == 2 and norm((a, b)) == p:
            return a, b
    raise ValueError(("no primary split factor", p))


def split_symbol(z, pi):
    """Exponent of ω in the cubic residue symbol at a norm-prime π."""
    p = norm(pi)
    omega = (-pi[0]*pow(pi[1], -1, p)) % p
    value = (z[0]+z[1]*omega) % p
    if not value:
        return None
    power = pow(value, (p-1)//3, p)
    return next(i for i in range(3) if pow(omega, i, p) == power)


def rational_symbol(z, p):
    """Exponent mod 3 for denominator (p), with None for nonunits."""
    if p == 3:
        raise ValueError("The ramified denominator requires a supplementary law")
    if p % 3 == 1:
        pi = PRIMARY[p]
        left = split_symbol(z, pi)
        right = split_symbol(z, conjugate(pi))
        return None if left is None or right is None else (left+right) % 3

    if z[0] % p == z[1] % p == 0:
        return None
    power = exponentiate(z, (p*p-1)//3, p)
    return next(i for i, u in enumerate(UNITS) if tuple(t % p for t in u) == power)


def composite_char(z, p, q, exp):
    left, right = rational_symbol(z, p), rational_symbol(z, q)
    return None if left is None or right is None else (exp[0]*left+exp[1]*right) % 3


def check_fibers(p, q, exp):
    """Exact zero averages along both CRT directions of denominator pq."""
    n = p*q
    rows = ({}, {})
    for z in product(range(n), repeat=2):
        value = composite_char(z, p, q, exp)
        if value is None:
            continue
        for divisor, table in zip((p, q), rows):
            key = tuple(t % divisor for t in z)
            table.setdefault(key, [0, 0, 0])[value] += 1
    for table in rows:
        assert table and all(c[0] == c[1] == c[2] and c[0] > 0 for c in table.values())
    return tuple(len(t) for t in rows)


P = [p for p in primes(400) if p != 3]
PRIMARY = {p: primary_split(p) for p in P if p % 3 == 1}


if __name__ == "__main__":
    assert all(multiply(pi, conjugate(pi), 5*p) == (p, 0)
               for p, pi in PRIMARY.items())
    assert all(pi[0] % 3 == 2 and pi[1] % 3 == 0
               for pi in PRIMARY.values())
    type_counts = Counter()
    for ell, pi in PRIMARY.items():
        for p in P:
            if p == ell:
                continue
            left = split_symbol((p, 0), pi)
            assert left == rational_symbol(pi, p)
            assert (left == 0) == (pow(p, (ell-1)//3, ell) == 1)
            type_counts[p % 3] += 1
    print("prime denominator comparisons (split, inert)", type_counts[1], type_counts[2])

    tests = Counter()
    for ell, pi in PRIMARY.items():
        small = [p for p in P if p < 50 and p != ell]
        for p, q in combinations(small, 2):
            for a, b in ((1, 1), (1, 2), (2, 1), (2, 2)):
                w = p**a*q**b
                left = split_symbol((w, 0), pi)
                assert left == composite_char(pi, p, q, (a, b))
                assert (left == 0) == (pow(w, (ell-1)//3, ell) == 1)
                tests[tuple(sorted((p % 3, q % 3)))] += 1
    print("composite denominator comparisons", sorted(tests.items()))

    for p, q in ((5, 11), (5, 7), (7, 13)):
        for exp in ((1, 1), (1, 2), (2, 1)):
            print("primitive Fourier fibers", p, q, exp, check_fibers(p, q, exp))
    try:
        rational_symbol((2, 3), 3)
    except ValueError:
        print("ramified p=3 correctly excluded")
    else:
        raise AssertionError("missing ramified-prime guard")

    balanced = [p for p in primes(2000) if p >= 1009]
    markers = sorted(PRIMARY)
    count = len(balanced)
    expected = {1:14184, 2:5352, 3:1906, 5:132, 8:2, 12:0, 20:0, len(markers):0}
    for prefix, expected_union in expected.items():
        vectors = [tuple(split_symbol((p, 0), PRIMARY[ell]) for ell in markers[:prefix])
                   for p in balanced]
        tally = Counter(vectors)
        zero = tally[(0,)*prefix]
        product_bad = sum(size*tally[tuple((-x) % 3 for x in vec)]
                          for vec, size in tally.items()) - zero
        quotient_bad = sum(size*(size-1) for size in tally.values())
        union_bad = sum(not any(x) or x == y or x == tuple((-t) % 3 for t in y)
                        for i, x in enumerate(vectors) for j, y in enumerate(vectors) if i != j)
        print(prefix, markers[prefix-1], count, zero, product_bad, quotient_bad, union_bad)
        assert union_bad == expected_union
