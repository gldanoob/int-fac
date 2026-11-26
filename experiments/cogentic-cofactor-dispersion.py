#!/usr/bin/env python3
"""Replay CRT pooling and changing cofactor omissions on finite windows."""

from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import gcd, lcm, prod

band = (11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
        73, 79, 83, 89, 97, 101)


def smooth(value, omitted=()):
    for p in band:
        if p not in omitted and value % p == 0:
            value //= p
    return value == 1


m, N, g = 11, 379, 2
digits = (5, 1, 3)
assert sum(digit * m**i for i, digit in enumerate(digits)) == N
Q = 6
windows = []
for a, start, length, sign in ((1, 100001, 23, 1), (3, 100201, 19, -1)):
    R = sum(digit * a**i for i, digit in enumerate(digits))
    d = (m - a) * Q
    assert R % (m - a) == N % (m - a)
    hits = [n for n in range(start, start + g * d * length) if smooth(n)]
    counts = Counter(n % (g * d) for n in hits)
    assert counts
    windows.append((start, sign * R, d, length, hits, counts))

d1, d2 = (window[2] for window in windows)
common = gcd(d1, d2)
cycle = lcm(d1, d2)
for offset, restriction in ((0, 1), (2, 3), (1, 4)):
    direct = sum(
        prod(counts[(start + g * R * (offset + restriction * k)) % (g * d)]
             for start, R, d, length, hits, counts in windows)
        for k in range(cycle)
    )
    assert direct
    pooled = Fraction(0)
    for k_class in range(common):
        count_product = Fraction(1)
        for start, R, d, length, hits, _ in windows:
            step = gcd(R * restriction * common, d)
            target = start + g * R * (offset + restriction * k_class)
            count = sum(n % (g * step) == target % (g * step) for n in hits)
            count_product *= Fraction(count, d // step)
        pooled += count_product / common
    assert pooled == Fraction(direct, cycle)

U, T, c, R, q, k0 = 90, 50, 101, 9, 20, 7
hits = [(u, j, c + g * R * u + q * j)
        for u in range(U) for j in range(T) if smooth(c + g * R * u + q * j)]
assert hits
actual = sum(not any(value % p == 0 and (k0 + g * u) % p == 0 for p in band)
             for u, _, value in hits)
assert 0 < actual < len(hits)


def intersection(primes):
    P = prod(primes)
    if P == 1:
        return len(hits)
    u0 = (-k0 * pow(g, -1, P)) % P
    j0 = (-(c + g * R * u0) * pow(q, -1, P)) % P
    count = sum(smooth((c + g * R * u + q * j) // P, primes)
                for u in range(u0, U, P) for j in range(j0, T, P))
    assert count == sum(value % P == 0 and (k0 + g * u) % P == 0
                        for u, _, value in hits)
    return count


order_one = intersection(()) - sum(intersection((p,)) for p in band)
order_two = order_one + sum(intersection(pair) for pair in combinations(band, 2))
assert order_one <= actual <= order_two
print(f"{cycle} cofactor residues, three restricted pools, and {len(hits)} omission-test hits passed.")
