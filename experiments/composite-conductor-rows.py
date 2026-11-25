"""Finite CRT lifts of independent Frobenius rows for indices 4, 6 and 8."""
from itertools import combinations, product
from math import gcd, isqrt, prod


def primes(low, high):
    return [n for n in range(low, high+1)
            if all(n % d for d in range(2, isqrt(n)+1))]


def discrete_table(p):
    g = next(g for g in range(2, p)
             if len({pow(g, i, p) for i in range(p-1)}) == p-1)
    return {pow(g, i, p): i for i in range(p-1)}


def row_for(k, prime_powers, x, y):
    row = [0] * len(x)
    for modulus in prime_powers:
        match = next(((i, j, d) for i, j in combinations(range(len(x)), 2)
                      if gcd((d := x[i]*y[j] - x[j]*y[i]), modulus) == 1), None)
        if match is None:
            return None
        i, j, determinant = match
        inv = pow(determinant, -1, modulus)
        cofactor = k//modulus
        idempotent = cofactor*pow(cofactor, -1, modulus)
        row[i] = (row[i]+idempotent*y[j]*inv) % k
        row[j] = (row[j]-idempotent*y[i]*inv) % k
    return tuple(row)


def paired_kernel(k, row):
    def value(v):
        return sum(a*b for a, b in zip(row, v)) % k

    zero = (0,)*len(row)
    vectors = list(product(range(k), repeat=len(row)))
    delta = next(v for v in vectors if value(v) == 1)
    generators = [tuple(((i == j)-row[i]*delta[j]) % k for j in range(len(row)))
                  for i in range(len(row))]
    generated = {zero}
    for generator in generators:
        generated = {tuple((v+e*g) % k for v, g in zip(x, generator))
                     for x in generated for e in range(k)}
    exact = {v for v in vectors if value(v) == 0}
    assert generated == exact
    return delta, len(exact)


for k, prime_powers, conductors in ((4, (4,), (17, 97, 113)),
                                    (6, (2, 3), (73, 97, 193, 241)),
                                    (8, (8,), (97, 193, 257))):
    logs = [discrete_table(p) for p in conductors]
    ps = primes(1009, 1400)
    states = [tuple(log[p % ell] % k for log, ell in zip(logs, conductors))
              for p in ps]
    tested = 0
    hard = None
    example = None
    for (p, x), (q, y) in combinations(zip(ps, states), 2):
        row = row_for(k, prime_powers, x, y)
        if row is None:
            continue
        assert sum(a*b for a, b in zip(row, x)) % k == 1
        assert sum(a*b for a, b in zip(row, y)) % k == 0
        assert sum(a != 0 for a in row) <= 2*len(prime_powers)
        tested += 1
        if example is None:
            example = p, q, x, y, row
        if all(gcd(a, k) > 1 for a in row) and all(
                gcd(x[i]*y[j] - x[j]*y[i], k) > 1
                for i, j in combinations(range(len(x)), 2)):
            hard = p, q, x, y, row
    if k == 6:
        assert hard
    pair = hard or example
    print(k, conductors, tested, pair, paired_kernel(k, pair[-1]))
