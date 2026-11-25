"""Greedy squarefree blocks, dyadic order constraints and their character bound."""

from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations
from math import gcd, prod


def subsets(items):
    for size in range(len(items) + 1):
        yield from combinations(items, size)


def check(q):
    primes = [p for p in (2, 3, 5, 7, 11, 13, 17, 19) if gcd(p, q) == 1]
    signs = {p: 1 if p % 4 == 1 else -1 for p in primes}
    parts = [row for row in subsets(primes) if row]
    blocks = [row for row in parts if prod(row[:-1]) <= q < prod(row)]

    def weight(row):
        return F(prod(signs[p] for p in row), prod(row))

    def split_prefix(row):
        for stop in range(1, len(row) + 1):
            if prod(row[:stop]) > q:
                return row[:stop], row[stop:]
        return (), row

    direct = 0
    for row in parts:
        a, rest = split_prefix(row)
        b, c = split_prefix(rest)
        if a and b:
            assert a in blocks and b in blocks
            assert a[-1] < b[0] and all(p > b[-1] for p in c)
            direct += weight(row)
        else:
            assert prod(row) <= q*q*max(primes)**2

    cut_sums, remainders = [], []
    orthogonality = 0
    for cutoff in primes:
        ordered = sum(weight(a+b) for a in blocks for b in blocks
                      if a[-1] < b[0] and b[-1] <= cutoff)
        by_siblings = 0
        for level in range((len(primes)-1).bit_length()):
            half = 1 << level
            first, second = {}, {}
            for row in blocks:
                high = primes.index(row[-1])
                low = primes.index(row[0])
                if (high // half) % 2 == 0:
                    first.setdefault(high // (2*half), []).append(row)
                if (low // half) % 2 == 1 and row[-1] <= cutoff:
                    second.setdefault(low // (2*half), []).append(row)
            for i in first.keys() & second.keys():
                by_siblings += sum(map(weight, first[i])) * sum(map(weight, second[i]))
            for lists in (first, second):
                for j in range(max(primes).bit_length()):
                    start = q * 2**j
                    actual = upper = 0
                    for rows in lists.values():
                        residues = defaultdict(F)
                        for row in rows:
                            a = prod(row)
                            if start < a <= 2*start:
                                residues[a % q] += weight(row)
                                upper += (1+start//q) * weight(row)**2
                        actual += sum(v*v for v in residues.values())
                    assert actual <= upper
                    orthogonality += 1
        assert by_siblings == ordered
        cut_sums.append(ordered)
        remainders.append(prod(1 + weight((p,)) for p in primes if p > cutoff))
    # Partial summation for a cutoff-dependent remaining Euler product.
    abel = cut_sums[-1] * remainders[-1]
    for i in range(len(primes)-1):
        abel += cut_sums[i]*(remainders[i]-remainders[i+1])
        assert remainders[i]-remainders[i+1] == weight((primes[i+1],))*remainders[i+1]
    assert abel == direct
    return len(blocks), len(parts), orthogonality


if __name__ == "__main__":
    counts = [check(q) for q in (2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 16, 17)]
    print("moduli, greedy blocks, squarefree products, orthogonality inequalities",
          len(counts), *map(sum, zip(*counts)))
