"""Verify CRT fibers and the finite-support splitting test on odd prime powers."""

from collections import defaultdict
from itertools import combinations
from math import gcd, isqrt


def scan(n, support):
    pairs = sorted((z * z % n, z) for z in support if gcd(z, n) == 1)
    previous_square = -1
    first = 0
    for square, z in pairs:
        if square != previous_square:
            previous_square, first = square, z
        elif z != first and (z + first) % n != 0:
            factor = gcd(first - z, n)
            assert 1 < factor < n
            return factor
    return None


def replay():
    cases = fibers = contrasts = 0
    for n, omega in [(15, 2), (45, 2), (63, 2), (77, 2), (105, 3), (315, 3), (1155, 4)]:
        units = [z for z in range(1, n) if gcd(n, z) == 1]
        groups = defaultdict(list)
        for z in units:
            groups[z * z % n].append(z)
        for roots in groups.values():
            assert len(roots) == 2 ** omega
            assert len({min(z, n-z) for z in roots}) == 2 ** (omega - 1)
            fibers += 1
            for z, zprime in combinations(roots, 2):
                answer = scan(n, [z, zprime])
                assert (answer is None) == ((z + zprime) % n == 0)
                contrasts += answer is not None
        assert scan(n, range(1, isqrt(n - 1) + 1)) is None
        assert scan(n, units) is not None
        cases += 1
    return cases, fibers, contrasts


if __name__ == "__main__":
    print("moduli, full fibers, proper factors from two-root supports", *replay())
