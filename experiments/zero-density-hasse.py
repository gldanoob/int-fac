"""Exact product-coefficient checks for splitting a repeated prime Dirichlet polynomial."""

from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import isqrt, prod
from pathlib import Path
import runpy


def multiply(first, second):
    out = defaultdict(F)
    for m, x in first.items():
        for r, y in second.items():
            out[m * r] += x * y
    return dict(out)


def check_compact_density_margin():
    sigma, g = F(79, 100), F(49, 50)
    cutoff = F(25, 32)
    assert cutoff > F(38, 49)
    assert 9 / (8 * (2 * cutoff - 1)) == 2
    bounds = (9 / (8 * (2 * sigma - 1)),
              3 / (2 * F(4, 5)),
              3 / (3 * F(9, 10) - 1))
    largest = max(bounds)
    assert g - largest / 2 == F(49, 50) - F(225, 232)
    mesh, epsilon = F(1, 10000), F(1, 100000)
    assert largest * mesh + epsilon < (2 * g - largest) / 20
    print(f"three density margins: {', '.join(str(g - bound / 2) for bound in bounds)}")


def check_two_searches():
    """Use deliberately small, distinct menus to exercise both searches and fallback."""
    ecm = runpy.run_path(str(Path(__file__).with_name("moving-legendre.py")))
    cube = runpy.run_path(str(Path(__file__).with_name("mean-time-ecm.py")))["shifts"]
    primes = [p for p in ecm["primes_up_to"](1601) if 113 <= p <= 293 or p >= 1151]
    paid = [0, 0, 0]
    fixtures = [p * q for i, p in enumerate(primes) for q in primes[i+1:i+5]]
    fixtures += [127**2 * 137, 131**2, 137 * 139 * 149, 151**3]
    for n in fixtures:
        pending, leaves = [n], []
        while pending:
            d = pending.pop()
            if ecm["toy_prime"](d):
                leaves.append(d)
                continue
            k = (d.bit_length() + 1) // 2
            seed = (d >> k) % (1 << k)
            for route, bound in enumerate((3, 13)):
                scalar = ecm["odd_scalar"](d, bound)
                try:
                    for shift in cube(k, 1):
                        lam = seed ^ shift
                        if all(ecm["checked_gcd"](v, d) == 1 for v in (lam, lam-1)):
                            ecm["marked_product"](next(ecm["marks"](2, 1)), lam, scalar, d)
                except ecm["ProperFactor"] as found:
                    factor = found.args[0]
                    break
            else:
                # Small finite replay of the always-finishing divisor-search branch.
                route = 2
                factor = next(v for v in range(2, isqrt(d) + 1) if d % v == 0)
            assert 1 < factor < d and d % factor == 0
            paid[route] += 1
            pending.extend((factor, d // factor))
        assert prod(leaves) == n and all(ecm["toy_prime"](v) for v in leaves)
    assert all(paid), paid
    print(f"{len(fixtures)} complete integer-only examples, splits by first, second and fallback {paid}")


def main():
    slot = {r: F(w, r) for r, w in zip((7, 11, 13, 17, 19), (2, 3, 3, 4, 4))}
    cofactors = {m: F(1, m) for m in (21, 35, 49, 55, 65, 77)}
    cases = atoms = tuples = 0
    for count in range(2, 6):
        reference = defaultdict(F)
        for row in product(slot, repeat=count):
            weight = prod(slot[r] for r in row)
            for m, a in cofactors.items():
                reference[m * prod(row)] += a * weight
                tuples += 1
        for split in range(1, count):
            a = cofactors
            for _ in range(count - split):
                a = multiply(a, slot)
            c = {1: F(1)}
            for _ in range(split):
                c = multiply(c, slot)
            assert multiply(a, c) == reference
            for u, weight in a.items():
                choices = sum(u % r == 0 for r in slot)
                assert u * weight <= (4 * choices)**(count - split)
            cases += 1
            atoms += len(reference)
    sigma = F(167, 200)
    g = F(999, 1000)
    margin = g - F(3, 2) / (3 * sigma - 1)
    assert margin > F(1, 500)
    assert sigma + F(31, 200) < 1
    print(f"{tuples} ordered tuples, {cases} splits, {atoms} atom comparisons, "
          f"density margin {margin}, backup exponent margin {1 - sigma - F(31, 200)}")


if __name__ == "__main__":
    main()
    check_compact_density_margin()
    check_two_searches()
