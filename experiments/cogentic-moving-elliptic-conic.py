#!/usr/bin/env python3
"""Check fixed separating markings in the two moving conic families."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import prod
from pathlib import Path
from runpy import run_path


MOVING = run_path(str(Path(__file__).with_name("cogentic-moving-elliptic-separation.py")))
PAIRS = MOVING["PAIRS"]
curve = MOVING["curve"]
pair_label = MOVING["pair_label"]
rank = MOVING["binary_rank"]


def permitted(z, a, h):
    if z == 0:
        return bool(a and h and a != h)
    return h == 0 and a not in (0, z)


def fixed_markings(z, a, h, f):
    possible = set(range(3))
    for u in range(4):
        labels = dict(zip(PAIRS, (0, a, z, h, u, f), strict=True))
        marks = {m for m in range(3)
                 if MOVING["separation_rank"](MOVING["label_rows"](labels, z, m)) == 3}
        assert marks
        possible &= marks
    return possible


def check_boolean():
    count = 0
    for z, a, h in product(range(4), repeat=3):
        if not permitted(z, a, h):
            continue
        for f in range(4):
            assert bool(fixed_markings(z, a, h, f)) == (z == 0 or f != a ^ z)
            count += 4
    assert count == 192


def local_parameters(b, seed, p):
    b = b.numerator * pow(b.denominator, -1, p) % p
    seed = seed.numerator * pow(seed.denominator, -1, p) % p
    w = (seed*seed+b) % p
    good = []
    for parameter in range(p):
        denominator = (1-w*parameter*parameter) % p
        if not denominator:
            assert (w*parameter-seed) % p != 0
            continue
        t = (seed+2*(w*parameter-seed)*pow(denominator, -1, p)) % p
        s = (1+parameter*(t-seed)) % p
        assert (t*t+b-w*s*s) % p == 0
        c = -t*t % p
        if c not in (0, 1, b):
            good.append((0, 1, b, c))
    assert len(good) >= p-12
    return good


def kummer_rows(coordinates, marking, p):
    roots, point = curve(coordinates, marking)
    assert point[1]**2 % p == prod(point[0]-root for root in roots) % p
    rows = []
    for root in roots[:2]:
        values = [prod(root-other for other in roots if other != root) if x == root else x-root
                  for x in (*roots[:2], point[0])]
        rows.append(sum((pow(value % p, (p-1)//2, p) == p-1) << j
                        for j, value in enumerate(values)))
    return rows


def invariant(coordinates, marking, p):
    r1, r2, r3 = curve(coordinates, marking)[0]
    lam = (r3-r1)*pow((r2-r1) % p, -1, p) % p
    return 256*(1-lam+lam*lam)**3*pow(lam*lam*(1-lam)**2 % p, -1, p) % p


def check_pair(p, q, b):
    z, a, h = (pair_label(value, p, q) for value in (-1, b, b-1))
    assert permitted(z, a, h)
    first = pair_label(-1-b, p, q)
    for seed in (Fraction(1), b):
        f = pair_label(-seed*seed-b, p, q)
        assert f == (first if seed == 1 else first ^ a)
        marks = fixed_markings(z, a, h, f)
        if not marks:
            continue
        m = min(marks)
        p_good, q_good = (local_parameters(b, seed, prime) for prime in (p, q))
        for p_coordinates, q_coordinates in product(p_good, q_good):
            assert rank(kummer_rows(p_coordinates, m, p) + kummer_rows(q_coordinates, m, q)) == 3
        sizes = []
        for good, prime in ((p_good, p), (q_good, q)):
            fibers = Counter(invariant(coordinates, m, prime) for coordinates in good)
            assert max(fibers.values(), default=0) <= 24
            assert 24*len(fibers) >= prime-12
            sizes.append(len(fibers))
        return tuple(sizes)
    raise AssertionError("neither seed has a fixed marking")


if __name__ == "__main__":
    check_boolean()
    fixtures = ((13, 17, Fraction(3)), (19, 13, Fraction(5)), (13, 19, Fraction(5)),
                (19, 23, Fraction(2)), (53, 73, Fraction(52, 49)))
    counts = [check_pair(*fixture) for fixture in fixtures]
    print("Checked all 192 label configurations.")
    print(f"Distinct local j-invariant counts on five separating pairs: {counts}.")
