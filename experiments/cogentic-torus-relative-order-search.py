"""Find a factor or a common relation lattice for norm-one bases over Z/NZ."""

import argparse
import json
from itertools import product
from math import gcd, isqrt
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).resolve().parent
interval_rectangles = run_path(str(HERE / "cogentic-boxed-order-relations.py"))["interval_rectangles"]
tuple_collision = run_path(str(HERE / "cogentic-unit-collision-search.py"))["tuple_collision"]
TORUS = run_path(str(HERE / "cogentic-varying-norm-torus.py"))
multiply, power, quotient_power = (TORUS[name] for name in ("multiply", "power", "quotient_power"))


def entries(ranges, bases, half, k, n):
    powers = [[(e, power(base, e, k, n)) for e in interval]
              for interval, base in zip(ranges, bases, strict=True)]
    labels, words = [], []
    for choices in product(*powers):
        exponents, factors = zip(*choices)
        value = (1, 0)
        for factor in factors:
            value = multiply(value, factor, k, n)
        a, b = value
        labels.append(((a + half*b) % n, b))
        words.append(exponents)
    return labels, words


def prefix_search(n, k, half, bases, ranges, stats):
    stats["prefix_tests"] += 1
    inverses = [((a+b) % n, -b % n) for a, b in bases]
    relation = None
    for left_ranges, right_ranges in interval_rectangles(ranges):
        left, left_words = entries(left_ranges, bases, half, k, n)
        right, right_words = entries(right_ranges, inverses, half, k, n)
        stats["list_entries"] += len(left) + len(right)
        hit = tuple_collision(n, left, right, prefer_split=True)
        if hit is None:
            continue
        if hit["status"] == "local-split":
            return hit["factor"], None
        relation = tuple(a+b for a, b in zip(left_words[hit["left_index"]],
                                            right_words[hit["right_index"]], strict=True))
    return None, relation


def relative_search(n, parameters, bound=None):
    """Use the bases (a + sqrt(3))/(a - sqrt(3)) for the supplied parameters."""
    if n < 3 or n % 2 == 0 or not parameters or (bound is not None and bound < 1):
        raise ValueError("require an odd N >= 3, at least one base, and a positive bound")
    if bound is None:
        bound = isqrt(n) + 1
    stats = dict(bound=bound, prefix_tests=0, list_entries=0)
    if n % 3 == 0:
        if n == 3:
            return dict(stats, status="ineligible")
        return dict(stats, status="factor", factor=3, stage=0)

    half = pow(2, -1, n)
    k = -half % n
    active, relations, radices = [], [], []
    size = 1
    for stage, a in enumerate(parameters, 1):
        denominator_gcd = gcd(a*a - 3, n)
        if denominator_gcd == n:
            return dict(stats, status="ineligible", stage=stage)
        if denominator_gcd != 1:
            return dict(stats, status="factor", factor=denominator_gcd, stage=stage)
        base = quotient_power(n, k, (a-1, 2), 1)
        bases = [g for _, g, _ in active] + [base]
        ranges = [range(radix) for _, _, radix in active]
        low, high = 1, bound//size
        factor, relation = prefix_search(n, k, half, bases, ranges + [range(1, high+1)], stats)
        if factor is not None:
            return dict(stats, status="factor", factor=factor, stage=stage)
        if relation is None:
            return dict(stats, status="bound-exhausted", stage=stage)
        high = relation[-1]
        while low < high:
            middle = (low+high)//2
            factor, hit = prefix_search(n, k, half, bases, ranges + [range(1, middle+1)], stats)
            if factor is not None:
                return dict(stats, status="factor", factor=factor, stage=stage)
            if hit is None:
                low = middle+1
            else:
                relation = hit
                high = hit[-1]
        indices = [i for i, _, _ in active] + [stage]
        relations.append([(i, e) for i, e in zip(indices, relation, strict=True) if e])
        radices.append(low)
        size *= low
        if low > 1:
            active.append((stage, base, low))
    return dict(stats, status="common-kernel", radices=radices, relations=relations, order=size)


def replay():
    for n, a, primes in [(137549, 13, (263, 523)), (13073941, 17, (2557, 5113))]:
        result = relative_search(n, [3, a])
        assert result["status"] == "factor" and result["stage"] == 2
        assert result["factor"] in primes
    result = relative_search(13073941, [3, 3, 17])
    assert result["status"] == "factor" and result["stage"] == 3
    result = relative_search(11**2*17, [0, 0])
    assert result["status"] == "common-kernel" and result["radices"] == [2, 1]
    assert result["relations"] == [[(1, 2)], [(1, 1), (2, 1)]]
    assert relative_search(13073941, [3, 17], 1)["status"] == "bound-exhausted"
    assert relative_search(11*263, [17])["factor"] == 11
    print("Relative-order replay passed two rough fixtures, a third-base split and a common kernel.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?", help="omit to run the self-check")
    parser.add_argument("--bases", type=int, nargs="+", default=[3, 17], metavar="A",
                        help="parameters a in (a + sqrt(3))/(a - sqrt(3))")
    parser.add_argument("--bound", type=int, help="maximum box volume, default floor(sqrt(N))+1")
    args = parser.parse_args()
    if args.N is None:
        replay()
    else:
        try:
            print(json.dumps(relative_search(args.N, args.bases, args.bound), sort_keys=True))
        except ValueError as error:
            parser.error(str(error))
