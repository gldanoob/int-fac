"""Find a factor or a common relation lattice for norm-one bases over Z/NZ."""

import argparse
import json
from itertools import combinations_with_replacement, groupby, product
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).resolve().parent
interval_rectangles = run_path(str(HERE / "cogentic-boxed-order-relations.py"))["interval_rectangles"]
tuple_collision = run_path(str(HERE / "cogentic-unit-collision-search.py"))["tuple_collision"]
TORUS = run_path(str(HERE / "cogentic-varying-norm-torus.py"))
multiply, power, quotient_power = (TORUS[name] for name in ("multiply", "power", "quotient_power"))


def inverse(base, n):
    a, b = base
    return (a+b) % n, -b % n


def signed_power(base, exponent, k, n):
    return power(inverse(base, n) if exponent < 0 else base, abs(exponent), k, n)


def entries(ranges, bases, half, k, n):
    powers = [[(e, signed_power(base, e, k, n)) for e in interval]
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
    inverses = [inverse(base, n) for base in bases]
    relation = None
    for left_ranges, right_ranges in interval_rectangles(ranges):
        left, left_words = entries(left_ranges, bases, half, k, n)
        right, right_words = entries(right_ranges, inverses, half, k, n)
        stats["list_entries"] += len(left) + len(right)
        hit = tuple_collision(n, left, right, prefer_split=True)
        if hit is None:
            continue
        relation = tuple(a+b for a, b in zip(left_words[hit["left_index"]],
                                            right_words[hit["right_index"]], strict=True))
        if hit["status"] == "local-split":
            return hit["factor"], relation
    return None, relation


def search_bound(n, parameters, bound):
    if n < 3 or n % 2 == 0 or not parameters or (bound is not None and bound < 1):
        raise ValueError("require an odd N >= 3, at least one base, and a positive bound")
    return isqrt(n) + 1 if bound is None else bound


def relative_search(n, parameters, bound=None):
    """Use the bases (a + sqrt(3))/(a - sqrt(3)) for the supplied parameters."""
    bound = search_bound(n, parameters, bound)
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


def short_boxes(dimension, bound):
    """Cover nonzero signed words in order of total coefficient bit length."""
    for bits in range(1, bound.bit_length()+1):
        for profile in combinations_with_replacement(range(dimension), bits):
            indices, widths = zip(*((i, 1 << (sum(1 for _ in repeats)-1))
                                    for i, repeats in groupby(profile)))
            for tail_signs in product((1, -1), repeat=len(indices)-1):
                ranges = [range(width, 2*width) if sign == 1 else range(1-2*width, 1-width)
                          for width, sign in zip(widths, (1,) + tail_signs, strict=True)]
                yield indices, ranges, 8*(isqrt(prod(widths)-1)+1)


def adaptive_search(n, parameters, bound=None, *, first_relation=False):
    """Interleave short boxes with doubling relative-order caps on one modulus."""
    bound = search_bound(n, parameters, bound)
    stats = dict(bound=bound, prefix_tests=0, list_entries=0,
                 short_prefix_tests=0, relative_rounds=0)
    if n % 3 == 0:
        return relative_search(n, parameters, bound) | stats
    half = pow(2, -1, n)
    k = -half % n
    bases = []
    for stage, a in enumerate(parameters, 1):
        divisor = gcd(a*a - 3, n)
        if divisor == n:
            return dict(stats, status="ineligible", stage=stage)
        if divisor != 1:
            return dict(stats, status="factor", factor=divisor, stage=stage)
        bases.append(quotient_power(n, k, (a-1, 2), 1))

    boxes = iter(short_boxes(len(bases), bound))
    pending = next(boxes, None)
    spent, cap = 0, 1
    while True:
        allowance = 8*len(bases)*(isqrt(cap-1)+1)
        while pending is not None and (first_relation or spent+pending[2] <= allowance):
            indices, ranges, charge = pending
            selected = [bases[i] for i in indices]
            factor, word = prefix_search(n, k, half, selected, ranges, stats)
            stats["short_prefix_tests"] += 1
            spent += charge
            if factor is not None or (first_relation and word is not None):
                value = (1, 0)
                for base, exponent in zip(selected, word, strict=True):
                    value = multiply(value, signed_power(base, exponent, k, n), k, n)
                certificate = dict(stats, strategy="short-box", word=list(zip((i+1 for i in indices), word)),
                                   relation_gcd=gcd(n, value[0]-1, value[1]))
                if factor is not None:
                    return dict(certificate, status="factor", factor=factor)
                return dict(certificate, status="relation")
            pending = next(boxes, None)
        if first_relation:
            return dict(stats, status="bound-exhausted")

        result = relative_search(n, parameters, cap)
        stats["relative_rounds"] += 1
        stats["prefix_tests"] += result["prefix_tests"]
        stats["list_entries"] += result["list_entries"]
        if result["status"] != "bound-exhausted" or cap == bound:
            return result | stats | dict(strategy="relative", relative_cap=cap)
        cap = min(2*cap, bound)


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
    result = adaptive_search(137549, [3, 13])
    assert result["status"] == "factor" and result["strategy"] == "short-box"
    assert result["word"] == [(1, 7), (2, 1)] and result["relation_gcd"] == 523
    assert result["list_entries"] < relative_search(137549, [3, 13])["list_entries"]
    result = adaptive_search(11*17, [3, 3], first_relation=True)
    assert result["status"] == "relation" and result["word"] == [(1, 1), (2, -1)]
    assert result["relation_gcd"] == 11*17
    result = adaptive_search(11**2*17, [0, 0])
    assert result["status"] == "common-kernel" and result["radices"] == [2, 1]
    assert adaptive_search(187, [3], 1, first_relation=True)["short_prefix_tests"] == 1
    print("Relative-order replay passed rough fixtures, short relations, a third-base split and a common kernel.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?", help="omit to run the self-check")
    parser.add_argument("--bases", type=int, nargs="+", default=[3, 17], metavar="A",
                        help="parameters a in (a + sqrt(3))/(a - sqrt(3))")
    parser.add_argument("--bound", type=int, help="maximum box volume, default floor(sqrt(N))+1")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--adaptive", action="store_true", help="interleave short-word boxes and doubling caps")
    mode.add_argument("--first-relation", action="store_true", help="stop at a short identity or a divisor")
    args = parser.parse_args()
    if args.N is None:
        replay()
    else:
        try:
            if args.adaptive or args.first_relation:
                result = adaptive_search(args.N, args.bases, args.bound, first_relation=args.first_relation)
            else:
                result = relative_search(args.N, args.bases, args.bound)
            print(json.dumps(result, sort_keys=True))
        except ValueError as error:
            parser.error(str(error))
