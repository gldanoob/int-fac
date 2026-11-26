"""Find a local divisor or recover global order relations from a signed exponent box."""

import argparse
import json
from itertools import groupby, product
from math import gcd, isqrt, prod
from operator import itemgetter
from pathlib import Path
from runpy import run_path

from sage.all import QQ, ZZ, VectorSpace, matrix

HERE = Path(__file__).resolve().parent
COLLISION = run_path(str(HERE / "cogentic-unit-collision-search.py"))["sorted_local_collision"]
POOLED_SPLIT = run_path(str(HERE / "cogentic-pooled-order-certificates.py"))["pooled_split"]


def word_value(n, bases, word):
    return prod(pow(base, int(exponent), n) for base, exponent in zip(bases, word, strict=True)) % n


def rectangles(bounds):
    return interval_rectangles([range(-bound, bound+1) for bound in bounds])


def interval_rectangles(ranges):
    """Split nonempty unit-step ranges into lists of O(sqrt(volume)) words."""
    widths = [len(entries) for entries in ranges]
    target = 1 + isqrt(prod(widths) - 1)
    prefix = 1
    for pivot, width in enumerate(widths):
        if prefix * width >= target:
            break
        prefix *= width
    radix = (target + prefix - 1) // prefix
    full, extra = divmod(width, radix)
    first = ranges[pivot].start
    for start, stop, size in [(0, full, radix), (full, full+1, extra)]:
        if size:
            left = ranges[:pivot] + [range(first, first+size)] + [(0,)] * (len(ranges)-pivot-1)
            right = [(0,)] * pivot + [range(start*radix, stop*radix, radix)] + ranges[pivot+1:]
            yield left, right


def buckets(n, bases, ranges):
    powers = [[(exponent, pow(base, exponent, n)) for exponent in entries]
              for base, entries in zip(bases, ranges, strict=True)]
    entries = []
    for choices in product(*powers):
        exponents, values = zip(*choices)
        entries.append((prod(values) % n, exponents))
    entries.sort(key=itemgetter(0))
    return [(residue, [word for _, word in group])
            for residue, group in groupby(entries, key=itemgetter(0))]


def add_words(left, right):
    return tuple(a+b for a, b in zip(left, right, strict=True))


def box_relations(n, bases, bounds, scalar):
    """Return a proper divisor or a rational basis of all exact relations in the box."""
    if n < 3 or n % 2 == 0 or scalar < 1 or not bases or len(bases) != len(bounds):
        raise ValueError("require an odd modulus, a positive scalar, and one bound per base")
    if any(bound < 0 for bound in bounds):
        raise ValueError("negative exponent bound")
    for base in bases:
        divisor = gcd(base, n)
        if 1 < divisor < n:
            return dict(status="base-gcd", factor=divisor, cofactor=n//divisor)
    if any(base % n == 0 for base in bases):
        raise ValueError("a base vanishes modulo the whole modulus")

    powered = [pow(base, scalar, n) for base in bases]
    inverse = [pow(residue, -1, n) for residue in powered]
    ambient = VectorSpace(QQ, len(bases))
    space = ambient.zero_subspace()
    independent = []
    matched_words = 0
    for left_ranges, right_ranges in rectangles(bounds):
        left = buckets(n, powered, left_ranges)
        right = buckets(n, inverse, right_ranges)
        hit = COLLISION(n, [(residue, i) for i, (residue, _) in enumerate(left)],
                        [(residue, i) for i, (residue, _) in enumerate(right)])
        if hit is not None:
            word = add_words(left[hit["left_index"]][1][0], right[hit["right_index"]][1][0])
            divisor = hit["factor"]
            assert gcd(word_value(n, powered, word)-1, n) == divisor
            return dict(status="local-relation", word=word, factor=divisor, cofactor=n//divisor)
        cursor = 0
        for residue, left_words in left:
            while cursor < len(right) and right[cursor][0] < residue:
                cursor += 1
            if cursor == len(right):
                break
            if right[cursor][0] != residue:
                continue
            right_words = right[cursor][1]
            matched_words += len(left_words)*len(right_words)
            if space.dimension() == len(bases):
                continue
            # A spanning tree of this equality bucket generates every pair sum.
            for side, fixed in [(left_words, right_words[0]), (right_words[1:], left_words[0])]:
                for item in side:
                    word = add_words(item, fixed)
                    if ambient(word) not in space:
                        independent.append(word)
                        space = ambient.subspace(independent)

    certificates = []
    if independent:
        diagonal, transform, _ = matrix(ZZ, independent).transpose().smith_form()
        saturation = transform.inverse()
        for j in range(len(independent)):
            word = tuple(map(int, saturation.column(j)))
            base = word_value(n, bases, word)
            exponent = scalar * abs(int(diagonal[j, j]))
            assert exponent > 0 and pow(base, exponent, n) == 1
            certificates.append(dict(word=word, base=base, exponent=exponent))
        complement = [tuple(map(int, saturation.column(j)))
                      for j in range(len(independent), len(bases))]
    else:
        complement = [tuple(int(i == j) for i in range(len(bases))) for j in range(len(bases))]
    result = dict(status="box-complete", relations=independent, rank=len(independent),
                  box_matches=matched_words, certificates=certificates, complement=complement)
    divisor = POOLED_SPLIT(n, [(c["base"], c["exponent"]) for c in certificates])
    if divisor is not None:
        result.update(status="saturated-split", factor=divisor, cofactor=n//divisor)
    return result


def refined_search(n, bases, bounds, scalar, refine_bound):
    """Repeat the search on a unimodular complement after a positive-rank round."""
    if refine_bound < 0:
        raise ValueError("negative refinement bound")
    rounds = []
    certified = []
    while True:
        result = box_relations(n, bases, bounds, scalar)
        rounds.append(dict(bases=bases, bounds=bounds, scalar=scalar, **result))
        if "factor" in result:
            return dict(status=result["status"], factor=result["factor"],
                        cofactor=result["cofactor"], rounds=rounds)
        certified.extend((c["base"], c["exponent"]) for c in result["certificates"])
        if len(rounds) > 1 and result["rank"]:
            divisor = POOLED_SPLIT(n, certified)
            if divisor is not None:
                return dict(status="pooled-split", factor=divisor, cofactor=n//divisor, rounds=rounds)
        if not result["rank"] or not result["complement"]:
            return dict(status="box-complete", rounds=rounds, rank=len(certified))
        # Smith invariants divide the last one, so all dropped directions now vanish.
        scalar = result["certificates"][-1]["exponent"]
        bases = [word_value(n, bases, word) for word in result["complement"]]
        bounds = [refine_bound] * len(bases)


def replay():
    for bounds in [(0,), (2,), (1, 2), (0, 1, 6), (2, 0, 3), (0, 0, 0), (13, 2, 1)]:
        words = [add_words(u, v) for left, right in rectangles(bounds)
                 for u in product(*left) for v in product(*right)]
        assert len(words) == len(set(words)) == prod(2*b+1 for b in bounds)
        assert all(all(abs(e) <= b for e, b in zip(word, bounds, strict=True)) for word in words)

    trials = 0
    for n in (9, 15, 25, 35, 49, 65, 77, 91, 101):
        bases = [a for a in range(2, n) if gcd(a, n) == 1][:3]
        for bounds in [(0, 0, 0), (1, 2, 0), (2, 1, 1)]:
            for scalar in (1, 2, 12, 1 << n.bit_length()):
                exact, local = [], set()
                for word in product(*(range(-b, b+1) for b in bounds)):
                    common = gcd(pow(word_value(n, bases, word), scalar, n)-1, n)
                    if common == n:
                        exact.append(word)
                    elif common > 1:
                        local.add(common)
                result = box_relations(n, bases, bounds, scalar)
                if local:
                    assert result["status"] == "local-relation" and result["factor"] in local
                else:
                    assert result["box_matches"] == len(exact)
                    reference = matrix(QQ, exact).row_space()
                    assert result["rank"] == reference.dimension()
                    assert all(reference.ambient_vector_space()(word) in reference for word in result["relations"])
                    sat = matrix(ZZ, len(result["certificates"]), len(bounds),
                                 [a for c in result["certificates"] for a in c["word"]])
                    assert sat.row_space().index_in_saturation() == 1
                trials += 1

    assert box_relations(15, [15, 6], [1, 1], 1)["factor"] == 3
    assert refined_search(101, [2], [1], 1, 3)["rank"] == 0
    refined = refined_search(91, [5, 9, 9], [1, 1, 2], 1, 2)
    assert [(r["scalar"], r.get("rank")) for r in refined["rounds"]] == [(1, 2), (3, None)]
    assert refined["factor"] == 7
    pooled = refined_search(481, [31, 45], [4, 1], 1, 3)
    assert [r["status"] for r in pooled["rounds"]] == ["box-complete", "box-complete"]
    assert pooled["status"] == "pooled-split" and pooled["factor"] == 37
    n, bases, scalar = 679, [2, 5, 11], 1024
    assert all(gcd(pow(a, scalar, n)-1, n) == 1 for a in bases)
    result = box_relations(n, bases, [1, 1, 1], scalar)
    assert result["rank"] == 3 and result["status"] == "saturated-split" and n % result["factor"] == 0
    n, bases, scalar = 91, [2, 17], 128
    assert all(gcd(pow(a, scalar*k, n)-1, n) == 1 for a in bases for k in (1, 2))
    result = box_relations(n, bases, [2, 2], scalar)
    assert result["rank"] == 2 and result["status"] == "saturated-split" and n % result["factor"] == 0
    n, bases = 26182823, [15759937, 23615508, 3958576, 19144294]
    assert all(gcd(pow(base, j, n)-1, n) == 1 for base in bases for j in (1, 2, 3))
    assert all(gcd(word_value(n, bases, word)-1, n) in (1, n)
               for word in product(range(-3, 4), repeat=4))
    outside_root = word_value(n, bases, (4, 1, 2, -1))
    assert outside_root**2 % n == 1 and gcd(outside_root-1, n) == 9341
    result = box_relations(n, bases, [3]*4, 1)
    assert result["rank"] == 3 and result["box_matches"] == 7
    assert result["status"] == "saturated-split" and result["factor"] in (2803, 9341)
    print(f"{trials} exponent boxes matched direct enumeration.")
    print("Verified mixed-relation splits at 679 and 26182823, refinement at 91, and pooling across rounds at 481.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", nargs="?", type=int)
    parser.add_argument("--bases", nargs="+", type=int, default=[2, 3])
    parser.add_argument("--bounds", nargs="+", type=int, default=[16, 16])
    parser.add_argument("--scalar", type=int, help="default: odd part of N-1 times 2^bitlength(N)")
    parser.add_argument("--refine-bound", type=int, help="search remaining Smith coordinates at this radius")
    args = parser.parse_args()
    if args.n is None:
        replay()
    elif args.n >= 2 and args.n % 2 == 0:
        print(json.dumps(dict(status="prime") if args.n == 2 else dict(status="even", factor=2, cofactor=args.n//2)))
    else:
        if args.n < 3:
            parser.error("require N >= 2")
        scalar = args.scalar
        if scalar is None:
            previous = args.n - 1
            scalar = (previous // (previous & -previous)) << args.n.bit_length()
        try:
            if args.refine_bound is None:
                result = box_relations(args.n, args.bases, args.bounds, scalar)
            else:
                result = refined_search(args.n, args.bases, args.bounds, scalar, args.refine_bound)
            print(json.dumps(result))
        except ValueError as error:
            parser.error(str(error))
