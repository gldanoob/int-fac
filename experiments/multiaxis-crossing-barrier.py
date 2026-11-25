"""Finite-field controls for exact cube ranks, interpolation and grid distances."""
from collections import Counter
from itertools import combinations, product
from math import comb, factorial, isqrt, prod
from pathlib import Path
from runpy import run_path

HERE = Path(__file__).resolve().parent
rank = run_path(str(HERE / "modular-product-crossings.py"))["sparse_rank"]
integer_root = run_path(str(HERE / "euclidean-crossing-barrier.py"))["integer_root"]


def pieces(d, labels, blocks, prime):
    n = 1 << d
    opposite = n - 1
    entries = [{} for _ in range(4)]
    # The first two pieces carry different matchings. They produce cancellation
    # outside the crossing's support even when the target is a direct sum.
    for color in range(blocks):
        for step, tensor in ((1, entries[0]), (n // 2, entries[1]), (opposite, entries[3])):
            left = [j for j in range(n) if j < j ^ step]
            for word in product(range(labels), repeat=len(left)):
                coord = [0] * n
                for j, value in zip(left, word):
                    coord[j] = coord[j ^ step] = color * labels + value
                tensor[tuple(coord)] = 1
    coeffs = set().union(*entries)
    for key in coeffs:
        residual = (entries[3].get(key, 0) - entries[0].get(key, 0) - entries[1].get(key, 0)) % prime
        if residual:
            entries[2][key] = residual
        assert sum(t.get(key, 0) for t in entries[:3]) % prime == entries[3].get(key, 0)
    return entries


def axis_ranks(tensor, d, prime):
    ranks = []
    for axis in range(d):
        rows = {}
        for key, value in tensor.items():
            row = tuple(a for j, a in enumerate(key) if not j & (1 << axis))
            column = tuple(a for j, a in enumerate(key) if j & (1 << axis))
            rows.setdefault(row, {})[column] = value
        ranks.append(rank(rows.values(), prime))
    return ranks


def check_rank_scores():
    controls = 0
    scale = 10000
    for d, labels, blocks in ((2, 2, 2), (2, 3, 2), (3, 2, 1), (3, 2, 2), (4, 2, 1)):
        m = 2 ** (d - 1)
        for prime in (2, 3, 5):
            tensors = pieces(d, labels, blocks, prime)
            ranks = [axis_ranks(t, d, prime) for t in tensors]
            assert ranks[-1] == [blocks * labels ** m] * d
            for weights in ((1,) * d, tuple(range(1, d + 1))):
                degree = sum(weights)
                # Integer lower bound on the score and upper bound on the RHS.
                floored = sum(integer_root(scale ** degree * prod(r ** w for r, w in zip(rs, weights)),
                                           degree) for rs in ranks[:-1])
                squared = sum(a * a for a in weights)
                denominator = 200
                numerator = isqrt(squared * denominator ** 2)
                numerator += numerator ** 2 < squared * denominator ** 2
                assert floored ** (degree * denominator) >= (
                    (blocks * scale) ** (degree * denominator) * labels ** (m * numerator))
                controls += 1
    return controls


def interpolation():
    # Leading order two with a nonzero cubic perturbation. Interpolate the
    # tensor square directly, including zero entries and cancellation.
    p = 11
    d = 3
    A, B, C, target = pieces(d, 2, 1, p)
    keys = list(product(range(2), repeat=2 ** d))
    n = 6
    coef = []
    for t in range(n + 1):
        poly = [1]
        for j in range(n + 1):
            if j == t:
                continue
            out = [0] * (len(poly) + 1)
            for r, x in enumerate(poly):
                out[r] -= j * x
                out[r + 1] += x
            poly = out
        denominator = (-1) ** (n - t) * factorial(t) * factorial(n - t)
        coef.append(poly[4] * pow(denominator, -1, p) % p)
    for j in range(7):
        assert sum(w * t ** j for t, w in enumerate(coef)) % p == (j == 4)
    values = []
    for t in range(7):
        row = {}
        for v in keys:
            a, b, c = (T.get(v, 0) for T in (A, B, C))
            terms = [a + t * b + t ** 2 * a, -a - t * b + t ** 2 * b, t ** 2 * c + t ** 3 * a]
            row[v] = sum(terms) % p
        values.append(row)
    for x, y in product(keys, repeat=2):
        recovered = sum(w * v[x] * v[y] for w, v in zip(coef, values)) % p
        assert recovered == target.get(x, 0) * target.get(y, 0)
    return len(keys) ** 2


def grid_distances():
    checked = 0
    for d in range(2, 6):
        for g in (2, 3, 4):
            sites = list(product(range(g), repeat=d))
            counts = Counter(sum(x != y for x, y in zip(left, right))
                             for left, right in combinations(sites, 2))
            for distance in range(1, d + 1):
                assert counts[distance] * 2 == len(sites) * comb(d, distance) * (g - 1) ** distance
            checked += sum(counts.values())
    assert (3 * 25 - 9 * 8) * 256 == 3 * 256
    return checked


if __name__ == "__main__":
    print("weighted finite-field rank inequalities", check_rank_scores())
    print("leading-coefficient tensor entries", interpolation())
    print("unordered grid-edge distances", grid_distances())
