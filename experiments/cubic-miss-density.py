"""Exact one-prime miss densities from cubic-miss-fields.gp records on stdin."""

from ast import literal_eval
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from math import isqrt, prod
from pathlib import Path
from runpy import run_path
import sys

profiles = run_path(str(Path(__file__).with_name("cubic-resolvent-profiles.py")))
ANCHOR = frozenset({-1, 3})
# Reduced numerator and power of 3, ordered by p = 1, 2 mod 3.
EXPECTED = (
    ((8, 3), (8, 3)),
    ((126976, 18), (45056, 17)),
    ((2626070511616000, 56), (723433553920, 45)),
    ((358406310451080095963545600000, 105), (390887254545831821312, 83)),
    ((3751836768747418575392271723396813789269036300763136000000000, 210),
     (928655478805204386109530099619888571088896000, 171)),
)


def factor(n):
    powers = {-1: 1} if n < 0 else {}
    n = abs(n)
    p = 2
    while p * p <= n:
        while n % p == 0:
            powers[p] = powers.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        powers[n] = 1
    return powers


def cubic_rank(squareclass, group):
    if squareclass == ANCHOR:
        exponents = [factor(m) for _, m in group]
        primes = sorted(set().union(*(row.keys() for row in exponents)))
        pivots = {}
        for row in exponents:
            v = [row.get(p, 0) % 3 for p in primes]
            for j, pivot in sorted(pivots.items()):
                v = [(a - v[j]*b) % 3 for a, b in zip(v, pivot, strict=True)]
            if any(v):
                j = next(i for i, a in enumerate(v) if a)
                pivots[j] = [a*v[j] % 3 for a in v]
        return len(pivots)
    if prod(squareclass) == -51:
        assert {d for d, _ in group} <= {-204, -459, -1836}
        return min(len(group), 2)
    assert len(group) <= 2
    return len(group)


def sum_products(_, inputs):
    return sum(prod(bucket) for bucket in inputs), ()


def field_groups(fields):
    groups = defaultdict(list)
    for d, m in fields:
        groups[frozenset(p for p, e in factor(d).items() if e % 2)].append((d, m))
    cyclic = [isqrt(d) for d, _ in groups.pop(frozenset(), [])]
    assert len(set(cyclic)) == len(cyclic) and set(cyclic) <= {7, 9, 13, 19}
    return groups, len(cyclic)


def density(fields, residue):
    groups, cyclic_count = field_groups(fields)
    terms, rank = [], 0
    for D, group in groups.items():
        w = cubic_rank(D, group)
        rank += w
        scope = tuple(sorted(D ^ ANCHOR if 3 in D else D))
        shift = (residue == 2) * int(3 in D)
        terms.append((scope, {bits: (3**w if (sum(bits) + shift) % 2 else 1)
                              for bits in product((0, 1), repeat=len(scope))}))
    signs = {p for scope, _ in terms for p in scope}
    denominator = 2**len(signs) * 3**(rank + cyclic_count)
    numerators, _ = profiles["eliminate"](terms, signs, sum_products)
    return Fraction(prod(numerators), denominator)


def positive_collision(D, group, rank):
    """Count pairs of positive-sign cubic vectors with the same root pattern."""
    if len(group) == rank:
        return 5**rank
    if D == ANCHOR:
        rows = [factor(m) for _, m in group]
        primes = sorted(set().union(*(row.keys() for row in rows)))
        forms = [[row.get(p, 0) for p in primes] for row in rows]
    else:
        assert prod(D) == -51 and rank == 2 and len(group) == 3
        forms = [(1, 0), (0, 1), (1, 1)]
    counts = Counter()
    columns = len(forms[0])
    for vector in product(range(3), repeat=columns):
        pattern = tuple(sum(a*b for a, b in zip(row, vector, strict=True)) % 3 != 0
                        for row in forms)
        counts[pattern] += 1
    numerator, remainder = divmod(sum(n*n for n in counts.values()), 9**(columns-rank))
    assert remainder == 0
    return numerator


def collision_density(fields, residues):
    groups, cyclic_count = field_groups(fields)
    terms, rank = [], 0
    for D, group in groups.items():
        w = cubic_rank(D, group)
        rank += w
        base = sorted(D ^ ANCHOR if 3 in D else D)
        scope = tuple(2*p+j for p in base for j in (0, 1))
        # Negative quadratic sign forces every cubic in the block to be reducible.
        weight = (positive_collision(D, group, w), 3**w, 9**w)
        table = {}
        for bits in product((0, 1), repeat=len(scope)):
            negatives = sum((sum(bits[j::2]) + (residues[j] == 2 and 3 in D)) % 2
                            for j in (0, 1))
            table[bits] = weight[negatives]
        terms.append((scope, table))
    signs = {v for scope, _ in terms for v in scope}
    numerators, _ = profiles["eliminate"](terms, signs, sum_products)
    return Fraction(prod(numerators)*5**cyclic_count, 2**len(signs)*9**(rank+cyclic_count))


def small_collision_walsh(fields):
    """Independent Walsh/Parseval check for heights one and two."""
    groups, cyclic = field_groups(fields)
    assert all(len(group) == 1 for group in groups.values())
    classes = list(groups)
    atoms = sorted(set.union(set(ANCHOR), *map(set, classes)))
    masks = [sum(1 << atoms.index(p) for p in D) for D in classes]
    anchor = sum(1 << atoms.index(p) for p in ANCHOR)
    size = 1 << len(classes)
    products = [0]*size
    for j in range(1, size):
        bit = j & -j
        products[j] = products[j ^ bit] ^ masks[bit.bit_length()-1]
    transforms = []
    for sign in (1, -1):
        values = [(-2)**j.bit_count() * (1 if d == 0 else sign if d == anchor else 0)
                  for j, d in enumerate(products)]
        for i in range(len(classes)):
            bit = 1 << i
            for j in range(size):
                if j & bit:
                    values[j] += values[j ^ bit]
        transforms.append(values)
    powers = [9**i for i in range(len(classes)+1)]
    result = []
    for a, b in ((0, 0), (0, 1), (1, 1)):
        total = sum(transforms[a][j] * transforms[b][j] * powers[len(classes)-j.bit_count()]
                    for j in range(size))
        result.append(Fraction(total * 5**cyclic, size * 9**len(fields)))
    return result


def main():
    if not __debug__:
        raise RuntimeError("Run without -O so certificate checks are enabled")
    records = [literal_eval(line) for line in sys.stdin]
    assert records[0] == [0, -51, 2, [2, 3, 6]]
    records = records[1:]
    fields = defaultdict(list)
    brute = {}
    for tag, *row in records:
        if tag == -1:
            H, residue, n, d = row
            brute[H, residue] = Fraction(n, d)
        else:
            assert 1 <= tag <= 5 and len(row) == 2
            fields[tag].append(row)
    if brute:
        assert set(brute) == set(product((1, 2), repeat=2))
    for H, count in enumerate((3, 18, 56, 106, 213), start=1):
        assert len(fields[H]) == count
        for residue, (n, power) in enumerate(EXPECTED[H - 1], start=1):
            expected = Fraction(n, 3**power)
            assert density(fields[H], residue) == expected
            assert brute.get((H, residue), expected) == expected
            print(f"H={H} p mod 3={residue}: {n}/3^{power} = {float(expected):.12g}")
        collisions = [collision_density(fields[H], pair) for pair in ((1, 1), (1, 2), (2, 2))]
        if brute and H <= 2:
            assert small_collision_walsh(fields[H]) == collisions
        if H == 1:
            assert collisions == [Fraction(125, 729)]*3
        print(f"H={H} both orders, branch pairs 11/12/22: "
              + " ".join(f"{float(x):.12g}" for x in collisions))
    if brute:
        print("Independent CRT and Walsh checks agree at H=1 and H=2.")


if __name__ == "__main__":
    main()
