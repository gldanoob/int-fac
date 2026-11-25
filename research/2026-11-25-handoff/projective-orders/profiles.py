"""Exact augmentation-module norm fibers for fixed Frobenius cycle types."""

from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import lcm


def cycles(sigma):
    seen = set()
    lengths = []
    for i in range(len(sigma)):
        if i in seen:
            continue
        n = 0
        while i not in seen:
            seen.add(i)
            n += 1
            i = sigma[i]
        lengths.append(n)
    return tuple(sorted(lengths))


def exact_fiber(sigma):
    """Enumerate norm fibers of the permutation on even-parity bit vectors."""
    k = len(sigma)
    lengths = cycles(sigma)
    order = lcm(*lengths)
    norm_columns = []
    for i in range(k):
        column = 0
        for _ in range(order):
            column ^= 1 << i
            i = sigma[i]
        norm_columns.append(column)
    norm = Counter()
    for x in range(1 << k):
        if x.bit_count() % 2:
            continue
        value = 0
        for i, column in enumerate(norm_columns):
            if x & (1 << i):
                value ^= column
        norm[value] += 1
    rank = len(norm).bit_length()-1
    assert len(norm) == 1 << rank and set(norm.values()) == {1 << (k-1-rank)}
    two_part = order & -order
    expected = (len(lengths)-1 if order % 2 else
                sum(v & -v == two_part for v in lengths))
    assert rank == expected
    return rank, Fraction(norm[0], 1 << (k-1))


def cyclic(k):
    return [tuple((i+d) % k for i in range(k)) for d in range(k)]


for name, family in [("C3", cyclic(3)), ("S3", list(permutations(range(3)))),
                     ("C5", cyclic(5)), ("S5", list(permutations(range(5))))]:
    classes = Counter((cycles(sigma), *exact_fiber(sigma)) for sigma in family)
    for (shape, rank, probability), count in sorted(classes.items()):
        print(name, shape, 'elements', count, 'rank', rank,
              'square probabilities u=1,2,3', *(str(probability**u) for u in (1, 2, 3)))
