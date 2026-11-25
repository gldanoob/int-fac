"""Exact public-character branching counts across all vectors for m <= 3."""

from fractions import Fraction
from itertools import product


def dot(a, b):
    return sum(x*y for x, y in zip(a, b)) % 3


def rows_for(s):
    m = len(s)
    pivot = next(i for i, x in enumerate(s) if x)
    low = tuple(pow(s[pivot], -1, 3) if j == pivot else 0 for j in range(m))
    return (low, *(tuple(((i == j)+(1-s[i])*low[j]) % 3 for j in range(m))
                   for i in range(m) if i != pivot))


def tail(rows, x, y):
    one = all(dot(r, x) == 0 for r in rows)
    dual = all((dot(r, x) == 0) == (dot(r, y) == 0) for r in rows)
    return one, dual


def canonical_rows(vectors):
    return [x for x in vectors if any(x) and next(t for t in x if t) == 1]


for m in range(1, 4):
    vs = list(product(range(3), repeat=m))
    fail = 0
    for s in vs:
        if not any(s):
            fail += len(vs)
            continue
        tests = rows_for(s)
        assert [dot(r, s) for r in tests] == [1]*m
        assert max(sum(x != 0 for x in row) for row in tests) <= 2
        assert len({tuple(dot(row, x) for row in tests) for x in vs}) == 3**m
        for j in range(1, m+1):
            masks = [tail(tests[:j], x, [(si-xi) % 3 for si, xi in zip(s, x)])
                     for x in vs]
            assert sum(one for one, _ in masks) == 3**(m-j)
            assert sum(dual for _, dual in masks) == 3**(m-j)
            assert not any(one and dual for one, dual in masks)
            if j == m:
                fail += sum(one or dual for one, dual in masks)
    assert fail == 3**(m+1)-2

    directions = canonical_rows(vs)
    # Check every fixed prefix of lengths one through three, including dependencies.
    for j in range(1, m+1):
        denominator = 3**(2*m)
        lower = Fraction(1, 3)**j + Fraction(5, 9)**j - Fraction(1, 9)**j
        optimum = min(Fraction(sum(any(tail(tests, x, y))
                                   for x, y in product(vs, repeat=2)), denominator)
                      for tests in product(directions, repeat=j))
        assert optimum == lower
    print(m, "worst failure", Fraction(fail, 3**(2*m)),
          "capped adaptive mean given nonzero s", 2-Fraction(1, 3)**(m-1),
          "known mode", Fraction(3, 2)*(1-Fraction(1, 3)**m),
          "capped fixed-list mean",
          sum(Fraction(1, 3)**j+Fraction(5, 9)**j-Fraction(1, 9)**j for j in range(m)))
