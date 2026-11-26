"""Seeded relation and pivot trials on the engineered N=15 two-field fixture.

The fields, common root and target prime are fixed. This exercises the
extraction pipeline and reports its bounded misses on this fixture.
"""

from collections import Counter
from pathlib import Path
from random import Random
from runpy import run_path

from sage.all import QQ, ZZ, lcm, matrix


HERE = Path(__file__).parent
EXACT = run_path(str(HERE / "cogentic-real-extractor-sage.py"))
pivot_lists = run_path(str(HERE / "cogentic-randomized-extraction.py"))["pivot_lists"]
GRID = [(a, b) for b in range(1, 13) for a in range(-35, 36)]
PIVOT_PRIMES = (2, 3, 5, 7, 11, 13)


def proposed_kernel(incidence, prime):
    columns = [list(map(int, column)) for column in incidence.columns()]
    rows, pivots = pivot_lists(columns, prime)
    free = [j for j in range(incidence.ncols()) if j not in pivots]
    minor = incidence.matrix_from_rows_and_columns(rows, pivots).change_ring(QQ)
    target = incidence.matrix_from_rows_and_columns(rows, free)
    solution = minor.solve_right(-target)
    relations = []
    for free_index, column in zip(free, solution.columns(), strict=True):
        scale = lcm(entry.denominator() for entry in column)
        relation = [0]*incidence.ncols()
        for index, entry in zip(pivots, column, strict=True):
            relation[index] = scale*entry
        relation[free_index] = scale
        relations.append(relation)
    kernel = matrix(ZZ, len(free), incidence.ncols(), relations)
    return kernel if incidence * kernel.transpose() == 0 else None


def trial(fixture, seed, budget):
    n, m, ell, fields = fixture
    rng = Random(seed)
    marks, incidence = EXACT["collect_marks"](n, m, ell, fields, rng.sample(GRID, budget))
    prime = rng.choice(PIVOT_PRIMES)
    kernel = proposed_kernel(incidence, prime)
    if kernel is None:
        return "pivot drop", len(marks), prime, None
    result = EXACT["split_from_relations"](n, m, ell, fields, marks, incidence, kernel)
    if result is None:
        return "insufficient unit rank", len(marks), prime, None
    exponent, divisor, _, _ = result
    assert pow(ell, exponent, n) == 1
    if divisor is None:
        return "no proper gcd", len(marks), prime, exponent
    assert 1 < divisor < n and n % divisor == 0
    return "split", len(marks), prime, (exponent, divisor)


def replay():
    fixture = EXACT["fixture"]()
    counts = Counter()
    for seed in range(12):
        status, marks, prime, result = trial(fixture, seed, 820)
        counts[status] += 1
        print(f"seed={seed} marks={marks} pivot={prime} {status} {result}")
    assert counts["split"] and counts["split"] < 12
    print(dict(counts))


if __name__ == "__main__":
    replay()
