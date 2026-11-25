"""Exact entry moments for incidence Grams with a hidden signed kernel."""

from fractions import Fraction
from itertools import combinations
from math import comb


def check_graphs():
    graphs = rows = 0
    for half in range(2, 13):
        n = 2 * half
        mean = Fraction(1, n - 1)
        for degree in range(1, half + 1):
            edges = {(i, half + (i + j) % half) for i in range(half) for j in range(degree)}
            assert all((i < half) != (j < half) for i, j in edges)
            for i in range(n):
                row = [Fraction(tuple(sorted((i, j))) in edges, degree) for j in range(n) if i != j]
                assert sum(row) == 1
                assert sum((v - mean) ** 2 for v in row) == Fraction(1, degree) - mean
                rows += 1
            graphs += 1
    return graphs, rows


def check_hypergraphs():
    hypergraphs = pairs = 0
    for half in range(2, 7):
        n = 2 * half
        for k in range(1, half):
            columns = [set(x + y) for x in combinations(range(half), k)
                       for y in combinations(range(half, n), k)]
            degree = comb(half - 1, k - 1) * comb(half, k)
            entries = []
            for i, j in combinations(range(n), 2):
                value = Fraction(sum(i in c and j in c for c in columns), degree)
                assert value == (Fraction(k - 1, half - 1) if i // half == j // half else Fraction(k, half))
                entries.append(value)
                pairs += 1
            mean = Fraction(2 * k - 1, n - 1)
            variance = Fraction(half * (half - 1), (n - 1) ** 2) * Fraction(half - k, half * (half - 1)) ** 2
            assert sum(entries) / len(entries) == mean
            assert sum((v - mean) ** 2 for v in entries) / len(entries) == variance
            hypergraphs += 1
    return hypergraphs, pairs


if __name__ == '__main__':
    print('regular graphs, rows, balanced hypergraphs, pairs:', *check_graphs(), *check_hypergraphs())
