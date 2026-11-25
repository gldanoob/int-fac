"""Finite closed walks, signed partition kernels and projective p^2 root lifts."""

from fractions import Fraction
from itertools import combinations, product


def partitions(length):
    words = [(0,)]
    for _ in range(1, length):
        words = [w + (j,) for w in words for j in range(max(w) + 2)]
    return words


def graph_stats(row, mark, selected):
    height = max(mark) + 1
    vertices = max(row) + 1 + height
    parents = list(range(vertices))
    edges = {(mark[j], height + row[i]) for j in selected for i in (j, (j+1) % len(row))}

    def root(a):
        while parents[a] != a:
            parents[a] = parents[parents[a]]
            a = parents[a]
        return a

    components = vertices
    for a, b in edges:
        ra, rb = root(a), root(b)
        if ra != rb:
            parents[ra] = rb
            components -= 1
    return components, len(edges) > vertices - components


def check_walks():
    checked = 0
    for k in range(2, 7):
        rows = [r for r in partitions(k) if all(r[j] != r[(j+1) % k] for j in range(k))]
        for row in rows:
            for mark in partitions(k):
                h = max(mark) + 1
                if h == k:
                    continue
                for hits in range(k + 1):
                    for selected in combinations(range(k), hits):
                        components, cyclic = graph_stats(row, mark, selected)
                        allowance = k-h + (h <= k//2)
                        exponent = k-h + components - 2*(k-hits) - int(cyclic)
                        assert exponent <= allowance
                        checked += 1
    return checked


def refines(p, q):
    return all(p[i] != p[j] or q[i] == q[j] for i, j in combinations(range(len(p)), 2))


def check_partition_kernel():
    checked = 0
    for k in range(2, 7):
        parts = sorted(partitions(k), key=lambda w: -len(set(w)))
        for prime in (3, 5, 7, 13):
            coeff = {}
            for q in parts:
                value = Fraction(prime, prime - 1)**(2*(k-len(set(q))))
                coeff[q] = value - sum(c for p, c in coeff.items() if refines(p, q))
                assert sum(c for p, c in coeff.items() if refines(p, q)) == value
                checked += 1
    return checked


def check_lifts():
    count = 0
    for p in (3, 5, 7, 11):
        # f(T)=(T-r)^2*s + (T-r)*v + p*u near a prescribed root.
        for r, slope, intercept in product(range(min(4, p)), range(p), range(p)):
            square = 3
            t = range(p)
            for a, b, c in combinations(t, 3):
                values = []
                for j, digit in enumerate((a, b, c)):
                    denominator = j*p + 1 + (j == 1)
                    numerator = denominator*(r+p*digit) + p*p
                    v = square*(numerator-r*denominator)**2 + slope*denominator*(numerator-r*denominator) + p*intercept*denominator**2
                    assert v % p == 0
                    values.append(v//p * pow(denominator, -2, p) % p)
                assert (values[2] - values[0]) % p == (c-a)*pow(b-a, -1, p)*(values[1]-values[0]) % p
                count += 1
    return count


if __name__ == '__main__':
    print('masked closed walks:', check_walks())
    print('partition inversions:', check_partition_kernel())
    print('three-lift interpolations:', check_lifts())
