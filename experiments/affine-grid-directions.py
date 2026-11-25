"""Enumerate plane boxes and cheapest-axis choices over small prime fields."""
from fractions import Fraction
from itertools import combinations, product
from math import prod


def dot(row, point, q):
    return sum(a * x for a, x in zip(row, point)) % q


def groups(rows, k):
    parts = [{i} for i in range(k)]
    for row in rows:
        support = {j for j, a in enumerate(row) if a}
        touched = [part for part in parts if part & support]
        parts = [part for part in parts if not part & support] + [set.union(*touched)]
    return sorted(parts, key=min)


def box_checks(rows, q):
    k = len(rows[0])
    points = list(product(range(q), repeat=k))
    parts = groups(rows, k)
    irregular = regular = nontrivial = 0
    bad_hyperplanes = []
    for mask in range(1 << k):
        indices = {j for j in range(k) if mask >> j & 1}
        for row in rows:
            left = tuple(a if j in indices else 0 for j, a in enumerate(row))
            right = tuple(a - b for a, b in zip(row, left))
            if any(left) and any(right):
                bad_hyperplanes.extend((left, right))
                break
    for xi in points[1:]:
        # Checking only increments in the basis box is exact because all basis
        # projections are selected; literal enumeration below does not assume it.
        choices = [set((0, dot(row, xi, q))) for row in rows]
        actual = {w for w in points if all(dot(row, w, q) in opt for row, opt in zip(rows, choices))}
        expected = {tuple(x if any(j in part and mask >> i & 1 for i, part in enumerate(parts)) else 0
                          for j, x in enumerate(xi)) for mask in range(1 << len(parts))}
        assert expected <= actual
        if actual == expected and all(xi):
            regular += 1
            nontrivial += len(actual) > 2
            for a in actual:
                b = tuple((x - y) % q for x, y in zip(xi, a))
                assert b in actual
                assert all({dot(row, a, q), dot(row, b, q)} == opt for row, opt in zip(rows, choices))
        else:
            irregular += 1
            assert not all(xi) or any(dot(h, xi, q) == 0 for h in bad_hyperplanes)
    assert irregular <= (k + 2 ** (k + 1)) * q ** (k - 1)
    for row in rows:
        assert sum(dot(row, xi, q) == 0 for xi in points[1:]) == q ** (k - 1) - 1
    return regular, irregular, nontrivial


def rounded_game():
    # One piece vector per possible preferred direction. Use exact enumeration
    # to distinguish choosing an axis per box from choosing it after all boxes.
    checked = 0
    for d in (2, 3, 4):
        for boxes in range(1, 8):
            vectors = [tuple(int(a != j) for a in range(d)) for j in range(d)]
            worst = max(min(sum(vectors[j][a] for j in choices) for a in range(d))
                        for choices in product(range(d), repeat=boxes))
            assert worst == boxes - (boxes + d - 1) // d
            assert Fraction(boxes * (d - 1), d) - 1 < worst <= Fraction(boxes * (d - 1), d)
            checked += 1
    return checked


def polynomial_boxes(k, q, polynomials):
    # A polynomial is a list of monomials, each given by its variable indices.
    supports = [{i for term in polynomial for i in term} for polynomial in polynomials]
    rows = [tuple(int(j in support) for j in range(k)) for support in supports]
    parts = groups(rows, k)
    degree = max(len(term) for poly in polynomials for term in poly)
    vertices = list(product(range(q), repeat=k))
    labels = {v: v + tuple(sum(prod(v[i] for i in term) for term in poly) % q
                          for poly in polynomials) for v in vertices}
    regular = irregular = larger = 0
    collapsed = [0] * len(polynomials)
    for u, v in combinations(vertices, 2):
        choices = [set(pair) for pair in zip(labels[u], labels[v])]
        actual = {w for w in vertices if all(x in s for x, s in zip(labels[w], choices))}
        expected = {tuple(v[j] if j in switched else u[j] for j in range(k))
                    for bits in product((False, True), repeat=len(parts))
                    for switched in [set().union(*(part for part, bit in zip(parts, bits) if bit))]}
        assert expected <= actual
        for a in range(len(collapsed)):
            collapsed[a] += labels[u][k + a] == labels[v][k + a]
        if all(x != y for x, y in zip(u, v)) and actual == expected:
            regular += 1
            larger += len(actual) > 2
            for w in expected:
                opposite = tuple(y if z == x else x for x, y, z in zip(u, v, w))
                assert [set(pair) for pair in zip(labels[w], labels[opposite])] == choices
        else:
            irregular += 1
    assert all(2 * n + len(vertices) <= degree * q ** (2 * k - 1) for n in collapsed)
    assert 2 * irregular <= (k + 2 ** (k + 1) * degree) * q ** (2 * k - 1)
    return regular, irregular, larger


if __name__ == "__main__":
    fixtures = [
        (2, 7, []), (2, 11, [(1, 1)]), (3, 7, [(1, 2, 0)]),
        (3, 7, [(1, 2, 0), (0, 1, 1)]), (3, 5, [(1, 1, 1)]),
        (4, 3, [(1, 1, 0, 0), (0, 0, 1, 1)]), (4, 5, [(1, 1, 1, 1)]),
    ]
    totals = [0, 0, 0]
    for k, q, extra in fixtures:
        basis = [tuple(int(i == j) for j in range(k)) for i in range(k)]
        counts = box_checks(basis + extra, q)
        if k == 2 and extra:
            assert counts[2] == 0
        totals = [x + y for x, y in zip(totals, counts)]
    print("regular differences, irregular differences, nontrivial regular boxes", *totals)
    print("adaptive cheapest-axis games", rounded_game())
    nonlinear = [(2, 7, [[(0, 1)]]), (2, 7, [[(0, 0)], [(1, 1)]]),
                 (3, 3, [[(0, 1), (1,)]]), (3, 5, [[(0, 1)], [(1, 2), (2,)]])]
    results = [polynomial_boxes(*case) for case in nonlinear]
    print("polynomial regular pairs, irregular pairs, nontrivial regular boxes",
          *(sum(values) for values in zip(*results)))
