"""Check integral projective evaluation lattices, including primes at infinity."""

from itertools import combinations, permutations
from math import exp, gcd, pi, prod, sqrt


def determinant(rows):
    n = len(rows)
    return sum(
        (-1) ** sum(i > j for k, i in enumerate(order) for j in order[k + 1:])
        * prod(row[j] for row, j in zip(rows, order))
        for order in permutations(range(n))
    )


def evaluation(a, b, n):
    return [a**j * b**(n-j) for j in range(n+1)]


def row_image_index(rows):
    rank = len(rows)
    index = 0
    for cols in combinations(range(len(rows[0])), rank):
        index = gcd(index, determinant([[r[j] for j in cols] for r in rows]))
    return index


def check_conditional_rows():
    # Prime-row constraints are represented exactly by a separate p-slack column.
    points = ((1, 0), (0, 1), (1, 1), (1, 2), (2, 3), (3, 5), (3, 7))
    prescriptions = (((2, 0),), ((3, 2),), ((2, 1), (3, 1)), ((3, 0), (5, 3)))
    checks = 0
    for rows in prescriptions:
        constraints = [evaluation(r, 1, 2) + [p if i == j else 0 for j in range(len(rows))]
                       for i, (p, r) in enumerate(rows)]
        assert row_image_index(constraints) == 1
        for first, second in permutations(points, 2):
            previous = constraints + [evaluation(*first, 2) + [0] * len(rows)]
            index1 = row_image_index(previous)
            hits1 = {p for p, r in rows if (first[0] - first[1] * r) % p == 0}
            hits2 = {p for p, r in rows if (second[0] - second[1] * r) % p == 0}
            assert index1 == prod(hits1)
            index2 = row_image_index(previous + [evaluation(*second, 2) + [0] * len(rows)])
            det = abs(first[0] * second[1] - second[0] * first[1])
            assert index2 == index1 * det * prod(hits2 - hits1)
            checks += 1
    return checks


def check_target_transfer():
    # Fix the polynomial mod ell. Among lifts, F(v')/ell excludes a single
    # class of F(v)/ell at overlapping simple roots regardless of the lift.
    checks = 0
    for prime in (3, 5, 7):
        for first in ((1, 1), (2, 3), (3, 5)):
            a, b = first
            if b % prime == 0:
                continue
            for scale in range(1, prime):
                aa, bb = scale * a + prime, scale * b
                if gcd(aa, bb) != 1:
                    continue
                # F0=(bX-aY)Y^2 has a simple root at v.
                by_first = {}
                for u in range(prime):
                    for w in range(prime):
                        val1 = (u*a + w*b) * b**2
                        val2 = (b*aa-a*bb)*bb**2 // prime + (u*aa + w*bb)*bb**2
                        key = val1 % prime
                        by_first.setdefault(key, set()).add(val2 % prime)
                assert len(by_first) == prime
                assert all(len(values) == 1 for values in by_first.values())
                assert len({next(iter(vals)) for vals in by_first.values()}) == prime
                offset = next(iter(by_first[0]))
                assert all(vals == {(offset + scale**3*k) % prime} for k, vals in by_first.items())
                checks += 1
    return checks


def check_lattices():
    points = ((1, 0), (0, 1), (1, 1), (-1, 1), (1, 2), (2, 3), (3, 5), (2, -1))
    indices = kernels = 0
    for h in (1, 2, 3, 4):
        for marks in combinations(points, h):
            vandermonde = prod(abs(a*d - b*c) for (a,b), (c,d) in combinations(marks, 2))
            polynomial = [1]
            for a, b in marks:
                polynomial = [
                    (b * polynomial[j-1] if j else 0)
                    - (a * polynomial[j] if j < len(polynomial) else 0)
                    for j in range(len(polynomial) + 1)
                ]
            for n in range(h-1, h+3):
                rows = [evaluation(a, b, n) for a, b in marks]
                index = 0
                for cols in combinations(range(n + 1), h):
                    index = gcd(index, determinant([[r[j] for j in cols] for r in rows]))
                assert index == vandermonde
                indices += 1
                for shift in range(n-h+1):
                    vector = [0] * shift + polynomial + [0] * (n-h-shift)
                    assert all(sum(c*x for c, x in zip(vector, row)) == 0 for row in rows)
                    kernels += 1
    return indices, kernels


def check_gaussians():
    # At (1,2), (2,3), the degree-two kernel is (2,-7,6) in ascending X degree.
    vector = (2, -7, 6)
    sqnorm = sum(c*c for c in vector)
    fibers = 0
    for width in (12, 16, 21):
        dual_tail = 2 * exp(-pi*width**2/sqnorm) / (1 - exp(-pi*width**2/sqnorm))
        for first in range(-3, 4):
            for second in range(-3, 4):
                offset = (first, second, first - 2*second)
                norm = sum(x*x for x in offset)
                projection = sum(x*y for x, y in zip(offset, vector))
                dist_sq = norm - projection**2 / sqnorm
                continuous = width/sqrt(sqnorm) * exp(-pi * dist_sq/width**2)
                discrete = sum(
                    exp(-pi*sum((x + k*y)**2 for x, y in zip(offset, vector))/width**2)
                    for k in range(-100, 101)
                )
                assert abs(discrete/continuous - 1) < dual_tail + 1e-13
                fibers += 1
    return fibers


if __name__ == "__main__":
    print("evaluation indices, integral kernel vectors, Gaussian fibers:", *check_lattices(), check_gaussians())
    print("conditional congruence indices, overlapping target transfers:", check_conditional_rows(), check_target_transfer())
