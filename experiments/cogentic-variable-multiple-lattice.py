"""Exact finite checks of the variable-multiple evaluation lattice and cell bound."""

from itertools import combinations, permutations
from math import gcd, prod


def determinant(matrix):
    a = [row[:] for row in matrix]
    n, sign, previous = len(a), 1, 1
    for k in range(n - 1):
        if not a[k][k]:
            pivot = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = (a[i][j] * a[k][k] - a[i][k] * a[k][j]) // previous
        previous = a[k][k]
    return sign * a[-1][-1]


def digits(value, base):
    coefficients = []
    while value:
        value, digit = divmod(value, base)
        coefficients.append(digit)
    return coefficients


def basis(mod, base, degree):
    r = digits(mod, base)
    out = [r + [0] * (degree + 1 - len(r))]
    for power in range(degree):
        out.append([0] * power + [-base, 1] + [0] * (degree - power - 1))
    return out


def evaluate(poly, mark):
    a, b = mark
    return sum(x * a**j * b**(len(poly) - 1 - j) for j, x in enumerate(poly))


def image_index(rows):
    index = 0
    for cols in combinations(range(len(rows[0])), len(rows)):
        index = gcd(index, determinant([[r[c] for c in cols] for r in rows]))
    return index


def check_images():
    points = ((0, 1), (1, 1), (1, 2), (1, 3), (2, 3), (3, 5), (3, 7), (1, 0))
    matrices = conditional = kernels = 0
    for mod, base in ((35, 4), (77, 5), (91, 7), (143, 6)):
        full_basis = basis(mod, base, len(digits(mod, base)) + 2)
        degree = len(full_basis) - 1
        assert abs(determinant(full_basis)) == mod
        assert all(evaluate(poly, (base, 1)) % mod == 0 for poly in full_basis)
        unit_marks = [v for v in points if gcd(v[0] - base*v[1], mod) == 1]
        for h in (1, 2, 3):
            for marks in combinations(unit_marks, h):
                rows = [[evaluate(poly, v) for poly in full_basis] for v in marks]
                vandermonde = prod(abs(a*d - b*c) for (a, b), (c, d) in combinations(marks, 2))
                assert image_index(rows) == vandermonde
                matrices += 1
                for poly in basis(mod, base, degree - h):
                    for a, b in marks:
                        poly = [b*x - a*y for x, y in zip([0] + poly, poly + [0])]
                    assert evaluate(poly, (base, 1)) % mod == 0
                    assert all(evaluate(poly, v) == 0 for v in marks)
                    kernels += 1
        for first, second in permutations(unit_marks, 2):
            det = abs(first[0] * second[1] - first[1] * second[0])
            for p, r in ((2, 0), (3, 2), (5, 1)):
                if mod % p == 0:
                    continue
                rows = [[evaluate(poly, (r, 1)) for poly in full_basis] + [p]]
                for v in (first, second):
                    rows.append([evaluate(poly, v) for poly in full_basis] + [0])
                hits = [(a-b*r) % p == 0 for a,b in (first, second)]
                assert image_index(rows[:2]) == (p if hits[0] else 1)
                assert image_index(rows) == det * (p if any(hits) else 1)
                conditional += 1
    return matrices, conditional, kernels


def check_cells():
    num = 0
    for length in (19, 37, 52):
        interval = range(12, 12 + length)
        for mark, denom in (((2, 5), 23), ((3, 7), 29)):
            a, b = mark
            for q in (1, 11, 13, 11*13):
                for h in (1, 2, 3, 6, 31, 2*31):
                    assert gcd(h, b*q) == 1
                    for r in (0, 1, 7):
                        weighted = sum((1+q*((x-r*denom) % q == 0)) for x in interval
                                       if (a*denom-x*b) % h == 0)
                        assert abs(weighted*h - 2*length) <= (q+1)*h
                        num += 1
                    for p in (11, 13):
                        weighted = sum((1+q*((x-denom) % q == 0)) for x in interval
                                       if (a*denom-x*b) % p**2 == 0)
                        assert weighted*p <= 2*length + (q+1)*p
                        num += 1
    return num


if __name__ == '__main__':
    print('evaluation images, prescribed fibers, digit-kernel checks:', *check_images())
    print('weighted class estimates:', check_cells())
