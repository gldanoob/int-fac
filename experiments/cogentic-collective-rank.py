"""Exact checks of collective mark constraints and the determinant update."""

from fractions import Fraction
from random import Random


def rank(rows):
    rows = [list(map(Fraction, row)) for row in rows]
    pivots = 0
    for col in range(len(rows[0])):
        pivot = next((i for i in range(pivots, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[pivot], rows[pivots] = rows[pivots], rows[pivot]
        for row in rows[pivots + 1:]:
            if row[col]:
                scale = row[col] / rows[pivots][col]
                row[col:] = [a - scale*b for a, b in zip(row[col:], rows[pivots][col:])]
        pivots += 1
    return pivots


def check_mark_spaces():
    incidences = 0
    for n in range(4, 17):
        # Consecutive affine triples force h to be globally affine. A quadratic
        # triple then forces it to be constant. Individual fields see few marks.
        fields = [[(a, a) for a in range(i, i + 3)] for i in range(n - 2)]
        fields += [[(a, a*a) for a in (0, 1, n - 1)], [(a, a*a) for a in range(4)]]
        cols = [(i, a, v) for i, field in enumerate(fields) for a, v in field]
        finite = [[int(i == j) for i, a, v in cols] for j in range(len(fields))]
        finite += [[int(a == b) for i, a, v in cols] for b in range(n)]
        finite += [[int(i == len(fields) - 1 and a == 0) for i, a, v in cols]]
        arch = [[v if i == j else 0 for i, a, v in cols] for j in range(len(fields))]
        augmented = [row + [int(j == len(finite) - 1)] for j, row in enumerate(finite)]
        r = rank(finite)
        assert rank(augmented) == r
        assert rank(finite + arch) == r + len(arch)
        incidences += len(cols)
    return incidences


def det_positive(matrix):
    # Every leading principal block is positive definite.
    m = [row[:] for row in matrix]
    previous = 1
    for k in range(len(m) - 1):
        for i in range(k + 1, len(m)):
            for j in range(k + 1, len(m)):
                numerator = m[k][k] * m[i][j] - m[i][k] * m[k][j]
                assert numerator % previous == 0
                m[i][j] = numerator // previous
        previous = m[k][k]
    return m[-1][-1]


def check_determinants():
    rng = Random(104729)
    comparisons = 0
    for n in range(2, 10):
        mat = [[int(i == j) for i in range(n)] for j in range(n)]
        for _ in range(16):
            g = [rng.randrange(-4, 5) for _ in range(n)]
            updated = [[mat[i][j] + g[i]*g[j] for j in range(n)] for i in range(n)]
            ratio = Fraction(det_positive(updated), det_positive(mat))
            for j in range(8):
                h = [rng.randrange(-5, 6) for _ in range(n)]
                h[j % n] = 1
                energy = sum(h[i]*mat[i][k]*h[k] for i in range(n) for k in range(n))
                assert ratio >= 1 + Fraction(sum(x*y for x, y in zip(h, g))**2, energy)
                comparisons += 1
            mat = updated
    return comparisons


if __name__ == '__main__':
    print('incidences in 13 collective systems, determinant comparisons:', check_mark_spaces(), check_determinants())
