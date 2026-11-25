"""Three-mark Gaussian contractions and exact fixed-trace parameter margins."""

from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import exp, pi, prod, sqrt


def inverse(a):
    n = len(a)
    rows = [list(row)+[F(i == j) for j in range(n)] for i, row in enumerate(a)]
    for i in range(n):
        pivot = rows[i][i]
        assert pivot
        rows[i] = [x/pivot for x in rows[i]]
        for j in range(n):
            if i != j:
                factor = rows[j][i]
                rows[j] = [x-factor*y for x, y in zip(rows[j], rows[i])]
    return [r[n:] for r in rows]


def quadratic(a, x):
    return sum(x[i]*a[i][j]*x[j] for i, j in product(range(len(x)), repeat=2))


def panel_moments(values, rho, degree):
    table = defaultdict(lambda: [0.]*(degree+1))
    for x, w in values:
        panel = int(x//rho)
        center = (panel+.5)*rho
        power = w
        for i in range(degree+1):
            table[panel][i] += power
            power *= (x-center)/rho
    return table


def contract(a, coords, rho, degree):
    first, second = [panel_moments(values, rho, degree) for values in coords[:2]]
    result = 0.
    cxx, cyy, cxy = (-pi*rho*rho*a[0][0], -pi*rho*rho*a[1][1], -2*pi*rho*rho*a[0][1])
    for gx, mx in first.items():
        for gy, my in second.items():
            for z, weight in coords[2]:
                center = ((gx+.5)*rho, (gy+.5)*rho, z)
                bx, by = [-2*pi*rho*sum(a[i][k]*center[k] for k in range(3)) for i in (0, 1)]
                coeffs = [[0.]*(degree+1) for _ in range(degree+1)]
                coeffs[0][0] = exp(-pi*quadratic(a, center))
                for j in range(degree+1):
                    if j:
                        coeffs[0][j] = (by*coeffs[0][j-1]+
                                         (2*cyy*coeffs[0][j-2] if j >= 2 else 0.))/j
                    for i in range(1, degree+1):
                        coeffs[i][j] = (bx*coeffs[i-1][j] +
                                        (2*cxx*coeffs[i-2][j] if i >= 2 else 0.) +
                                        (cxy*coeffs[i-1][j-1] if j else 0.))/i
                    result += weight*my[j]*sum(mx[i]*coeffs[i][j] for i in range(degree+1))
    return result


def check_tensors():
    marks = [(1, 4), (1, 2), (3, 4), (2, 3)]
    checked, worst = 0, 0.
    for points in combinations(marks, 3):
        slopes = [F(a, b) for a, b in points]
        spacing = prod(abs(x-y) for x, y in combinations(slopes, 2))
        for degree in (2, 3, 5):
            gram = [[sum((x*y)**i for i in range(degree+1)) for x in slopes] for y in slopes]
            inv = inverse(gram)
            assert max(abs(x) for row in inv for x in row)*spacing**2 < 25
            matrix = [[float(x) for x in row] for row in inv]
            rho = 1/(4*sqrt(pi*sum(abs(x) for row in matrix for x in row)))
            for residues in ((0, 0, 0), (0, 1, 1), (1, 1, 0)):
                coords = [[((y-4)*rho/3, (1+(y+v)**2 % 5)/5)
                           for y in range(9) if y % 2 == residue]
                          for v, residue in enumerate(residues)]
                direct = sum(prod(v for _, v in vals)*exp(-pi*quadratic(matrix, [u for u, _ in vals]))
                             for vals in product(*coords))
                error = abs(direct-contract(matrix, coords, rho, 12))
                assert error < 2e-11*max(1, direct)
                worst = max(worst, error)
                checked += 1
    return checked, worst


def check_parameters():
    schedules = []
    for scale in (100, 1000, 10000, 100000):
        top = 1
        while 9*top**3 <= 16*scale**3:
            top += 1
        v = F(top+3, scale)
        x = 1/v+F(1, 10*scale)
        c = v/x
        b = c/2-F(1, 10*scale)
        height = v+1/x
        eta = F(1, 100*scale)
        k = 2*(int(1/eta)+1)
        assert x*v > 1 and c > 2*b and k % 2 == 0 and k > 2/eta
        assert 2*c-2*height/(3*b) > (1+eta)*b
        schedules.append(v)
    assert all(x > y for x, y in zip(schedules, schedules[1:]))
    return len(schedules), schedules[-1]


if __name__ == "__main__":
    tensors, delta = check_tensors()
    count, ratio = check_parameters()
    print(f"{tensors} restricted three-mark contractions, max absolute difference {delta:.3g}; "
          f"{count} fixed-even-trace schedules down to {ratio}")
