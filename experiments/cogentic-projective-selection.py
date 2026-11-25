"""Fixed leading coefficients, residue-class fibers and separated Gaussian panel sums."""

from fractions import Fraction
from itertools import product
from math import exp, pi, sqrt


def weights(mark, degree):
    a, b = mark
    return [a**i * b**(degree-i) for i in range(degree+1)]


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def check_fixed_prefixes():
    checked = classes = 0
    marks = ((1, 2), (1, 3))
    total_degree = 4
    for j in range(1, total_degree+1):
        for known in product((-1, 2), repeat=total_degree-j):
            first, second = [weights(mark, j) for mark in marks]
            full = [weights(mark, total_degree) for mark in marks]
            shifts = [dot(row[j+1:], known) for row in full]
            for u in product((-2, 0, 1), repeat=j+1):
                for hit, mark in enumerate(marks):
                    direct = dot(full[hit], u+known)
                    reduced = dot((first, second)[hit], u)
                    assert direct == shifts[hit] + mark[1]**(total_degree-j)*reduced
                    checked += 1
            # The prescription is evaluation of the same polynomial at (2,1)
            # modulo 3. Its offset changes with every fixed leading coefficient.
            prime = 3
            row = weights((2, 1), total_degree)
            offset = 1-dot(row[j+1:], known)
            permitted = {(dot(first, u) % prime, dot(second, u) % prime)
                         for u in product(range(prime), repeat=j+1)
                         if (dot(row[:j+1], u)-offset) % prime == 0}
            for y in product(range(prime), repeat=2):
                # Here determinant of the two marks is 1; enumerate a larger
                # coefficient box to independently verify the affine image.
                possible = any((dot(first, u)-y[0]) % prime == 0 and
                               (dot(second, u)-y[1]) % prime == 0 and
                               (dot(row[:j+1], u)-offset) % prime == 0
                               for u in product(range(-1, 3), repeat=j+1))
                assert possible == (y in permitted)
                classes += 1
    return checked, classes


def panel_sum(first, second, matrix, residue, modulus, rho, degree):
    a, cross, c = matrix
    grouped = {}
    for y, x, value in first:
        if y % modulus == residue[0]:
            panel = int(x//rho)
            grouped.setdefault(panel, []).append((x, value))
    total = 0.0
    for panel, x_values in grouped.items():
        center = (panel+.5)*rho
        first_sums = [0.0]*(degree+1)
        for xi, value in x_values:
            power = value
            for l in range(degree+1):
                first_sums[l] += power
                power *= (xi-center)/rho
        for y, eta, value in second:
            if y % modulus != residue[1]:
                continue
            h0 = -pi*(a*center**2 + 2*cross*center*eta + c*eta**2)
            h1 = -2*pi*rho*(a*center+cross*eta)
            h2 = -pi*a*rho**2
            previous, coefficient = 0.0, exp(h0)
            for l in range(degree+1):
                total += value*coefficient*first_sums[l]
                previous, coefficient = coefficient, (h1*coefficient+2*h2*previous)/(l+1)
    return total


def check_separated_gaussians():
    cases = 0
    worst = 0.0
    for marks in (((1, 2), (2, 3)), ((1, 3), (1, 2)), ((1, 3), (3, 5))):
        for j in (1, 2, 3):
            ts = [a/b for a, b in marks]
            v, w = [tuple(t**i for i in range(j+1)) for t in ts]
            g00, g01, g11 = dot(v, v), dot(v, w), dot(w, w)
            det = g00*g11-g01**2
            matrix = (g11/det, -g01/det, g00/det)
            rho = 1/(4*sqrt(pi*(g00+g11)/det))
            arrays = []
            for idx, (_, b) in enumerate(marks):
                scale = 2 * b**j
                arrays.append([(u, u/scale, ((u*u + (idx+1)*u+2) % 7)/7)
                               for u in range(-min(30, scale*2), min(30, scale*2)+1)])
            for residue in product(range(3), repeat=2):
                direct = sum(f*g*exp(-pi*(matrix[0]*x*x+2*matrix[1]*x*y+matrix[2]*y*y))
                             for i, x, f in arrays[0] for k, y, g in arrays[1]
                             if i % 3 == residue[0] and k % 3 == residue[1])
                separated = panel_sum(*arrays, matrix, residue, 3, rho, 20)
                worst = max(worst, abs(direct-separated))
                assert abs(direct-separated) < 5e-12*max(1, direct)
                cases += 1
    return cases, worst


def check_schedules():
    # Approach v=(8/3)^(1/3) from strictly above using rational b,c,x.
    rows = []
    for scale in (100, 1000, 10000, 100000):
        top = 1
        while 3*top**3 <= 8*scale**3:
            top += 1
        v = Fraction(top+3, scale)
        x = 1/v+Fraction(1, 10*scale)
        c = v/x
        b = c/2-Fraction(1, 10*scale)
        s = 2*c+2*b+1
        height = x*c+1/x
        assert x*c > 1/x and c > 2*b and b*(c-b) > height/3 and s > 2*c+2*b
        assert v**3 > Fraction(8, 3)
        rows.append(v)
    assert all(x > y for x, y in zip(rows, rows[1:]))
    return len(rows), rows[-1]


if __name__ == "__main__":
    fixed, classes = check_fixed_prefixes()
    gaussians, error = check_separated_gaussians()
    schedules, result = check_schedules()
    print(f"{fixed} conditional evaluations; {classes} projected congruences; "
          f"{gaussians} separated Gaussians (max absolute difference {error:.3g}); "
          f"{schedules} strict schedules down to {result}")
