"""Check the projection, normalization and derivative identities on finite boxes."""

from itertools import product
from math import gcd
from pathlib import Path
import runpy

PLANTS = runpy.run_path(str(Path(__file__).with_name("cogentic-planted-norm-two.py")))
evaluate = PLANTS["evaluate"]
multiply = PLANTS["multiply"]


def derivative(poly):
    return [i*c for i, c in enumerate(poly) if i]


def homogeneous(poly, a, b):
    degree = len(poly)-1
    return sum(c*a**j*b**(degree-j) for j, c in enumerate(poly))


def fields(coefficients, d, m):
    f = [2] + [0]*(d-1) + [1]
    for j, c in enumerate(multiply([-4*m, 4], coefficients)):
        f[j] += c
    g = f + [1]
    g[d] -= m
    return f, g


def run():
    d, k, height, coefficient_height = 5, 2, 3, 2
    coefficient_box = tuple(product(range(-coefficient_height, coefficient_height+1), repeat=k+1))
    marks = [(a, b) for b in range(1, height+1) for a in range(-height, height+1)
             if gcd(a, b) == 1]
    bases = (999_983, 1_000_003)
    pairs = {(coefficients, m): fields(coefficients, d, m) for coefficients in coefficient_box for m in bases}
    for (coefficients, m), (f, g) in pairs.items():
        n = m**d+2
        expected = d*m**(d-1)+4*evaluate(coefficients, m)
        assert evaluate(f, m) == evaluate(g, m) == n
        assert evaluate(derivative(f), m) == expected
        assert evaluate(derivative(g), m) % n == (expected-2) % n

    forms = comparisons = exceptions = 0
    for a, b in marks:
        by_projection = {}
        for coefficients in coefficient_box:
            u = homogeneous(coefficients, a, b)
            assert abs(u) <= (k+1)*coefficient_height*max(abs(a), b)**k
            if u:
                intercept = a**d+2*b**d+4*a*b**(d-1-k)*u
                slope = 4*b**(d-k)*u
                owner = 0
            else:
                intercept = a**d*(a+b)+2*b**(d+1)
                slope = b*a**d
                owner = 1
            by_projection[u] = (intercept, slope)
            for m in bases:
                norm = homogeneous(pairs[coefficients, m][owner], a, b)
                assert norm == intercept-slope*m
                assert norm % 2 == 1 if a % 2 else norm % 4 == 2
                comparisons += 1
        assert len(by_projection) < len(coefficient_box)
        for intercept, slope in by_projection.values():
            if slope == 0:
                assert (a, b, intercept) == (0, 1, 2)
                exceptions += 1
                continue
            common = gcd(intercept, slope)
            terms = [(intercept-slope*m)//common for m in range(bases[0], bases[0]+80, 2)]
            assert all(abs(value) >= bases[0]-abs(intercept) for value in terms)
            for divisor in range(3, 32, 2):
                hits = sum(value % divisor == 0 for value in terms)
                if gcd(divisor, slope//common) > 1:
                    assert hits == 0
                else:
                    assert divisor*hits <= len(terms)+divisor
            forms += 1
    assert exceptions == 1 and forms < comparisons//2
    print(f"{comparisons} exact norm comparisons, {forms} projected affine forms, {len(pairs)} derivative pairs")


if __name__ == "__main__":
    run()
