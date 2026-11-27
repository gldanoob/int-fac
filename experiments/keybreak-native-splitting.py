"""Exhaustive finite-field checks for native affine polynomial probes."""

from collections import Counter
from fractions import Fraction
from itertools import product

from sage.all import GF, PolynomialRing, legendre_symbol, prime_range


def check_slice(p, d, target):
    field = GF(p)
    ring = PolynomialRing(field, "x")
    x = ring.gen()
    point = field(1)
    target = field(target)
    degrees = [int(q) for q in prime_range(d // 2 + 1, d)]
    long = Counter()
    signs = Counter()
    affine_signs = Counter()
    for coefficients in product(range(p), repeat=d):
        monic = x**d + ring(coefficients)
        sign = legendre_symbol(int(monic.discriminant()), p)
        signs[sign] += 1

        # All polynomials of degree at most d with the prescribed value at 1.
        f = target + (x - point) * ring(coefficients)
        if f.degree() == d:
            affine_sign = legendre_symbol(int(f.discriminant()), p)
            affine_signs[affine_sign] += 1
            assert f(point) == target and f.monic()(point) != 0
            assert legendre_symbol(int(f.monic().discriminant()), p) == affine_sign
        for factor, multiplicity in f.factor():
            q = int(factor.degree())
            if q in degrees:
                assert multiplicity == 1
                long[q] += 1

    for q in degrees:
        assert long[q] == ((p**q - p) // q) * p**(d-q)
    assert signs[0] == p**(d-1)
    assert signs[-1] == signs[1]
    # A Frobenius sign inconsistent with the target rules out that square class.
    for wanted in (-1, 1):
        accepted = p**(d-1) + affine_signs[0] + affine_signs[wanted]
        assert Fraction(accepted, p**d) <= Fraction(1, 2) + Fraction(3, 2*p)
    return p**d


if __name__ == "__main__":
    total = sum(check_slice(p, d, a) for p, d, a in
                ((3, 4, 1), (3, 6, 2), (3, 7, 1), (5, 5, 2)))
    print(f"Checked affine long factors and discriminant signs on {total} polynomials.")
