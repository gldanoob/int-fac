"""Check square-space gains from compatible quadratic charts."""

from fractions import Fraction
from math import gcd
from pathlib import Path
from runpy import run_path


MATCHING = run_path(str(Path(__file__).with_name("cogentic-rational-root-matching.py")))
SQUARES = MATCHING["SQUARES"]


def reduce_fraction(value, n):
    value = Fraction(value)
    return value.numerator * pow(value.denominator, -1, n) % n


def align(n, reference, chart):
    discriminant, root = chart
    scale = SQUARES["rational_sqrt"](Fraction(discriminant, reference[0]))
    if scale is None:
        return None, None
    mapped = reduce_fraction(scale, n) * reference[1] % n
    if root % n == mapped:
        return scale, None
    if root % n == -mapped % n:
        return -scale, None
    factor = gcd(root-mapped, n)
    assert 1 < factor < n
    return None, factor


def coordinates(slope, scale, a, b):
    return Fraction(2*a+b*slope, 2), -b*Fraction(scale, 2)


def replay():
    n, discriminant = 93, 112
    assert 1+20+72 == 4+36+53 == n
    assert gcd(22, n) == 1
    scale, factor = align(n, (112, 22), (112, 22))
    assert scale == 1 and factor is None
    first = coordinates(20, 1, -7, 1)
    second = coordinates(18, scale, -172, 35)
    sign = (-1, 0)
    assert not SQUARES["square_kernel"](discriminant, [first, sign])
    assert not SQUARES["square_kernel"](discriminant, [second, sign])
    assert SQUARES["norm"](discriminant, first) == -19
    assert SQUARES["norm"](discriminant, second) == -13851
    signed = SQUARES["square_kernel"](discriminant, [first, sign, second, sign])
    assert len(signed) == 2

    multiply = SQUARES["multiply"]
    known_root = coordinates(20, 1, 9, -1)
    square = coordinates(20, 1, 9, 2)
    assert multiply(discriminant, known_root, known_root) == square
    assert multiply(discriminant, first, square) == second
    (mask, root), = SQUARES["square_kernel"](discriminant, [first, second])
    assert mask == 3
    residue = reduce_fraction(root[0]+22*root[1], n)
    _, normalized = MATCHING["matched_basis"](n, [((-8)*(-242), residue)])[0]
    assert {gcd(normalized-1, n), gcd(normalized+1, n)} == {3, 31}
    assert MATCHING["matched_basis"](n, [((-8)*(-3497), residue)]) == []

    fractional, factor = align(n, (448, 44), (112, 22))
    assert fractional == Fraction(1, 2) and factor is None
    a, b = coordinates(20, fractional, -7, 1)
    assert reduce_fraction(a+44*b, n) == -8 % n
    assert align(n, (112, 22), (112, -22)) == (-1, None)
    assert align(n, (112, 22), (112, 40)) == (None, 3)
    print("Verified merged square dimensions, the split of 93, and chart alignment")


if __name__ == "__main__":
    replay()
