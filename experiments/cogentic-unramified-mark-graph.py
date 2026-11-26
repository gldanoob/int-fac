#!/usr/bin/env python3
"""Replay graph-supported mark valuations, signs and cycle units in two fields."""

from fractions import Fraction
from itertools import product
from math import gcd, prod
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).parent
PLANTS = run_path(str(HERE / "cogentic-planted-norm-two.py"))
evaluate, multiply = PLANTS["evaluate"], PLANTS["multiply"]
integer_root = PLANTS["BASE"]["integer_root"]
binary_rank = run_path(str(HERE / "cogentic-sparse-kernel.py"))["binary_rank"]
squarefree_factors = run_path(str(HERE / "cogentic-fixed-rank-audit.py"))["squarefree_factors"]


def divide_monic(dividend, divisor):
    remainder = list(dividend)
    quotient = [0] * (len(dividend) - len(divisor) + 1)
    for i in reversed(range(len(quotient))):
        leading = remainder.pop()
        quotient[i] = leading
        for j, c in enumerate(divisor[:-1]):
            remainder[i + j] -= leading * c
    return quotient, remainder


def build(n, m, h, marks, degree):
    r = len(marks)
    period = 1 << (r - 1).bit_length()
    assert n % 2 and max(marks) < m < n <= m**h
    assert degree % 2 and (degree - 1) % period == 0
    assert degree > 2*r + 1 and degree - r >= h

    mark_poly = [1]
    for a in marks:
        divisor = gcd(m - a, n)
        if divisor > 1:
            return divisor
        mark_poly = multiply(mark_poly, [-a, 1])

    quotient, remainder = divide_monic([0, -1] + [0]*(degree - 2) + [1], mark_poly)
    assert all(c % 2 == 0 for c in remainder)
    quotient = [c % 2 for c in quotient]
    assert quotient[0] == 0
    quotient[0] = 2

    at_m = evaluate(mark_poly, m)
    target = (-m * pow(at_m, -1, n) - evaluate(quotient, m)) * pow(4, -1, n) % n
    for i in range(h):
        target, digit = divmod(target, m)
        quotient[i] += 4*digit
    assert target == 0

    polynomial = multiply(mark_poly, quotient)
    polynomial[1] += 1
    bump = multiply([-m, 1], multiply(mark_poly, mark_poly))
    endpoints = [Fraction(3*a + side, 3) for a, side in product(marks, (-1, 1))]
    scale = max(1, *(1 + evaluate(polynomial, x) // (-4*evaluate(bump, x)) for x in endpoints))
    for i, c in enumerate(bump):
        polynomial[i] += 4*scale*c
    return polynomial


def cycle_unit(polynomial, numerator, denominator):
    value = [1]
    for a in numerator:
        value = multiply(value, [a, -1])
    for a in denominator:
        # Subtract a multiple of F to make the division exact at a.
        scale = Fraction(evaluate(value, a), a)
        dividend = [-scale*c for c in polynomial]
        for i, c in enumerate(value):
            dividend[i] += c
        quotient, remainder = divide_monic(dividend, [-a, 1])
        assert remainder == [0]
        value = [-c for c in quotient]
    assert all(c.denominator == 1 for c in value)
    return [int(c) for c in value]


def check_field(polynomial, n, m, edges, cycles):
    assert polynomial[-1] == 1 and polynomial[0] % 4 == 2
    assert all(c % 2 == 0 for c in polynomial[:-1])
    assert evaluate(polynomial, m) % n == 0
    derivative = [i*c for i, c in enumerate(polynomial) if i]
    marks = tuple(map(prod, edges))

    sign_rows = []
    offset = Fraction(1, 3)
    for a, edge in zip(marks, edges, strict=True):
        norm = evaluate(polynomial, a)
        assert norm == a and squarefree_factors(norm) == sorted(edge)
        # The simple root 0 mod p identifies the same degree-one prime for every incident edge.
        assert all(a % p == 0 and evaluate(derivative, a) % p == 1 for p in edge)
        for left, right in ((a - offset, a), (a, a + offset)):
            assert evaluate(polynomial, left) * evaluate(polynomial, right) < 0
            assert all(not left < mark < right for mark in marks)
            sign_rows.append(sum(1 << i for i, mark in enumerate(marks) if mark <= left))
    assert binary_rank(sign_rows) == len(marks)

    images, cycle_signs = [], []
    for numerator, denominator in cycles:
        assert prod(numerator) == prod(denominator)
        unit = cycle_unit(polynomial, numerator, denominator)
        inverse = cycle_unit(polynomial, denominator, numerator)
        _, remainder = divide_monic(multiply(unit, inverse), polynomial)
        assert remainder == [1] + [0]*(len(polynomial) - 2)

        ratio = Fraction(prod(a - m for a in numerator), prod(a - m for a in denominator))
        image = ratio.numerator * pow(ratio.denominator, -1, n) % n
        assert evaluate(unit, m) % n == image and image not in (0, 1, n - 1)
        images.append(image)

        mask = sum(1 << marks.index(a) for a in numerator + denominator)
        cycle_signs.append(sum(((mask & row).bit_count() % 2) << i for i, row in enumerate(sign_rows)))
    assert binary_rank(cycle_signs) == len(cycles)
    return images


def replay():
    left, right = (19, 23), (29, 31, 37)
    vertices = left + right
    assert len(set(vertices)) == len(vertices) and all(p % 2 for p in vertices)
    assert max(vertices) < 2*min(vertices) and all(squarefree_factors(p) == [p] for p in vertices)
    edges = tuple(product(left, right))
    marks = tuple(map(prod, edges))
    incidence = [sum(1 << i for i, edge in enumerate(edges) if p in edge) for p in vertices]
    assert all(row.bit_count() >= 2 for row in incidence)
    cycles = [((left[0]*right[0], left[1]*p), (left[0]*p, left[1]*right[0])) for p in right[1:]]
    cycle_masks = [sum(1 << marks.index(a) for a in numerator + denominator)
                   for numerator, denominator in cycles]
    finite_rank = binary_rank(incidence)
    assert finite_rank == len(vertices) - 1
    assert all((mask & row).bit_count() % 2 == 0 for mask in cycle_masks for row in incidence)
    assert binary_rank(cycle_masks) == len(edges) - finite_rank == len(cycles)

    n, h = 1_000_000_007 * 1_000_000_009, 6
    m = integer_root(n - 1, h) + 1
    degrees = (17, 25)
    images = [check_field(build(n, m, h, marks, degree), n, m, edges, cycles) for degree in degrees]
    assert images[0] == images[1] and len(set(images[0])) == len(cycles)

    p, q = 1_000_003, 1_000_033
    assert build(p*q, p + marks[0], 2, marks, degrees[0]) == p
    print(f"K2,3 with N={n}, m={m}, degrees {degrees}: "
          f"finite rank {finite_rank}, sign rank {len(marks)}, cycle rank {len(cycles)}")
    print(f"Common cycle images {images[0]}; proper gcd branch returned {p}.")


if __name__ == "__main__":
    replay()
