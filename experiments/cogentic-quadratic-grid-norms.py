"""Compute exact norm squareclasses on a centered quadratic mark grid."""

from fractions import Fraction
from math import gcd, isqrt
from pathlib import Path
from runpy import run_path
from time import perf_counter


HERE = Path(__file__).resolve().parent
GRID = run_path(str(HERE / "cogentic-monic-large-primes.py"))


def norm_words(field, points, height):
    """Return packed signed rational norm columns on the given primitive marks."""
    constant, linear, leading = field
    if leading != 1 or linear not in (0, -1, -2) or height < 1:
        raise ValueError("expected a centered monic quadratic and positive grid height")
    cutoff = (2 + abs(linear))*height**2
    primes = tuple(GRID["primes_through"](cutoff))
    bits, cached, words = {}, {}, []
    for a, b in points:
        if abs(a) > height or not 1 <= b <= height or gcd(a, b) != 1:
            raise ValueError("expected primitive marks in the given box")
        value = a*a + linear*a*b + constant*b*b
        if not value:
            raise ValueError("squareclasses require nonzero norms")
        if value not in cached:
            word = int(value < 0)
            remaining = abs(value)
            for p in primes:
                if p*p > remaining:
                    break
                odd = False
                while remaining % p == 0:
                    remaining //= p
                    odd = not odd
                if odd:
                    word |= 1 << bits.setdefault(p, len(bits)+1)
            if remaining > 1 and isqrt(remaining)**2 != remaining:
                # Any residual at most cutoff is prime, and all larger shared tails are equal.
                word |= 1 << bits.setdefault(remaining, len(bits)+1)
            cached[value] = word
        words.append(cached[value])
    return words


def norm_basis(field, points, height):
    """Return original-coordinate kernel masks, including the final norm-one sign column."""
    words = [*norm_words(field, points, height), 0]
    return GRID["eliminate"](words, (1 << j for j in range(len(words))))


def compare(reference, field, points, height):
    start = perf_counter()
    words = reference([*(GRID["homogeneous"](field, a, b) for a, b in points), 1])
    expected = GRID["eliminate"](words, (1 << j for j in range(len(words))))
    trial = perf_counter()-start
    start = perf_counter()
    actual = norm_basis(field, points, height)
    bounded = perf_counter()-start
    assert actual == expected
    return len(actual)-1, trial, bounded


def main():
    quadratic = run_path(str(HERE / "cogentic-quadratic-square-kernel.py"))
    reference = quadratic["rational_words"]
    centered = run_path(str(HERE / "cogentic-selected-polynomial-recenter.py"))["centered_pair"]
    inputs = run_path(str(HERE / "cogentic-monic-blind-grid.py"))["INPUTS"]
    height = 4
    points = [(a, b) for a in range(-height, height+1) for b in range(1, height+1)
              if gcd(a, b) == 1]
    for field in ((-2, 0, 1), (25, -2, 1), (101*103**2-1, 0, 1), ((101*103)**2-1, 0, 1)):
        compare(reference, field, points, height)
    assert norm_words((101*103**2-1, 0, 1), [(1, 1), (-1, 1)], height) == [2, 2]
    assert norm_words(((101*103)**2-1, 0, 1), [(1, 1), (-1, 1)], height) == [0, 0]
    left, right = norm_words((66, -2, 1), [(-3, 2), (1, 3)], 3)
    assert (left & right).bit_count() == 1

    print("N, height, unit marks, total norm rank, gcd-free seconds, bounded seconds", flush=True)
    for height in (12, 24):
        for n in inputs:
            m = isqrt(n)
            slopes, constants, _ = centered(n)
            points = [(a, b) for a in range(-height, height+1) for b in range(1, height+1)
                      if gcd(a, b) == gcd(a-b*m, n) == 1]
            results = [compare(reference, (v, u, 1), points, height)
                       for u, v in zip(slopes, constants, strict=True)]
            nullity, trial, bounded = map(sum, zip(*results, strict=True))
            print(n, height, len(points), 2*len(points)-nullity,
                  f"{trial:.6f}", f"{bounded:.6f}", flush=True)

    n, height = inputs[0], 24
    m = isqrt(n)
    slopes, constants, discriminants = centered(n)
    points = [(a, b) for a in range(-height, height+1) for b in range(1, height+1)
              if gcd(a, b) == gcd(a-b*m, n) == 1]
    print("N, height, slope, signed norm nullity, square nullity, product seconds, second gcd-free seconds")
    for u, v, d in zip(slopes, constants, discriminants, strict=True):
        basis = norm_basis((v, u, 1), points, height)
        elements = [(a+Fraction(b*u, 2), Fraction(-b, 2)) for a, b in points] + [(-1, 0)]
        start = perf_counter()
        scalars = [quadratic["descent"](d, quadratic["masked_product"](d, elements, mask))[0] for mask in basis]
        products = perf_counter()-start
        start = perf_counter()
        squares = GRID["eliminate"](reference([*scalars, d]), [*basis, 0])
        descent = perf_counter()-start
        print(n, height, u, len(basis), len(squares), f"{products:.6f}", f"{descent:.6f}")


if __name__ == "__main__":
    main()
