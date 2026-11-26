#!/usr/bin/env python3
"""Try to split an integer using the fixed elliptic four-mark chart."""

import argparse
import sys
from math import gcd
from pathlib import Path
from runpy import run_path


EXACT = run_path(str(Path(__file__).with_name("cogentic-elliptic-square-cycle.py")))
CURVE, K, SEED = (EXACT[name] for name in ("CURVE", "K", "SEED"))
AXES = ((-1344, 13680), (-544, 9520))
BAD_PRIMES = (2, 3, 5, 7, 11, 17, 19)


class FactorFound(Exception):
    """A modular operation exposed a proper divisor."""


def checked_gcd(value, modulus):
    divisor = gcd(value, modulus)
    if 1 < divisor < modulus:
        raise FactorFound(divisor)
    return divisor


def negate(point, modulus):
    return None if point is None else (point[0], -point[1] % modulus)


def add(left, right, modulus, a2=CURVE[2], a4=CURVE[1]):
    if left is None:
        return right
    if right is None:
        return left
    x, y = left
    u, v = right
    if x == u:
        if (y + v) % modulus == 0:
            return None
        if y != v:
            # At equal x, (y-v)(y+v)=0. Mixed signs expose a proper gcd.
            checked_gcd(y - v, modulus)
            raise AssertionError("mixed signs without a proper divisor")
        numerator, denominator = 3*x*x + 2*a2*x + a4, 2*y
    else:
        numerator, denominator = v - y, u - x
    checked_gcd(denominator, modulus)
    slope = numerator * pow(denominator, -1, modulus) % modulus
    w = (slope*slope - a2 - x - u) % modulus
    return w, (slope*(x - w) - y) % modulus


def check_chart(point, modulus):
    if point is None:
        return
    x, y = point
    if checked_gcd(x, modulus) == modulus:
        return
    inverse = pow(x, -1, modulus)
    m = (51 - K*inverse) % modulus
    root = -K*y*inverse*inverse % modulus
    a = (m - 51)*(m - 95) % modulus
    b = (m - 57)*(m - 85) % modulus
    f = (m + a*b*(a - 1)) % modulus
    if checked_gcd(f, modulus) == modulus:
        algebraic = b*(1 - 2*a) % modulus
        assert (algebraic*algebraic - root*root) % modulus == 0
        checked_gcd(algebraic - root, modulus)
        checked_gcd(algebraic + root, modulus)


def find_split(modulus, radius=None):
    """Return a proper divisor or None after the specified finite search."""
    if modulus < 2:
        raise ValueError("modulus must be at least 2")
    if radius is None:
        radius = modulus.bit_length()
    if radius < 0:
        raise ValueError("radius must be nonnegative")

    try:
        for prime in BAD_PRIMES:
            if checked_gcd(prime, modulus) == modulus:
                return None
        seed = tuple(c % modulus for c in SEED)
        step1, step2 = (tuple(c % modulus for c in point) for point in AXES)
        axis1 = {0: seed}
        axis2 = {0: None}
        reverse1 = negate(step1, modulus)
        multiple = seed
        check_chart(seed, modulus)
        for r in range(1, radius + 1):
            if r > 1:
                multiple = add(multiple, seed, modulus)
                check_chart(multiple, modulus)
            axis1[r] = add(axis1[r - 1], step1, modulus)
            axis1[-r] = add(axis1[1 - r], reverse1, modulus)
            axis2[r] = add(axis2[r - 1], step2, modulus)
            axis2[-r] = negate(axis2[r], modulus)
            for j in range(-r, r + 1):
                check_chart(add(axis1[r], axis2[j], modulus), modulus)
                check_chart(add(axis1[-r], axis2[j], modulus), modulus)
            for i in range(1 - r, r):
                check_chart(add(axis1[i], axis2[r], modulus), modulus)
                check_chart(add(axis1[i], axis2[-r], modulus), modulus)
    except FactorFound as found:
        divisor, = found.args
        assert 1 < divisor < modulus and modulus % divisor == 0
        return divisor
    return None


def replay():
    assert find_split(9703, 0) in (31, 313)
    assert find_split(31*101, 0) == 31
    modulus = 33873417617833492629436999
    assert find_split(modulus, 1) is None
    assert find_split(modulus) in (5829071504407, 5811117189457)
    rank_two = 119145577638761874911337251
    assert find_split(rank_two, 0) is None
    assert find_split(rank_two, 1) in (7048565572157, 16903521208543)
    assert find_split(17) is None and find_split(121, 0) == 11
    assert find_split(1_000_000_007 * 1_000_000_009, 2) is None

    modulus = 23*29
    seed = tuple(c % modulus for c in SEED)
    assert add(seed, negate(seed, modulus), modulus) is None

    def crt(left, right):
        return tuple(a % 23 + 23*((b - a % 23)*pow(23, -1, 29) % 29)
                     for a, b in zip(left, right, strict=True))

    mixed = crt(seed, negate(seed, modulus))
    tangent = crt((12, 0), seed)
    for left, right, divisor in ((seed, mixed, 23), (tangent, tangent, 23), (seed, tangent, 29)):
        try:
            add(left, right, modulus)
        except FactorFound as found:
            assert found.args == (divisor,)
        else:
            raise AssertionError("nonunit denominator did not give the expected factor")
    check_chart((0, 6), 23)
    print("Modular elliptic chart split the seed, 85-bit and rank-two fixtures. Bounded misses passed.")


def main():
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?", help="integer to split, or omit to run the replay")
    parser.add_argument("--radius", type=int, help="shell limit, defaults to the bit length of N")
    args = parser.parse_args()
    if args.N is None:
        if args.radius is not None:
            parser.error("--radius requires N")
        replay()
        return
    try:
        divisor = find_split(args.N, args.radius)
    except ValueError as error:
        parser.error(str(error))
    if divisor is None:
        radius = args.N.bit_length() if args.radius is None else args.radius
        print(f"No split found within radius {radius}.")
        raise SystemExit(1)
    print(f"{args.N} = {divisor} * {args.N // divisor}")


if __name__ == "__main__":
    main()
