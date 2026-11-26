#!/usr/bin/env python3
"""Search small imaginary quadratic norm-one tori for a smooth local order."""

import argparse
from math import gcd
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).resolve().parent
weighted_class_number = run_path(str(HERE / "untwisted-legendre-traces.py"))["weighted_order_class_number"]
saturation = run_path(str(HERE / "cogentic-elliptic-local-saturation.py"))
smooth_exponent = saturation["smooth_exponent"]
primes_through = saturation["primes_through"]


def norm_generator(s, ell, h):
    """For D=-s and odd split prime ell, find z generating an ell-ideal to power h."""
    k = (1 + s) // 4
    root = next((x for x in range(ell) if (x*x - x + k) % ell == 0), None)
    if root is None:
        return None
    derivative_inverse = pow(2*root - 1, -1, ell)
    modulus = ell
    for _ in range(1, h):
        quotient = (root*root - root + k) // modulus
        root += modulus * ((-quotient * derivative_inverse) % ell)
        modulus *= ell

    def norm(vector):
        a, b = vector
        return a*a + a*b + k*b*b

    # Gauss reduction for the norm Gram matrix in the basis (1, omega).
    first, second = (modulus, 0), (-root, 1)
    while True:
        if norm(second) < norm(first):
            first, second = second, first
        a, b = first
        c, d = second
        inner_twice = 2*a*c + a*d + b*c + 2*k*b*d
        length = norm(first)
        if abs(inner_twice) <= length:
            assert length == modulus
            return first
        quotient = (inner_twice + length) // (2*length)
        second = c - quotient*a, d - quotient*b


def multiply(left, right, k, n):
    a, b = left
    c, d = right
    return (a*c - k*b*d) % n, (a*d + b*c + b*d) % n


def quotient_power(n, k, z, exponent):
    a, b = z
    norm = a*a + a*b + k*b*b
    inverse = pow(norm, -1, n)
    base = tuple(c*inverse % n for c in multiply(z, z, k, n))
    value = (1, 0)
    for bit in bin(exponent)[2:]:
        value = multiply(value, value, k, n)
        if bit == "1":
            value = multiply(value, base, k, n)
    return value


def split_from_generator(n, k, z, odd_power):
    value = quotient_power(n, k, z, odd_power)
    for _ in range((4*n).bit_length() + 1):
        divisor = gcd(n, value[0] - 1, value[1])
        if divisor > 1:
            return divisor if divisor < n else None
        value = multiply(value, value, k, n)
    return None


def find_split(n, smooth_bound, menu_bound):
    if n < 3 or n % 2 == 0 or smooth_bound < 1 or menu_bound < 3:
        raise ValueError("expected odd N >= 3, positive smooth bound and menu bound >= 3")
    primes = primes_through(menu_bound)
    for p in primes:
        if n % p == 0:
            return p if p < n else None
    odd_power = smooth_exponent(n, smooth_bound)
    for s in primes:
        if s % 4 != 3:
            continue
        h = int(weighted_class_number(-s) * (6 if s == 3 else 2))
        assert h % 2 == 1
        for ell in primes:
            if ell in (2, s):
                continue
            z = norm_generator(s, ell, h)
            if z is not None:
                factor = split_from_generator(n, (1 + s) // 4, z, odd_power)
                if factor is not None:
                    return factor
    return None


def replay():
    count = local_checks = 0
    for s in (3, 7, 11, 19, 23, 31, 47, 59, 71, 83):
        h = int(weighted_class_number(-s) * (6 if s == 3 else 2))
        for ell in primes_through(43):
            if ell in (2, s):
                continue
            value = norm_generator(s, ell, h)
            if value is None:
                assert pow(-s, (ell-1)//2, ell) == ell - 1
            else:
                a, b = value
                assert a*a + a*b + ((1+s)//4)*b*b == ell**h
                count += 1
                for p in primes_through(101):
                    if p in (2, s, ell):
                        continue
                    split = pow(-s, (p - 1)//2, p) == 1
                    order = p - 1 if split else p + 1
                    assert quotient_power(p, (1+s)//4, value, order//2) == (pow(ell, (p-1)//2, p), 0)
                    local_checks += 1
    z = norm_generator(23, 3, 3)
    assert split_from_generator(53*103, 6, z, smooth_exponent(53*103, 3)) == 53
    assert find_split(53*103, 3, 23) in (53, 103)
    assert find_split(101, 5, 19) is None
    assert find_split(53**2 * 103, 3, 23) in (53, 53**2, 103, 53*103)
    print(f"Checked {count} principal generators and {local_checks} local half powers. D=-23, ell=3, norm 27 splits 5459.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?")
    parser.add_argument("--bound", type=int, default=11, help="odd smoothness cutoff")
    parser.add_argument("--menu", type=int, default=31, help="maximum discriminant prime and split prime")
    args = parser.parse_args()
    if args.N is None:
        replay()
    else:
        try:
            divisor = find_split(args.N, args.bound, args.menu)
        except ValueError as error:
            parser.error(str(error))
        if divisor is None:
            print("No split in the specified menu.")
            raise SystemExit(1)
        print(f"{args.N} = {divisor} * {args.N // divisor}")
