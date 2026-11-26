#!/usr/bin/env python3
"""Search small imaginary quadratic norm-one tori for a smooth local order."""

import argparse
from functools import cache
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).resolve().parent
weighted_class_number = run_path(str(HERE / "untwisted-legendre-traces.py"))["weighted_order_class_number"]
saturation = run_path(str(HERE / "cogentic-elliptic-local-saturation.py"))
smooth_exponent = saturation["smooth_exponent"]
primes_through = saturation["primes_through"]
FactorFound, checked_gcd = (saturation[name] for name in ("FactorFound", "checked_gcd"))
IDENTITY = (1, 0)


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


def power(value, exponent, k, n):
    result = IDENTITY
    for bit in bin(exponent)[2:]:
        result = multiply(result, result, k, n)
        if bit == "1":
            result = multiply(result, value, k, n)
    return result


def quotient_power(n, k, z, exponent):
    a, b = z
    norm = a*a + a*b + k*b*b
    inverse = pow(norm, -1, n)
    value = tuple(c*inverse % n for c in multiply(z, z, k, n))
    return power(value, exponent, k, n)


def height_split(n, k, value):
    for _ in range((4*n).bit_length() + 1):
        divisor = gcd(n, value[0] - 1, value[1])
        if divisor > 1:
            return divisor if divisor < n else None
        value = multiply(value, value, k, n)
    return None


@cache
def collision_checker():
    try:
        return run_path(str(HERE / "cogentic-unit-collision-search.py"))["tuple_collision"]
    except ModuleNotFoundError as error:
        if error.name == "sage":
            raise ValueError("residual-order search requires SageMath Python") from error
        raise


def batch_match(modulus, giant_labels, baby_labels):
    """Expose a proper gcd or return the indices of a global scalar match."""
    hit = collision_checker()(modulus, ((x,) for x in giant_labels), ((x,) for x in baby_labels))
    if hit is None:
        return None
    if hit["status"] == "local-split":
        raise FactorFound(hit["factor"])
    return hit["left_index"], hit["right_index"]


def trace(value, n):
    return (2*value[0] + value[1]) % n


def signed_multiple(left, right, i, j, n):
    # At each good prime, equal traces on norm-one elements mean equality or inversion.
    assert i != j
    a, b = left
    c, d = right
    same = checked_gcd(gcd(a - c, b - d), n)
    inverse = checked_gcd(gcd(a - c - d, b + d), n)
    if same == n:
        return abs(i - j)
    assert inverse == n
    return i + j


def bounded_multiple(n, k, value, bound):
    """Return a global multiple or None, or raise FactorFound for a proper gcd."""
    # A local order r <= bound can be written j*width - i inside these lists.
    width = isqrt(bound - 1) + 1
    babies = []
    baby = IDENTITY
    for _ in range(width):
        babies.append(baby)
        baby = multiply(baby, value, k, n)

    giants = []
    step, giant = baby, IDENTITY
    for j in range(1, (bound + width - 1)//width + 1):
        giant = multiply(giant, step, k, n)
        if checked_gcd(gcd(giant[0] - 1, giant[1]), n) == n:
            return j*width
        giants.append(giant)

    if width == 1:
        return None
    hit = batch_match(n, (trace(x, n) for x in giants), (trace(x, n) for x in babies))
    if hit is None:
        return None
    j, i = hit
    return signed_multiple(giants[j], babies[i], (j+1)*width, i, n)


def split_from_generator(n, k, z, odd_power, residual_order=None):
    value = quotient_power(n, k, z, odd_power)
    divisor = height_split(n, k, value)
    if divisor is not None or residual_order is None:
        return divisor
    # Reduction from a good prime power to its residue field has odd-order kernel.
    projected = power(value, 1 << (4*n).bit_length(), k, n)
    try:
        relation = bounded_multiple(n, k, projected, residual_order)
    except FactorFound as found:
        return found.args[0]
    if relation is None:
        return None
    odd_relation = relation // (relation & -relation)
    return height_split(n, k, power(value, odd_relation, k, n))


def find_split(n, smooth_bound, menu_bound, residual_order=None):
    if n < 3 or n % 2 == 0 or smooth_bound < 1 or menu_bound < 3:
        raise ValueError("expected odd N >= 3, positive smooth bound and menu bound >= 3")
    if residual_order is not None and residual_order < 1:
        raise ValueError("residual order bound must be positive")
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
                factor = split_from_generator(n, (1 + s) // 4, z, odd_power, residual_order)
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


def replay_stage_two():
    z = norm_generator(3, 7, 1)
    for n in (13*17, 13*47, 13**2*17, 13**2*47):
        assert find_split(n, 1, 7) is None
        assert find_split(n, 1, 7, 1) is None
        divisor = find_split(n, 1, 7, 3)
        assert 1 < divisor < n and n % divisor == 0
    assert find_split(101, 1, 7, 3) is None

    n = 13*47
    projected = quotient_power(n, 1, z, 1 << (4*n).bit_length())
    assert power(projected, 2, 1, n) != projected and power(projected, 3, 1, n) == IDENTITY
    assert bounded_multiple(n, 1, projected, 3) == 3
    assert height_split(n, 1, quotient_power(n, 1, z, 3)) == 13

    n = 29*31
    z = norm_generator(23, 3, 3)
    odd = smooth_exponent(n, 3)
    projected = quotient_power(n, 6, z, odd << (4*n).bit_length())
    giant_trace = trace(power(projected, 4, 6, n), n)
    differences = [giant_trace - trace(power(projected, i, 6, n), n) for i in range(4)]
    assert all(difference % n for difference in differences)
    assert gcd(prod(differences), n) == n
    assert split_from_generator(n, 6, z, odd) is None
    assert split_from_generator(n, 6, z, odd, 10) == 31

    n = 13**2*47
    z = norm_generator(3, 7, 1)
    projected = quotient_power(n, 1, z, 1 << (4*n).bit_length())
    assert projected != IDENTITY and trace(power(projected, 3, 1, n), n) == 2
    assert split_from_generator(n, 1, z, 1, 10) == 13*47
    print("Stage two split 221 by trace and 611 by a saved odd multiple.")
    print("Saturated products, mixed identity at a repeated prime, and prime input passed.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?")
    parser.add_argument("--bound", type=int, default=11, help="odd smoothness cutoff")
    parser.add_argument("--menu", type=int, default=31, help="maximum discriminant prime and split prime")
    parser.add_argument("--residual-order", metavar="D", type=int, help="stage-two odd order bound (requires SageMath)")
    parser.add_argument("--replay-stage-two", action="store_true", help="run the stage-two replay (requires SageMath)")
    args = parser.parse_args()
    if args.replay_stage_two:
        if args.N is not None or args.residual_order is not None:
            parser.error("--replay-stage-two does not take N or --residual-order")
        try:
            replay_stage_two()
        except ValueError as error:
            parser.error(str(error))
    elif args.N is None:
        if args.residual_order is not None:
            parser.error("--residual-order requires N")
        replay()
    else:
        try:
            divisor = find_split(args.N, args.bound, args.menu, args.residual_order)
        except ValueError as error:
            parser.error(str(error))
        if divisor is None:
            print("No split in the specified menu.")
            raise SystemExit(1)
        print(f"{args.N} = {divisor} * {args.N // divisor}")
