#!/usr/bin/env python3
"""Repair a four-mark unit chart at a prescribed rational evaluation."""

import argparse
import json
from math import gcd, prod

MARKS = (1, 2, 13, 14)
W = (364, -600, 265, -30, 1)
DERIVATIVE = tuple(i * W[i] for i in range(1, len(W)))


def homogeneous_value(coefficients, A, B, n):
    """Evaluate B^degree P(A/B) modulo n for ascending coefficients."""
    value = 0
    b_power = 1
    for coefficient in reversed(coefficients):
        value = (A * value + b_power * coefficient) % n
        b_power = b_power * B % n
    return value


def _digits(target, A, B, length):
    digits = [0] * length
    peel_constant = abs(A) >= B
    large, small = (A, B) if peel_constant else (B, A)
    radix = abs(large)
    for remaining in range(length - 1, 0, -1):
        if radix == 1:
            digit = 0
        else:
            digit = target * pow(pow(small, remaining, radix), -1, radix) % radix
            if 2 * digit > radix:
                digit -= radix
        index = length - 1 - remaining if peel_constant else remaining
        digits[index] = digit
        target = (target - digit * small**remaining) // large
    digits[-1 if peel_constant else 0] = target
    return digits


def repair(n, A, B, d=None):
    """Return a chart with ascending coefficients, a proper factor, or a chart obstruction."""
    if n < 3 or B == 0 or gcd(A, B) != 1:
        raise ValueError("require modulus at least 3 and a reduced rational argument")
    if d is not None and (d < 7 or d % 4 != 3):
        raise ValueError("require degree at least 7 and congruent to 3 modulo 4")
    if B < 0:
        A, B = -A, -B

    differences = [A - a * B for a in MARKS]
    # Removing these primes also ensures that the four marks remain distinct.
    divisors = [gcd(n, x) for x in (2, 3, 5, 7, 11, 13, B, *differences)]
    for divisor in divisors:
        if 1 < divisor < n:
            return {"status": "factor", "factor": divisor}
    if n in divisors:
        return {"status": "obstructed"}

    if d is None:
        height = max(abs(A), B)
        if height == 1:
            d = 7
        else:
            # Start from a lower bound on the needed degree.
            lower = (n.bit_length() - 1) // height.bit_length()
            d = max(7, lower + (3 - lower) % 4)
            capacity = height**d
            step = height**4
            while capacity < n:
                d += 4
                capacity *= step

    k = d - 4
    quotient = [0] * (k + 1)
    for i in range(3, k + 1, 4):
        quotient[i] = 1
    if DERIVATIVE[0] % 25 == 0:
        quotient[0] = 5

    w_value = prod(differences) % n
    base_value = (
        w_value * homogeneous_value(quotient, A, B, n)
        - pow(B, d - 3, n) * homogeneous_value(DERIVATIVE, A, B, n)
    )
    target = -base_value * pow(25 * B * w_value, -1, n) % n
    if 2 * target > n:
        target -= n
    for i, digit in enumerate(_digits(target, A, B, k)):
        quotient[i] += 25 * digit

    polynomial = [0] * (d + 1)
    for i, coefficient in enumerate(DERIVATIVE):
        polynomial[i] = -coefficient
    for i, coefficient in enumerate(quotient):
        for j, w_coefficient in enumerate(W):
            polynomial[i + j] += coefficient * w_coefficient
    slope = tuple(i * polynomial[i] for i in range(1, len(polynomial)))
    common = gcd(homogeneous_value(slope, A, B, n), n)
    if 1 < common < n:
        return {"status": "factor", "factor": common}
    if common == n:
        # Adding 25(BX-A)W keeps the same root and changes the derivative by a unit.
        quotient[0] -= 25*A
        quotient[1] += 25*B
        for i, w_coefficient in enumerate(W):
            polynomial[i] -= 25*A*w_coefficient
            polynomial[i+1] += 25*B*w_coefficient
        slope = tuple(i * polynomial[i] for i in range(1, len(polynomial)))
        assert gcd(homogeneous_value(slope, A, B, n), n) == 1
    check = homogeneous_value(polynomial, A, B, n)
    assert check == 0 and polynomial[-1] == 1
    assert all(coefficient % 5 == 0 for coefficient in polynomial[:-1])
    assert polynomial[0] % 25 != 0

    return {
        "status": "chart",
        "degree": d,
        "numerator": A,
        "denominator": B,
        "polynomial": tuple(polynomial),
        "quotient": tuple(quotient),
        "homogeneous_value_mod_n": check,
        "evaluation": A * pow(B, -1, n) % n,
        "unit": prod(differences[:2]) * pow(prod(differences[2:]), -1, n) % n,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int)
    parser.add_argument("A", type=int)
    parser.add_argument("B", type=int)
    parser.add_argument("--degree", type=int)
    args = parser.parse_args()
    try:
        print(json.dumps(repair(args.N, args.A, args.B, args.degree)))
    except ValueError as error:
        parser.error(str(error))
