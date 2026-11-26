#!/usr/bin/env python3
"""Generate high rational arguments on twists of the four-mark quartic."""

import argparse
import json
import sys
from fractions import Fraction
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).parent
REPAIR = run_path(str(HERE / "cogentic-projective-unit-chart.py"))
SATURATION = run_path(str(HERE / "cogentic-elliptic-local-saturation.py"))
repair = REPAIR["repair"]
primes_through = SATURATION["primes_through"]
smooth_exponent = SATURATION["smooth_exponent"]
MARKS = REPAIR["MARKS"]
C0 = prod(MARKS[0]-root for root in MARKS[1:])
SEEDS = tuple(map(Fraction, (3, 4, 5, 7, 15, "3/2")))


def quartic(t):
    return prod(t-root for root in MARKS)


def twist(seed):
    seed = Fraction(seed)
    d = quartic(seed)
    if not d:
        raise ValueError("the seed must lie outside the four branch marks")
    scale = d*C0
    left, middle, right = (-scale/(1-root) for root in MARKS[1:])
    coefficients = -(left+middle+right), left*middle+left*right+middle*right
    return scale, coefficients, (scale/(seed-1), d*scale/(seed-1)**2)


def add(left, right, coefficients):
    if left is None:
        return right
    if right is None:
        return left
    x, y = left
    other_x, other_y = right
    a2, a4 = coefficients
    if x == other_x:
        if y == -other_y:
            return None
        slope = (3*x*x+2*a2*x+a4)/(2*y)
    else:
        slope = (other_y-y)/(other_x-x)
    next_x = slope*slope-a2-x-other_x
    return next_x, slope*(x-next_x)-y


def argument(scale, point):
    if point is None or not point[0] or not point[1]:
        return None
    return 1+scale/point[0]


def height_bits(t):
    return max(abs(t.numerator), t.denominator).bit_length()


def arguments(seed, count, minimum_bits=0, doublings=6):
    scale, coefficients, base = twist(seed)
    point, first = base, 1
    if minimum_bits:
        for step in range(doublings+1):
            t = argument(scale, point)
            if t is not None and height_bits(t) >= minimum_bits:
                break
            if step == doublings or point is None:
                return
            point = add(point, point, coefficients)
            first *= 2
    for multiple in range(first, first+count):
        t = argument(scale, point)
        if t is not None and height_bits(t) >= minimum_bits:
            yield multiple, t
        point = add(point, base, coefficients)


def multiplier_split(n, unit, exponent):
    residue = pow(unit, exponent, n)
    for _ in range(n.bit_length()+1):
        divisor = gcd(residue-1, n)
        if divisor > 1:
            return divisor if divisor < n else None
        residue = residue*residue % n
    return None


def search(n, degree=None, minimum_bits=0, count=8, doublings=6,
           trial_bound=13, smooth_bound=None):
    if n < 3 or minimum_bits < 0 or count < 1 or doublings < 0 or trial_bound < 2:
        raise ValueError("require N >= 3, positive count, trial bound >= 2 and nonnegative height and doublings")
    if degree is not None and (degree < 7 or degree % 4 != 3):
        raise ValueError("require degree at least 7 and congruent to 3 modulo 4")
    if smooth_bound is not None and smooth_bound < 1:
        raise ValueError("require a positive smoothness bound")
    for prime in primes_through(min(trial_bound, n-1)):
        if n % prime == 0:
            return {"status": "factor", "factor": prime, "source": "trial"}
    exponent = None if smooth_bound is None else smooth_exponent(n, smooth_bound)
    first_chart = None
    for seed in SEEDS:
        for multiple, t in arguments(seed, count, minimum_bits, doublings):
            result = repair(n, t.numerator, t.denominator, degree)
            if result["status"] == "obstructed":
                continue
            result.update(seed=str(seed), multiple=multiple, height_bits=height_bits(t))
            if result["status"] == "factor":
                return dict(result, source="chart gcd")
            if exponent is None:
                return result
            if first_chart is None:
                first_chart = result
            divisor = multiplier_split(n, result["unit"], exponent)
            if divisor is not None:
                return dict(result, status="factor", factor=divisor, source="smooth multiplier")
    return first_chart if first_chart is not None else {"status": "no-chart"}


def polynomial_product(left, right):
    result = [0]*(len(left)+len(right)-1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i+j] += a*b
    return result


def divisible_by_monic(coefficients, polynomial):
    while len(coefficients) >= len(polynomial):
        top = coefficients.pop()
        offset = len(coefficients)-len(polynomial)+1
        for i, coefficient in enumerate(polynomial[:-1]):
            coefficients[offset+i] -= top*coefficient
    return not any(coefficients)


def order_unit(left, right, quotient):
    left_derivative = [left[1], 2]
    right_derivative = [right[1], 2]
    result = polynomial_product(right_derivative, polynomial_product(left, quotient))
    for i, coefficient in enumerate(polynomial_product(right_derivative, left_derivative)):
        result[i] -= coefficient
    for i, coefficient in enumerate(left):
        result[i] -= 4*coefficient
    return result


def replay():
    for seed in SEEDS:
        for _, t in arguments(seed, 4):
            ratio = quartic(t)/quartic(seed)
            assert ratio > 0
            assert isqrt(ratio.numerator)**2 == ratio.numerator
            assert isqrt(ratio.denominator)**2 == ratio.denominator

    doubled, = arguments(Fraction(3), 1, minimum_bits=10)
    amplified, = arguments(Fraction(3), 1, minimum_bits=30)
    assert doubled == (2, Fraction(-2837, 23))
    multiple, t = amplified
    assert multiple == 4 and height_bits(t) == 42

    n = (2**61-1)*(2**31-1)
    chart = search(n, degree=7, minimum_bits=30, count=1)
    assert chart["status"] == "chart" and chart["multiple"] == 4
    assert Fraction(chart["numerator"], chart["denominator"]) == t
    polynomial, quotient = chart["polynomial"], chart["quotient"]
    assert polynomial[-1] == 1
    assert all(c % 5 == 0 for c in polynomial[:-1]) and polynomial[0] % 25
    assert max(map(abs, polynomial)) <= 30000 * max(abs(t.numerator), t.denominator)
    assert max(map(abs, polynomial)) < n
    evaluate = REPAIR["homogeneous_value"]
    assert evaluate(polynomial, t.numerator, t.denominator, n) == 0
    derivative = tuple(i*c for i, c in enumerate(polynomial) if i)
    assert gcd(evaluate(derivative, t.numerator, t.denominator, n), n) == 1

    left = [MARKS[0]*MARKS[1], -sum(MARKS[:2]), 1]
    right = [MARKS[2]*MARKS[3], -sum(MARKS[2:]), 1]
    unit = order_unit(left, right, quotient)
    inverse = order_unit(right, left, quotient)
    relation = polynomial_product(unit, inverse)
    relation[0] -= 1
    assert divisible_by_monic(relation, polynomial)
    fraction_relation = polynomial_product(unit, right)
    for i, coefficient in enumerate(left):
        fraction_relation[i] -= coefficient
    assert divisible_by_monic(fraction_relation, polynomial)
    residue = chart["evaluation"]
    assert evaluate(unit, residue, 1, n) == chart["unit"]
    exact_ratio = (t-MARKS[0])*(t-MARKS[1])/((t-MARKS[2])*(t-MARKS[3]))
    assert exact_ratio.numerator * pow(exact_ratio.denominator, -1, n) % n == chart["unit"]

    split = search(17*19, degree=7, minimum_bits=10, count=1, smooth_bound=3)
    assert split["status"] == "factor" and split["source"] == "smooth multiplier"
    assert split["multiple"] == 2 and split["factor"] == 19
    assert search(35) == {"status": "factor", "factor": 5, "source": "trial"}

    repaired = repair(17, -29, 2, 7)
    assert repaired["status"] == "chart"
    derivative = tuple(i*c for i, c in enumerate(repaired["polynomial"]) if i)
    assert evaluate(derivative, -29, 2, 17)
    assert repair(323, -49, 3, 7) == {"status": "factor", "factor": 19}
    print("Checked square classes on six twists and a degree-seven chart at a 42-bit argument from [4]P.")
    print("The unit at [2]P splits 323 = 17 * 19 with smooth bound 3.")


if __name__ == "__main__":
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?")
    parser.add_argument("--degree", type=int, help="repair degree, at least 7 and congruent to 3 modulo 4")
    parser.add_argument("--height-bits", type=int, default=0, help="minimum numerator or denominator bit length")
    parser.add_argument("--count", type=int, default=8, help="number of consecutive multiples per seed")
    parser.add_argument("--doublings", type=int, default=6, help="cap on doublings to reach the requested height")
    parser.add_argument("--trial-bound", type=int, default=13)
    parser.add_argument("--smooth-bound", type=int, help="try a smooth multiplier on each unit")
    args = parser.parse_args()
    if args.N is None:
        replay()
    else:
        try:
            result = search(args.N, degree=args.degree, minimum_bits=args.height_bits,
                            count=args.count, doublings=args.doublings, trial_bound=args.trial_bound,
                            smooth_bound=args.smooth_bound)
        except ValueError as error:
            parser.error(str(error))
        print(json.dumps(result))
