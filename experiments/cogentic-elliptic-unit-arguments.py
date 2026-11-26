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
    seen = set()
    while minimum_bits:
        t = argument(scale, point)
        if t is not None and height_bits(t) >= minimum_bits:
            break
        if point is None or point in seen or (doublings is not None and len(seen) == doublings):
            return
        seen.add(point)
        point = add(point, point, coefficients)
        first *= 2
    stop = 8*first+1 if count is None else first+count
    for multiple in range(first, stop):
        t = argument(scale, point)
        if t is not None and (count is None or height_bits(t) >= minimum_bits):
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


def rational_seeds(limit):
    for denominator in range(1, (limit-1)//14+1):
        for numerator in range(14*denominator+1, limit+1):
            if gcd(numerator, denominator) == 1:
                yield Fraction(numerator, denominator)


def charts(n, *, degree=None, minimum_bits=None, count=8, doublings=None,
           trial_bound=13, seed_height=None, partner=False):
    """Yield distinct charts, or a proper factor when a guard finds one."""
    if n < 3 or count < 1 or trial_bound < 2:
        raise ValueError("require N >= 3, positive count and trial bound >= 2")
    if (minimum_bits is not None and minimum_bits < 0) or (doublings is not None and doublings < 0):
        raise ValueError("require nonnegative height and doublings")
    if degree is not None and (degree < 7 or degree % 4 != 3):
        raise ValueError("require degree at least 7 and congruent to 3 modulo 4")
    seeds = SEEDS
    if seed_height is not None:
        if seed_height < 15:
            raise ValueError("require seed height at least 15")
        seeds = rational_seeds(seed_height)
        trial_bound = max(trial_bound, 2*seed_height)
        count = None
        if minimum_bits is None:
            b = n.bit_length()
            # Round (b^2 log_2 b)^(1/3) up to a nearby power of two.
            size = (b*b*b.bit_length()).bit_length()
            minimum_bits = 1 << ((size+2)//3)
    else:
        doublings = 6 if doublings is None else doublings
        minimum_bits = 0 if minimum_bits is None else minimum_bits

    for prime in primes_through(min(trial_bound, n-1)):
        if n % prime == 0:
            yield {"status": "factor", "factor": prime, "source": "trial"}
            return
    seen = set()
    for seed in seeds:
        for multiple, t in arguments(seed, count, minimum_bits, doublings):
            if t in seen:
                continue
            seen.add(t)
            result = repair(n, t.numerator, t.denominator, degree)
            if result["status"] == "obstructed":
                continue
            if result["status"] == "chart" and partner:
                other = repair(n, t.numerator, t.denominator, result["degree"]+4)
                if other["status"] != "chart":
                    result = other
                    if result["status"] == "obstructed":
                        continue
                else:
                    result["partner_polynomial"] = other["polynomial"]
                    result["partner_degree"] = other["degree"]
            result.update(seed=str(seed), multiple=multiple, height_bits=height_bits(t))
            if result["status"] == "factor":
                yield dict(result, source="chart gcd")
                return
            yield result


def search(n, *, smooth_bound=None, **options):
    if smooth_bound is not None and smooth_bound < 1:
        raise ValueError("require a positive smoothness bound")
    exponent = first_chart = None
    for result in charts(n, **options):
        if result["status"] == "factor" or smooth_bound is None:
            return result
        if first_chart is None:
            first_chart = result
            exponent = smooth_exponent(n, smooth_bound)
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

    assert list(rational_seeds(30))[-1] == Fraction(29, 2)
    menu = list(charts(2**61-1, seed_height=15, degree=7, partner=True))
    assert {entry["status"] for entry in menu} == {"chart"}
    first = menu[0]["multiple"]
    assert first == 4 and {entry["multiple"] for entry in menu} == set(range(first, 8*first+1))
    assert len({(entry["numerator"], entry["denominator"]) for entry in menu}) == len(menu)
    for entry in menu:
        A, B = entry["numerator"], entry["denominator"]
        other = entry["partner_polynomial"]
        assert entry["partner_degree"] == 11 and len(other) == 12
        assert evaluate(other, A, B, 2**61-1) == 0
        assert evaluate(tuple(i*c for i, c in enumerate(other) if i), A, B, 2**61-1)
    assert list(charts(17*19, seed_height=15)) == [{"status": "factor", "factor": 17, "source": "trial"}]
    options = dict(seed_height=15, minimum_bits=10, degree=7)
    first_chart = next(charts(31*83, **options))
    assert first_chart["multiple"] == 2
    assert multiplier_split(31*83, first_chart["unit"], smooth_exponent(31*83, 3)) is None
    later_split = search(31*83, smooth_bound=3, **options)
    assert later_split["source"] == "smooth multiplier"
    assert later_split["multiple"] == 3 and later_split["factor"] == 83
    print("Checked square classes on six twists and a degree-seven chart at a 42-bit argument from [4]P.")
    print("The unit at [2]P splits 323 = 17 * 19 with smooth bound 3.")
    print(f"The theorem menu checks {len(menu)} distinct paired charts at indices {first} through {8*first}.")


if __name__ == "__main__":
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?")
    parser.add_argument("--degree", type=int, help="repair degree, at least 7 and congruent to 3 modulo 4")
    parser.add_argument("--height-bits", type=int, help="minimum bit length (theorem menu defaults to the V scale)")
    parser.add_argument("--count", type=int, default=8, help="consecutive multiples per seed in the fixed demo")
    parser.add_argument("--doublings", type=int, help="cap on doublings (default six in the fixed demo)")
    parser.add_argument("--trial-bound", type=int, default=13)
    parser.add_argument("--smooth-bound", type=int, help="try a smooth multiplier on each unit")
    parser.add_argument("--seed-height", type=int, help="stream the public rational seed menu up to this height")
    parser.add_argument("--partner", action="store_true", help="also repair a chart of degree four higher")
    args = parser.parse_args()
    if args.N is None:
        replay()
    else:
        options = dict(degree=args.degree, minimum_bits=args.height_bits, count=args.count,
                       doublings=args.doublings, trial_bound=args.trial_bound,
                       seed_height=args.seed_height, partner=args.partner)
        try:
            if args.seed_height is not None and args.smooth_bound is None:
                results = charts(args.N, **options)
                first = next(results, {"status": "no-chart"})
                print(json.dumps(first))
                for result in results:
                    print(json.dumps(result))
            else:
                print(json.dumps(search(args.N, smooth_bound=args.smooth_bound, **options)))
        except ValueError as error:
            parser.error(str(error))
