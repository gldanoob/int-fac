"""Compare the exact Legendre trace counts with automorphism-weighted class numbers."""

from collections import Counter
from fractions import Fraction
from functools import cache
from math import gcd, isqrt


@cache
def weighted_order_class_number(discriminant):
    classes = 0
    for a in range(1, isqrt(-discriminant // 3) + 1):
        for b in range(-a, a + 1):
            c, remainder = divmod(b * b - discriminant, 4 * a)
            if remainder or a > c or gcd(a, gcd(b, c)) != 1:
                continue
            if b < 0 and (abs(b) == a or a == c):
                continue
            classes += 1
    units = {-3: 6, -4: 4}.get(discriminant, 2)
    return Fraction(classes, units)


@cache
def mass(discriminant):
    total = Fraction(0)
    for f in range(1, isqrt(-discriminant) + 1):
        d, remainder = divmod(discriminant, f * f)
        if remainder == 0 and d % 4 in (0, 1):
            total += weighted_order_class_number(d)
    return total


def test_traces():
    fields = parameters = traces = equalities = 0
    for p in range(5, 502, 2):
        if any(p % r == 0 for r in range(3, isqrt(p) + 1, 2)):
            continue
        fields += 1
        chi = [-1] * p
        chi[0] = 0
        for a in range(1, p):
            chi[a * a % p] = 1
        histogram = Counter()
        for lam in range(2, p):
            trace = -sum(chi[x * (x - 1) * (x - lam) % p] for x in range(p))
            histogram[trace] += 1
            parameters += 1
        for t in range(-isqrt(4 * p), isqrt(4 * p) + 1):
            if t == 0 or (p + 1 - t) % 8 != 4:
                continue
            d = t * t - 4 * p
            full = mass(d)
            full_two = mass(d // 4)
            assert histogram[t] == 2 * (full - full_two)
            assert full >= 2 * full_two
            equalities += full == 2 * full_two
            traces += 1
    return fields, parameters, traces, equalities


if __name__ == "__main__":
    print("prime fields, Legendre parameters, ordinary traces, equal mass cases",
          *test_traces())
