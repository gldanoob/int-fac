"""Exact finite controls for the odd restriction in Harman's interval sieve."""

from fractions import Fraction
from math import isqrt


def sign_surd(a, b, p):
    """Sign of a + b*sqrt(p) from integer comparisons."""
    if b == 0:
        return (a > 0) - (a < 0)
    if b < 0:
        return -sign_surd(-a, -b, p)
    if a >= 0:
        return 1
    return (b * b * p > a * a) - (b * b * p < a * a)


def central_endpoints():
    selected = 0
    all_scales = 0
    for p in range(2, 4097):
        # x = (p + 1 - sqrt(p))/4. Check x < s <= x + sqrt(x).
        radius = isqrt(p) + 2
        for s in range(max(1, p // 4 - radius), p // 4 + radius + 1):
            a = 4 * s - p - 1
            inside = (sign_surd(a, 1, p) > 0
                      and sign_surd(a * a - 3 * p - 4, 2 * a + 4, p) <= 0)
            if inside:
                assert a * a <= p
                selected += 1
        all_scales += 1
    assert (4 * Fraction(31, 200)) ** 2 * Fraction(8, 3) > 1
    return all_scales, selected


def parity_transfers():
    checked = 0
    for x in range(65, 356, 11):
        for y in (isqrt(x), x):
            for d in range(1, 48):
                for first in (1, 2, 4, 8, 16, 32):
                    stop = 2 * first
                    full = sum(x < d * m <= x + y for m in range(first, stop))
                    odd = sum(x < d * m <= x + y for m in range(first, stop) if m % 2)
                    half = sum(x < 2 * d * v <= x + y
                               for v in range((first + 1) // 2, (stop + 1) // 2))
                    assert odd == full - half
                    assert abs(2 * odd - full) <= 1
                    checked += 1
    return checked


def harmonic_checks():
    sums = [Fraction(0)]
    for v in range(1, 251):
        sums.append(sums[-1] + Fraction(1 if v % 2 else -1, v))
    checked = 0
    for a in range(1, 251):
        for b in range(a, 251):
            assert abs(sums[b] - sums[a - 1]) <= Fraction(1, a)
            checked += 1
    return checked


if __name__ == "__main__":
    print("Hasse endpoint scales and selected integers", *central_endpoints())
    print("odd free-variable transfers", parity_transfers())
    print("alternating harmonic intervals", harmonic_checks())
