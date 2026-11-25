"""Finite smooth-count, Fejér-kernel and exponent checks for longer integer factors."""

from cmath import exp
from fractions import Fraction
from math import ceil, pi


def largest_prime_factors(limit):
    factors = [0] * (limit + 1)
    for p in range(2, limit + 1):
        if factors[p] == 0:
            for n in range(p, limit + 1, p):
                factors[n] = p
    return factors


def smooth_counts():
    factors = largest_prime_factors(10000)
    comparisons = 0
    for y in (3, 7, 13, 31, 61):
        prefix = [0]
        for p in factors[1:]:
            prefix.append(prefix[-1] + (p <= y))
        for z in range(10, 5001, 78):
            direct = sum(factors[r] <= y for r in range(z + 1, 2 * z, 2))
            assert direct == prefix[2 * z] - 2 * prefix[z] + prefix[z // 2]
            comparisons += 1
    return comparisons


def phase_arcs():
    # On each equally spaced circle the first h moments vanish exactly for h<n.
    # These arc counts use pi>3 and a half-step grid to majorize all centers.
    checks = 0
    for n in (1024, 2048):
        for denominator in (2, 4, 8):
            density = Fraction(1, denominator)
            h = ceil(100 / density)
            assert h < n
            # Every arc of angular radius 1/h has length < n/(3h) grid steps.
            largest_arc = n // (3 * h) + 1
            assert Fraction(largest_arc, n) <= density / 25
            for start in range(0, n, 127):
                phases = [exp(2j * pi * k / n) for k in range(start, start + n // denominator)]
                # Contiguous arcs maximize the real part in a fixed direction.
                assert abs(sum(phases) / len(phases)) < 1 - float(density**2 / 100000)
                checks += 1
    return checks


def exponents():
    kappa = Fraction(1, 1000)
    density_exp = Fraction(1, 200)
    slots_exp = Fraction(1, 50)
    assert kappa < density_exp
    assert slots_exp - 2 * density_exp == Fraction(1, 100)
    assert slots_exp + Fraction(2, 3) < 1
    assert slots_exp < Fraction(1, 3)
    assert 4 * (16000 * kappa)**3 / Fraction(13366, 100) > 2


if __name__ == "__main__":
    print("odd smooth-count identities", smooth_counts())
    print("phase concentration checks", phase_arcs())
    exponents()
