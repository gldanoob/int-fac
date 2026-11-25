"""Exact checks for the wider prime slots and the zero-density exponent margins."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import prod


def expanded_slots():
    primes = (29, 31, 37, 41, 43)
    # Positive numerator weights modeling bounded (log r)/w on a fixed relative log range.
    weights = {p: i % 3 + 1 for i, p in enumerate(primes)}
    refinements = tuples = 0
    for j in range(2, 7):
        split = j // 2
        coefficients = Counter()
        for chosen in product(primes, repeat=j - split):
            n = prod(chosen)
            coefficients[n] += prod(weights[r] for r in chosen)
            tuples += 1
        for n, numerator in coefficients.items():
            choices = sum(n % r == 0 for r in primes)
            assert 29 ** (j - split) <= n <= 43 ** (j - split)
            assert numerator <= (3 * choices) ** (j - split)
        direct = Counter()
        for chosen in product(primes, repeat=j):
            direct[prod(chosen)] += prod(weights[r] for r in chosen)
        rebuilt = Counter()
        for chosen in product(primes, repeat=split):
            extra, weight = prod(chosen), prod(weights[r] for r in chosen)
            for n, numerator in coefficients.items():
                rebuilt[extra * n] += weight * numerator
        assert rebuilt == direct
        refinements += len(direct)
    return tuples, refinements


def centered_sums():
    # An integer convolution with a symmetric, finite-variance probability law.
    base = {-2: 1, -1: 2, 0: 3, 1: 2, 2: 1}
    law = {0: 1}
    checks = 0
    for j in range(1, 65):
        updated = Counter()
        for x, mass in law.items():
            for z, weight in base.items():
                updated[x + z] += mass * weight
        law = updated
        assert sum(law.values()) == 9**j
        for k in (-1, 0, 1):
            assert 100 * j * law[k]**2 >= 9**(2 * j)
            checks += 1
    return checks


def budget():
    sigma0, sigma = Fraction(4, 5), Fraction(167, 200)
    xi, epsilon = Fraction(1, 200), Fraction(1, 100)
    a = 1 - xi - epsilon
    geometric_saving = a * (1 - sigma0) - xi
    assert a > max(Fraction(15, 16), Fraction(15, 17))
    assert geometric_saving == Fraction(24, 125)
    assert geometric_saving > 1 - sigma
    assert 1 - sigma - Fraction(31, 200) == Fraction(1, 100)
    return a - Fraction(15, 16), geometric_saving - (1 - sigma)


if __name__ == "__main__":
    print("partial tuples and full coefficients", *expanded_slots())
    print("central probability checks", centered_sums())
    print("density and squared-integral margins", *budget())
