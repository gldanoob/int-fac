"""Exact finite checks for the crossing and prime-lift arguments."""

from fractions import Fraction
from itertools import product
from math import gcd, prod


def crossing_counts(h):
    # Shift every coordinate by 1/((h+1)D), keeping all subset sums off quarter endpoints.
    d = 2 ** (h + 1)
    sign = [1 if k < d // 4 or k >= 3 * d // 4 else -1 for k in range(d)]
    masks = range(1, 2**h - 1)
    highest = [(mask.bit_length() - 1, mask ^ (1 << (mask.bit_length() - 1))) for mask in masks]
    displacement = [(mask & 1) - ((mask >> 1) & 1) for mask in masks]
    condition_sums = [0] * d
    singles = odd = first = factorial_second = 0
    sums = [0] * (2**h - 1)
    for x in product(range(d), repeat=h):
        value = 1
        crossings = 0
        for mask, (i, prefix), delta in zip(masks, highest, displacement):
            k = (sums[prefix] + x[i]) % d
            sums[mask] = k
            value *= sign[k]
            if delta and sign[k] != sign[(k + delta) % d]:
                crossings += 1
        condition_sums[sum(x) % d] += value
        singles += crossings == 1
        odd += crossings % 2
        first += crossings
        factorial_second += crossings * (crossings - 1)
    population = d**h
    m = 2 ** (h - 1)
    assert Fraction(first, population) == Fraction(2*m, d)
    assert Fraction(factorial_second, population) == Fraction(4*m*(m-1), d**2)
    assert singles >= first - factorial_second >= population // 4
    # Project onto functions of the coordinate sum to measure all diagonal energy at once.
    off_diagonal = 1 - Fraction(sum(s*s for s in condition_sums), d**(2*h - 1))
    assert off_diagonal >= Fraction(odd, population) >= Fraction(1, 4)
    print(f"h={h}, points={population}, single={Fraction(singles,population)}, "
          f"odd={Fraction(odd,population)}, off_diagonal={off_diagonal}")


def wave(k, n):
    return 1 if 4 * min(k % n, -k % n) < n else -1


def literal_lifts():
    checks = 0
    for blocks in ((5, 7), (3, 5, 7), (9, 5, 11), (3, 5, 7, 11),
                   (9, 5, 7, 13), (3, 5, 7, 11, 13), (3, 5, 7, 11, 13, 17)):
        n = prod(blocks)
        idempotents = [(n // d) * pow(n // d, -1, d) for d in blocks]
        for ell in (5, 7, 11, 13, 17, 19, 23, 29):
            if gcd(ell, n) != 1:
                continue
            a = pow(ell, -1, n)
            modulus = n * ell
            quarter = sum((x*x-1) % modulus == 0 for x in range(1, modulus//4 + 1))
            corrected = (-1) ** ((quarter - 1 - (wave(2*a, n) == 1)) % 2)
            hidden = 1
            for flags in product((0, 1), repeat=len(blocks)):
                if 0 < sum(flags) < len(flags):
                    hidden *= wave(2*a*sum(v*e for v, e in zip(flags, idempotents)), n)
            assert hidden == corrected
            checks += 1
    print(f"{checks} literal prime lifts, two through six prime-power blocks")


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O to enable the checks')
    for h in range(2, 5):
        crossing_counts(h)
    literal_lifts()
