"""Check finite multiplicities, truncation and constants for the integer factors."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import prod


def omega(n):
    count = 0
    p = 2
    while p * p <= n:
        while n % p == 0:
            count += 1
            n //= p
        p += 1
    return count + (n > 1)


def coefficients():
    primes = (3, 5, 7, 11)
    peak = atoms = collisions = 0
    for z, slots, cap in ((8, 3, 2), (16, 3, 2), (24, 2, 3)):
        odds = [r for r in range(z + 1, 2 * z + 1, 2)]
        allowed = [r for r in odds if omega(r) <= cap]
        moment = sum(Fraction(3, 2) ** omega(r) for r in odds)
        assert len(odds) - len(allowed) <= moment / Fraction(3, 2) ** cap
        assert min(allowed) >= z + 1
        assert sum(Fraction(1, len(allowed)) for r in allowed) == 1
        cofactors = Counter(prod(chosen) for chosen in product(allowed, repeat=slots))
        for v, multiplicity in cofactors.items():
            assert omega(v) <= slots * cap
            assert multiplicity <= slots ** omega(v)
        j = 3
        direct = Counter()
        for chosen in product(primes, repeat=j):
            part = prod(chosen)
            for v, multiplicity in cofactors.items():
                direct[part * v] += multiplicity
        assert sum(direct.values()) == len(primes)**j * len(allowed)**slots
        for n, multiplicity in direct.items():
            prime_options = sum(n % p == 0 for p in primes)
            assert multiplicity <= prime_options**j * slots**(cap * slots)
            peak = max(peak, multiplicity)
            collisions += multiplicity > 1
        atoms += len(direct)
    return atoms, collisions, peak


def constants():
    # e^4>1+4+8+64/6+256/24+1024/120>4*10.463.
    exp4_lower = sum(Fraction(4**k, factorial) for k, factorial in
                     enumerate((1, 1, 2, 6, 24, 120)))
    assert exp4_lower > 4 * Fraction(10463, 1000)
    c = 16
    ford = Fraction(c**3, 2) / Fraction(13366, 100)
    assert ford > 4
    # log 2>1/2, log(3/2)>1/3 by integrating 1/x.
    assert 100 * Fraction(1, 2) > 20 + 1
    assert 100 * Fraction(1, 3) > Fraction(3, 2) + 10
    return ford


if __name__ == "__main__":
    print("distinct products, collisions, peak multiplicity", *coefficients())
    print("limiting Ford exponent at C=16", constants())
