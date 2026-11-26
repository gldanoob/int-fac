from fractions import Fraction
from itertools import combinations
from math import comb, gcd, isqrt, prod
from random import Random


def prime_band(cutoff):
    return tuple(
        p for p in range(isqrt(cutoff) + 1, cutoff + 1)
        if all(p % d for d in range(2, isqrt(p) + 1))
    )


def piece_bound(low, length, primes):
    minimum_factors, largest_product = 0, 1
    while largest_product < low:
        minimum_factors += 1
        largest_product *= primes[-minimum_factors]

    coefficients = [1] + [0] * minimum_factors
    for prime in primes:
        for m in range(minimum_factors, 0, -1):
            coefficients[m] = prime * coefficients[m] + coefficients[m - 1]
        coefficients[0] *= prime
    primorial = coefficients[0]
    bound = (Fraction(1), 0)
    for m in range(1, minimum_factors + 1):
        numerator = length * coefficients[m] + primorial * comb(len(primes), m)
        denominator = primorial * length * comb(minimum_factors, m)
        bound = min(bound, (Fraction(numerator, denominator), m))
    return bound


def upper_count(start, step, length, primes):
    primorial = prod(primes)
    if step == 0:
        return length if start and primorial % abs(start) == 0 else 0
    common = gcd(start, step)
    if primorial % common:
        return 0
    start, step = start // common, step // common
    primes = tuple(p for p in primes if common % p and step % p)
    primorial = prod(primes)
    if step < 0:
        start += (length - 1) * step
        step = -step

    bound = 0
    for first in (start, -start - (length - 1) * step):
        left = max(0, (step - first) // step)
        right = min(length - 1, (primorial - first) // step)
        if left <= right:
            size = right - left + 1
            bound += size * piece_bound(first + left * step, size, primes)[0]
    return bound


def main():
    rng = Random(9472)
    band = prime_band(31)
    cases = [(5, 5, 80, band), (25, 25, 80, band), (0, 5, 80, band),
             (1, 0, 10, ()), (0, 0, 10, ()), (7 * 11, -7, 30, band)]
    cases.extend(
        (rng.randrange(-500, 500), rng.randrange(-30, 31), rng.randrange(1, 150),
         tuple(p for p in band if rng.randrange(4)))
        for _ in range(2500)
    )
    strict_nontrivial = 0
    for start, step, length, primes in cases:
        values = (start + step * j for j in range(length))
        primorial = prod(primes)
        direct = sum(bool(v) and primorial % abs(v) == 0 for v in values)
        bound = upper_count(start, step, length, primes)
        assert direct <= bound <= length
        strict_nontrivial += 0 < direct < bound < length
    assert strict_nontrivial > 100

    for low in (1, 10, 100, 1000, 10000):
        k = next(k for k in range(len(band) + 1) if prod(band[len(band) - k:]) >= low)
        expected = (Fraction(1), 0)
        for m in range(1, k + 1):
            symmetric = sum(Fraction(1, prod(ps)) for ps in combinations(band, m))
            expected = min(expected, ((symmetric + Fraction(comb(len(band), m), 47))
                                      / comb(k, m), m))
        assert piece_bound(low, 47, band) == expected

    primes = prime_band(997)
    primorial = prod(primes)
    step, length = 1 << 240, 1 << 160
    high = prod(primes[-60:])
    low = high - step * (length - 1)
    bound, moment = piece_bound(low, length, primes)
    assert primorial % high == 0 and high > length**2
    assert upper_count(low, step, length, primes) == bound * length
    assert upper_count(-low, -step, length, primes) == bound * length
    assert moment == 20 and Fraction(1, 1 << 129) < bound < Fraction(1, 1 << 128)
    assert 37 in primes and pow(37, 1 << 238, step) == 1 and pow(37, 1 << 237, step) != 1
    residue = primorial * pow(high, -1, step) % step
    complementary = (primorial // low - residue) // step
    complementary -= ((primorial - 1) // high - residue) // step
    assert high.bit_length() == 577 and complementary.bit_length() == 349
    assert (high // (step * length)).bit_length() == 177
    print(f"{len(cases)} exact-count comparisons ({strict_nontrivial} strict positive bounds)")
    print("2^160-member progression certified below 2^-128 at moment 20")


if __name__ == "__main__":
    main()
