#!/usr/bin/env python3
"""Check the residue accounting and the rectangle bound by exact arithmetic."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb, gcd, isqrt, prod


def primes_through(limit):
    sieve = bytearray(b'\1') * (limit + 1)
    sieve[:2] = b'\0\0'
    for prime in range(2, isqrt(limit) + 1):
        if sieve[prime]:
            start = prime * prime
            sieve[start::prime] = b'\0' * ((limit - start) // prime + 1)
    return [prime for prime, present in enumerate(sieve) if present]


def check_harmonic_budget(modulus, exponent, primes):
    window = 1 << exponent
    budget = (window * modulus).bit_length()
    offsets = [(prime, (prime * pow(prime, -1, modulus) - 1) // modulus)
               for prime in primes]
    for frequency in range(1, modulus):
        counts = Counter()
        for prime, offset in offsets:
            half = prime // 2
            residue = (frequency * offset + half) % prime - half
            value = frequency + residue * modulus
            assert 0 < abs(value) < window * modulus
            assert value % prime == 0
            counts[residue] += 1
        assert sum(counts.values()) == len(primes)
        assert all(exponent * count < budget for count in counts.values())
        harmonic = sum(Fraction(2 * count, 1 + abs(residue))
                       for residue, count in counts.items())
        assert harmonic * exponent <= (2 + 4 * exponent) * budget
    return modulus - 1


def evaluation_matrix(modulus, a, b, weighted_draws):
    matrix = [[0] * modulus for _ in range(modulus)]
    for x, y, weight in weighted_draws:
        matrix[(x + a * y) % modulus][(x + b * y) % modulus] += weight
    return matrix


def rectangle_discrepancy(matrix):
    modulus = len(matrix)
    total = sum(map(sum, matrix))
    centered = [[modulus ** 2 * entry - total for entry in row]
                for row in matrix]
    discrepancy = 0
    for size in range(1, modulus + 1):
        for rows in combinations(centered, size):
            sums = list(map(sum, zip(*rows)))
            positive = sum(value for value in sums if value > 0)
            negative = sum(-value for value in sums if value < 0)
            discrepancy = max(discrepancy, positive, negative)
    return Fraction(discrepancy, total * modulus ** 2)


def check_rectangle_bound(modulus):
    draws = list(product(range(modulus), repeat=2))
    a, b = 1, 2
    uniform = evaluation_matrix(modulus, a, b, ((x, y, 1) for x, y in draws))
    assert all(entry == 1 for row in uniform for entry in row)
    count = 0
    for slopes in range(1, modulus + 1):
        for weighted in (False, True):
            points = ((x, y, 1 + (x + 3 * y) % 5 if weighted else 1)
                      for x, y in draws if y < slopes)
            matrix = evaluation_matrix(modulus, a, b, points)
            support = sum(entry > 0 for row in matrix for entry in row)
            assert support == modulus * slopes
            discrepancy = rectangle_discrepancy(matrix)
            if not weighted:
                assert discrepancy == 0 if slopes == modulus else discrepancy > 0
            if discrepancy <= Fraction(1, 4):
                # 7 bounds 4 sqrt(3), and the tested moduli are perfect squares.
                denom = 32 * (7 * discrepancy + Fraction(1, isqrt(modulus))) ** 2
                assert support * denom >= modulus
                if modulus == 4:
                    brute_force = max(
                        abs(sum(Fraction(matrix[i][j], sum(map(sum, matrix)))
                                - Fraction(1, modulus ** 2)
                                for i in range(modulus) for j in range(modulus)
                                if rows >> i & 1 and cols >> j & 1))
                        for rows, cols in product(range(1 << modulus), repeat=2)
                    )
                    assert discrepancy == brute_force
                count += 1
    return count


def check_common_intercept():
    modulus, width = 16, 8
    probabilities = [Fraction(1 + (x == 0), modulus + 1)
                     for x in range(modulus)]
    weighted_mass = []
    for x in range(width):
        mass = sum(probabilities[s] * probabilities[y1] * probabilities[y2]
                   for s, y1, y2 in product(range(modulus), repeat=3)
                   if (x + s) % modulus < width and y1 < width and y2 < width)
        weighted_mass.append(mass * Fraction(modulus, width) ** 4 / modulus)
    assert all(weight >= Fraction(1, 8 * width) for weight in weighted_mass)

    # Distinct box origins give distinct failed intercepts for the same toy score.
    origins = [32, 30, 27] + list(range(100, 161))
    failed = [{x for x in range(width) if origin + x == 32} for origin in origins]
    weighted_scores = [sum(weighted_mass[x] for x in target) for target in failed]
    for target, score in zip(failed, weighted_scores):
        assert Fraction(len(target), width) <= 8 * score
    rho = 8 * sum(weighted_scores) / len(origins)
    for size in (1, 2, 4, 8):
        per_intercept = [Fraction(sum(x in target for target in failed), len(origins))
                         for x in range(size)]
        expect_fail = sum(per_intercept) / size
        assert expect_fail <= rho * width / size
        if size ** 2 >= rho * width ** 2:
            assert expect_fail ** 2 <= rho
        if size >= 8 * rho * width:
            chance_bad = Fraction(sum(value > Fraction(1, 4)
                                      for value in per_intercept), size)
            assert chance_bad <= Fraction(1, 2)
    assert 8 * rho * width < width
    return len(origins)


def check_affine_line_obstruction(lines):
    band, mark_limit, width = 127, 64, 1 << 15
    modulus = prod(prime for _, _, prime in lines)
    mark = next(a for a in range(1, modulus + 1)
                if all((a + slope) % prime == 0 for _, slope, prime in lines))
    assert mark <= mark_limit
    step = 2 * 113 * (257 - mark)
    eligible = [prime for prime in primes_through(band)
                if prime > band // 2 and step % prime != 0]

    degree = 0
    while 4 * band ** (degree + 1) <= step * width:
        degree += 1
    buckets = {}
    for primes in combinations(eligible, degree):
        value = prod(primes)
        key = (1 << (value.bit_length() - 1), value % step)
        buckets.setdefault(key, []).append(value)
    (bottom, residue), values = max(buckets.items(), key=lambda entry: len(entry[1]))
    assert len(values) * (degree + 2) * step >= comb(len(eligible), degree)
    constant = next(residue + step * j for j in range(modulus)
                    if all((residue + step * (j + intercept)) % prime == 0
                           for intercept, _, prime in lines))
    assert constant * 4 < bottom and gcd(constant, step) == 1

    slope_count = width // mark_limit
    primorial = prod(prime for prime in primes_through(band) if prime ** 2 > band)
    for intercept, slope, _ in lines:
        for y in range(slope_count):
            x = intercept + slope * y
            assert 0 <= x < width
            assert primorial % (constant + step * (x + mark * y)) != 0

    witnesses = set()
    for value in values:
        for y in range(1 + bottom // (4 * mark_limit * step)):
            quotient, rem = divmod(value - constant, step)
            x = quotient - mark * y
            assert rem == 0 and 0 <= x < width and 0 <= y < slope_count
            assert primorial % (constant + step * (x + mark * y)) == 0
            witnesses.add((x, y))
    mass = Fraction(len(witnesses), width * slope_count)
    assert mass >= Fraction(comb(len(eligible), degree),
                            128 * (degree + 2) * band ** (degree + 2) * 2 ** degree)
    return len(lines) * slope_count, len(witnesses)


def check_dyadic_origin_obstruction():
    base, ell, width = 257, 11, 32
    intercept_origin, slope_origin = 45, 16
    lines = [(1, 0, 3), (2, 1, 5)]
    modulus = prod(prime for _, _, prime in lines)
    mark = next(a for a in range(1, modulus + 1)
                if all((a + slope) % prime == 0 for _, slope, prime in lines))
    step = 2 * ell * (mark - base)
    # These fixed polynomials agree at base and have identical local reductions.
    first = mark ** 2 + mark + 1
    second = first + step
    constants = [second + step * (intercept_origin + j * width + mark * slope_origin)
                 for j in range(2 * ell)]
    assert all((constant - second) % abs(step) == 0 for constant in constants)
    assert gcd(second, step) == 1
    constant = next(c for c in constants
                    if all((c + step * intercept) % prime == 0
                           for intercept, _, prime in lines))
    for intercept, slope, prime in lines:
        for y in range(width):
            x = intercept + slope * y
            if 0 <= x < width:
                assert (constant + step * (x + mark * y)) % prime == 0


def main():
    frequencies = 0
    for exponent in range(3, 11):
        window = 1 << exponent
        primes = [prime for prime in primes_through(2 * window) if prime > window]
        for modulus in (4, 16, 64, 256):
            frequencies += check_harmonic_budget(modulus, exponent, primes)
    rectangle_cases = sum(check_rectangle_bound(modulus) for modulus in (4, 16))
    print(f'{frequencies} Fourier residue budgets and {rectangle_cases} rectangle bounds passed')
    print(f'Common intercept bounds passed for {check_common_intercept()} targets')
    crossing = check_affine_line_obstruction([(1, 0, 3), (2, 1, 5)])
    parallel = check_affine_line_obstruction([(1024, -1, 3), (2048, -1, 5)])
    line_points, witnesses = (sum(counts) for counts in zip(crossing, parallel))
    print(f'Affine-line obstruction passed for {line_points} rejected line points'
          f' and {witnesses} accepted box points')
    check_dyadic_origin_obstruction()
    print('Dyadic-origin CRT preserved the fixed marked residue')


if __name__ == '__main__':
    main()
