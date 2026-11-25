"""Independent finite controls for interval clustering and Fourier information."""

from bisect import bisect_left, bisect_right
from itertools import combinations
from math import isqrt


def prime_table(limit):
    table = bytearray([1]) * (limit + 1)
    table[0:2] = b'\0\0'
    for prime in range(2, isqrt(limit) + 1):
        if table[prime]:
            table[prime * prime::prime] = bytearray((limit - prime * prime) // prime + 1)
    return [i for i in range(2, limit + 1) if table[i]]


def cover_controls():
    checked_primes = centers = occupied_bins = bad_primes = 0
    for P in (4096, 16384, 65536):
        primes = prime_table(2 * P)
        for cutoff in (5, 11, 19):
            smooth = {1}
            for prime in primes:
                if prime == 2:
                    continue
                if prime > cutoff:
                    break
                expanded = set(smooth)
                for n in smooth:
                    while n * prime <= 3 * P:
                        n *= prime
                        expanded.add(n)
                smooth = expanded
            orders = sorted(4 * n for n in smooth)
            bin_width = isqrt(P) // 4
            short_radius = isqrt(P) // 8
            for required in (2, 4, 7):
                bins = set()
                for p in primes:
                    if p <= P:
                        continue
                    checked_primes += 1
                    radius = isqrt(p)
                    center = p + 1
                    first = bisect_left(orders, center - radius)
                    last = bisect_right(orders, center + radius)
                    if last - first < required:
                        bins.add(center // bin_width)
                        bad_primes += 1
                for i in bins:
                    for center in range(i * bin_width, (i + 1) * bin_width):
                        first = bisect_left(orders, center - short_radius)
                        last = bisect_right(orders, center + short_radius)
                        assert last - first < required
                        centers += 1
                occupied_bins += len(bins)
    return checked_primes, bad_primes, occupied_bins, centers


def cofactor_controls():
    # In a small finite field the completely multiplicative weight n^s
    # makes both sides exactly comparable without floating point logarithms.
    checked = 0
    primes = (13, 17, 19, 23, 29, 31)
    for field in (101, 251):
        for exponent in (-1, 2, 7, 11):
            for degree in range(1, 6):
                coefficients = [1] + [0] * degree
                for prime in primes:
                    value = pow(prime, exponent, field)
                    for j in range(degree, 0, -1):
                        coefficients[j] = (coefficients[j] + value * coefficients[j - 1]) % field
                direct = 0
                for selected in combinations(primes, degree):
                    number = 1
                    for prime in selected:
                        number *= prime
                    direct += pow(number, exponent, field)
                assert coefficients[-1] == direct % field
                checked += 1
    return checked


def exact_fourier_controls():
    # A subgroup of queried frequencies permits an exact rational projection.
    tested = 0
    for n in (32, 64, 128):
        for m in (2, 4, 8):
            for j in range(n):
                # f=1-(e_j-Proj(e_j))/(1-m/n), scaled by n-m.
                values = [n - m + (m if (r - j) % m == 0 else 0) for r in range(n)]
                values[j] -= n
                assert values[j] == 0 and min(values) >= 0
                assert sum((v - (n - m)) ** 2 for v in values) == n * (n - m)
                for k in range(m):
                    assert sum(values[k::m]) == n // m * (n - m)
                tested += 1
    return tested


if __name__ == "__main__":
    print("prime tests, bad incidences, occupied bins, short centers", *cover_controls())
    print("elementary-symmetric coefficient controls", cofactor_controls())
    print("hidden-bin Fourier controls", exact_fourier_controls())
