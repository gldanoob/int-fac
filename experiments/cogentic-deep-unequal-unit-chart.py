#!/usr/bin/env python3
"""Replay the modular tests for one unequal-power chart."""

from itertools import combinations, count
from math import gcd, isqrt, lcm, prod


def profile(prime):
    order = next(e for e in count(1) if pow(3, e, prime) == 1)
    odd_order = order
    while odd_order % 2 == 0:
        odd_order //= 2
    period = next(e for e in count(1) if pow(2, e, odd_order) in {1 % odd_order, -1 % odd_order})
    return order, odd_order, period


def signed_gcds(t, modulus):
    return gcd(t * t + 3, modulus), gcd(3 * t * t + 1, modulus)


def availability(t, modulus):
    return tuple(gcd(value, modulus) for value in (t, t - 1, t + 1, t * t + 1))


def predicted_gcds(pair, profiles, depth_plus_one):
    factors = [1, 1]
    for prime in pair:
        order, odd_order, period = profiles[prime]
        phase = pow(2, depth_plus_one, odd_order)
        hits = [order == 2 * odd_order and phase == sign % odd_order for sign in (1, -1)]
        assert any(hits) == (order == 2 * odd_order and depth_plus_one % period == 0)
        for sign, hit in enumerate(hits):
            if hit:
                factors[sign] *= prime
    return tuple(factors)


def polynomial_values(n):
    return n - 1, n + 1, n * n + 1, 11 * (n + 2)


def main():
    primes = [p for p in range(5, 308, 2) if all(p % d for d in range(3, isqrt(p) + 1, 2))]
    profiles = {p: profile(p) for p in primes}
    depth_count = 24
    depth_product = prod((2**e - 1) * (2**e + 1) for e in range(1, depth_count + 1))
    finite_checks = 0
    for pair in combinations(primes, 2):
        modulus = prod(pair)
        t = 3
        for e in range(1, depth_count + 1):
            direct = signed_gcds(t, modulus)
            assert direct == predicted_gcds(pair, profiles, e), (pair, e)
            if availability(t, modulus) == (1, 1, 1, 1):
                a = t * (t - 1) * pow(t + 1, -1, modulus)
                b = (t - 1) * pow(t * (t + 1), -1, modulus)
                ratio = -t * a * b * b
                assert direct == (gcd(ratio - 1, modulus), gcd(ratio + 1, modulus))
            for prime in pair:
                if any(factor % prime == 0 for factor in direct):
                    assert availability(t, prime) == (1, 1, 1, 1)
                    assert depth_product % profiles[prime][1] == 0
            t = t * t % modulus
            finite_checks += 1

    support_checks = 0
    support_hits = 0
    for r, (order, _, period) in profiles.items():
        v = next((p for p in primes if p > 5 and p != 11 and period % p == 0), None)
        if v is None:
            continue
        roots = {x for x in range(v) if any(value % v == 0 for value in polynomial_values(r * x))}
        assert len(roots) <= 5 and v < r
        for q in primes:
            if q == r:
                continue
            values = polynomial_values(r * q)
            for e in (*values, lcm(*values), 15 * prod(values), gcd(*values)):
                t = pow(3, pow(2, e - 1, order), r)
                if r in signed_gcds(t, r):
                    assert e % v == 0 and q % v in roots, (r, q, e)
                    support_hits += 1
                support_checks += 1

    for p, q, depth, expected in [(271, 307, 3, (271, 307)), (43, 67, 4, (1, 67)), (7, 11, 0, (1, 7))]:
        n = p * q
        t = pow(3, 2**depth, n)
        assert signed_gcds(t, n) == expected and availability(t, n) == (1, 1, 1, 1)
    assert signed_gcds(3, 5 * 7) == (1, 7) and availability(3, 5 * 7) == (1, 1, 1, 5)
    assert finite_checks and 0 < support_hits < support_checks
    print(f"{finite_checks} finite-depth checks, {support_checks} support checks ({support_hits} hits), and four fixtures passed")


if __name__ == "__main__":
    main()
