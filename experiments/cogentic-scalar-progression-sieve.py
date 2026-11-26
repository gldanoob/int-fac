#!/usr/bin/env python3
"""Exact replay for divisor counting by sieving progression indices."""

from math import gcd, isqrt
from random import Random


def primes_through(n):
    sieve = bytearray(b"\x01") * (n + 1)
    if n >= 0:
        sieve[0] = 0
    if n >= 1:
        sieve[1] = 0
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p:n + 1:p] = b"\x00" * (((n - p * p) // p) + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def progression_sieve(c, d, t, allowed_primes):
    """Count nonzero |c+d*j| that are squarefree products of allowed primes."""
    residual = [abs(c + d * j) for j in range(t)]
    squarefree = [True] * t
    visits = 0
    for p in allowed_primes:
        if d % p == 0:
            indices = range(t) if c % p == 0 else range(0)
        else:
            first = (-c * pow(d, -1, p)) % p
            indices = range(first, t, p)
        for j in indices:
            visits += 1
            if residual[j] and residual[j] % p == 0:
                residual[j] //= p
                if residual[j] % p == 0:
                    squarefree[j] = False
    accepted = sum(value != 0 and rest == 1 and sf
                   for value, rest, sf in zip((abs(c + d*j) for j in range(t)), residual, squarefree))
    return accepted, visits


def direct_count(c, d, t, allowed_primes):
    allowed = set(allowed_primes)
    accepted = 0
    for j in range(t):
        value = abs(c + d * j)
        if not value:
            continue
        remaining = value
        valid = True
        p = 2
        while p * p <= remaining:
            if remaining % p == 0:
                if p not in allowed:
                    valid = False
                    break
                remaining //= p
                if remaining % p == 0:
                    valid = False
                    break
            p += 1
        if valid and remaining > 1 and remaining not in allowed:
            valid = False
        accepted += valid
    return accepted


def check_cases():
    rng = Random(20261126)
    cases = [
        (0, 0, 9, [2, 3]),
        (12, 0, 5, [2, 3]),
        (6, 6, 12, [2, 3, 5]),
        (-15, 4, 20, [2, 3, 5, 7]),
        (31, -8, 19, [2, 5, 7]),
        (0, 1, 40, [2, 3, 5, 7]),
    ]
    for _ in range(500):
        b = rng.randrange(3, 50)
        band = [p for p in primes_through(b) if p > isqrt(b)]
        allowed = [p for p in band if rng.randrange(2)]
        cases.append((rng.randrange(-10000, 10001), rng.randrange(-100, 101),
                      rng.randrange(1, 60), allowed))

    for c, d, t, allowed in cases:
        fast, visits = progression_sieve(c, d, t, allowed)
        slow = direct_count(c, d, t, allowed)
        assert fast == slow, (c, d, t, allowed, fast, slow)
        # Every p not dividing d visits at most ceil(T/p) indices; p|d visits T.
        bound = sum(t if d % p == 0 and c % p == 0 else
                    (0 if d % p == 0 else len(range((-c * pow(d, -1, p)) % p, t, p)))
                    for p in allowed)
        assert visits == bound

    # Demonstrate the additive visit count on a long progression versus
    # testing every value against every eligible prime.
    eligible = [p for p in primes_through(1000) if p > 31]
    c, d, t = 123456789, 17, 20000
    _, visits = progression_sieve(c, d, t, eligible)
    naive_tests = t * len(eligible)
    assert visits < naive_tests // 20
    print(f"exact progression counts agree on {len(cases)} cases")
    print(f"long case: {visits} progression visits vs {naive_tests} value-prime tests")


if __name__ == "__main__":
    check_cases()
