"""Replay a scheduled input with an isolated odd valuation per grid slope."""

from math import factorial, gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


def single_valuation_lift(residue, prime, evaluate):
    assert evaluate(residue) % prime == 0
    lift = residue + prime if evaluate(residue) % prime**2 == 0 else residue
    assert evaluate(lift) % prime**2 != 0
    return lift


def run():
    constructor = run_path(str(Path(__file__).with_name("cogentic-monic-pair.py")))
    d, height = 5, 2
    slopes = [(a, b) for a in range(-height, height + 1) if a
              for b in range(1, height + 1) if gcd(a, b) == 1]
    affine = {(a, b): (a**d * (a + b) + 2*b**(d+1), b*a**d) for a, b in slopes}
    excluded = factorial(d) * (d**d - 2) * prod(abs(a**d + 2*b**d) for a, b in slopes)
    odd_part = excluded // (excluded & -excluded)
    congruences = [(0, odd_part), (1, 2)]

    auxiliary = (47, 53, 59, 67, 73, 79)
    cutoff = 80
    p, q = 83, 89
    primes = [r for r in range(2, q+1) if all(r % k for k in range(2, isqrt(r) + 1))]
    assert cutoff < p < q < 2*cutoff
    for prime in (*auxiliary, p, q):
        assert prime in primes
        assert odd_part % prime

    for x, prime in zip(slopes, auxiliary, strict=True):
        numerator, linear = affine[x]
        assert (numerator**d + 2*linear**d) % prime
        residue = numerator * pow(linear, -1, prime) % prime
        lift = single_valuation_lift(residue, prime, lambda m: numerator - m*linear)
        congruences.append((lift, prime**2))

    for prime in (p, q):
        residue = pow(-2, pow(d, -1, prime-1), prime)
        lift = single_valuation_lift(residue, prime, lambda m: m**d + 2)
        congruences.append((lift, prime**2))

    modulus = prod(factor for _, factor in congruences)
    residue = sum(r * (modulus // k) * pow(modulus // k, -1, k)
                  for r, k in congruences) % modulus
    j = next(j for j in range(1, 100) if d**3 * j < 2**j)
    base_limit = 2**(d*d*j)
    low = base_limit - base_limit // (4*d)
    high = (8*d-1)*base_limit // (8*d)
    first = low + (residue - low) % modulus
    small_prime_product = prod(prime for prime in primes if prime <= cutoff)
    m = next(candidate for candidate in range(first, high+1, modulus)
             if gcd(candidate**d + 2, small_prime_product) == 1)
    n = m**d + 2
    assert constructor["scheduled_degree"](n) == d
    root_argument, f, g = constructor["check_pair"](n, d)
    assert (root_argument, f, g) == (m, (2, 0, 0, 0, 0, 1), (2, 0, 0, 0, 0, 1-m, 1))
    for prime in (p, q):
        assert n % prime == 0 and n % prime**2 != 0
    assert gcd(d*m**(d-1), n) == gcd(m**(d-1)*(d+m), n) == 1
    for a in range(-height, height + 1):
        for b in range(-height, height + 1):
            if (a, b) != (0, 0):
                assert gcd(a-b*m, n) == 1

    for slope, prime in zip(slopes, auxiliary, strict=True):
        for a, b in slopes:
            norm = sum(c*a**i*b**(d+1-i) for i, c in enumerate(g))
            numerator, linear = affine[a, b]
            assert norm == numerator - m*linear
            assert (norm % prime == 0) == ((a, b) == slope)
            assert norm % prime**2 != 0
    assert g[0] == 2

    # These columns multiply to 4(-1-X)^2 before reduction in either field.
    columns = ((-2, 2), (-1, 1), (2, 0))
    root = 2*(-1-m)
    assert prod(a-b*m for a, b in columns) == root**2
    assert gcd(root-root, n) == n and gcd(2*root, n) == 1
    print(f"Verified scheduled d={d}, height={height}, {len(slopes)} isolated slopes, "
          f"and trivial signs at {n.bit_length()} bits with prime divisors {p}, {q} "
          f"and none through {cutoff}")


if __name__ == "__main__":
    run()
