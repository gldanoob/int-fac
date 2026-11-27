"""Check Euclidean recurrence recovery against the sparse implementation."""

from itertools import product
from pathlib import Path
from random import Random
from runpy import run_path

from sage.all import GF, PolynomialRing


def pade_recurrence(ring, sequence, n):
    """Return a verified monic recurrence of length ≤n, or None."""
    x = ring.gen()
    series = ring(sequence)
    if not series:
        return ring.one()
    previous, remainder = x**(2*n), series
    previous_denominator, denominator = ring.zero(), ring.one()
    while remainder.degree() >= n:
        quotient, next_remainder = previous.quo_rem(remainder)
        previous, remainder = remainder, next_remainder
        previous_denominator, denominator = denominator, previous_denominator-quotient*denominator
    divisor = denominator.gcd(remainder)
    denominator, remainder = denominator//divisor, remainder//divisor
    if not denominator[0]:
        return None
    scale = denominator[0]**-1
    denominator, remainder = scale*denominator, scale*remainder
    if (denominator*series-remainder) % (x**(2*n)):
        return None
    length = max(denominator.degree(), remainder.degree()+1)
    return ring([denominator[length-i] for i in range(length+1)])


def replay():
    sparse = run_path(str(Path(__file__).with_name("keybreak-sparse-dependency.py")))
    bm = sparse["berlekamp_massey"]
    rng = Random(2402)
    binary = PolynomialRing(GF(2), "z")
    counts = []
    for degree in (1, 3, 5):
        modulus = sparse["irreducible"](degree)
        if degree == 1:
            field = GF(2)
            lift, encode = field, int
        else:
            polynomial = binary([(modulus >> i) & 1 for i in range(degree+1)])
            field = GF(2**degree, name="a", modulus=polynomial)
            lift, encode = field.from_integer, lambda z: int(z.to_integer())
        ring = PolynomialRing(field, "x")
        samples = list(product(range(2), repeat=8)) if degree == 1 else []
        samples.extend(tuple(rng.randrange(2**degree) for _ in range(2*n))
                       for n in range(1, 13) for _ in range(16))
        for sequence in samples:
            n = len(sequence)//2
            expected = bm(sequence, modulus)
            actual = pade_recurrence(ring, [lift(x) for x in sequence], n)
            if len(expected)-1 > n:
                assert actual is None
            else:
                assert actual is not None and [encode(x) for x in actual.list()] == expected
        counts.append(len(samples))
    print(f"Euclidean and discrepancy recurrences agreed on {sum(counts)} prefixes over three fields.")


if __name__ == "__main__":
    replay()
