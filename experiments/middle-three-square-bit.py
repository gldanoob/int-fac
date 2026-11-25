"""Certify a middle binary digit from the unfactored three-square index under Dirichlet GRH."""

from fractions import Fraction
from math import isqrt
import subprocess
import sys


def primes_below(n):
    sieve = bytearray([1]) * n
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(n - 1) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((n - 1 - p*p)//p + 1)
    return [p for p in range(n) if sieve[p]]


def ceiling(x, y):
    return -(-x // y)


def pi_bounds(bits):
    # Machin's identity and adjacent partial sums for arctan(1/q).
    def arctan(q):
        value = Fraction()
        power = q
        j = 0
        while True:
            step = Fraction((-1)**j, (2*j+1)*power)
            value += step
            if j % 2:
                lo = value
                if -step < Fraction(1, 1 << bits):
                    return lo, lo - step
            j += 1
            power *= q*q
    a, A = arctan(5)
    b, B = arctan(239)
    return 16*a - 4*B, 16*A - 4*b


def count_interval(m, Q, primes, scale, pi):
    """Return integer count bounds. The table must list all primes below 2Q."""
    assert m > 0 and m % 8 == 3 and Q >= 5000
    residual = m
    small = []
    for p in primes:
        if residual % (p*p) == 0:
            power = 1
            while residual % (p*p) == 0:
                residual //= p*p
                power *= p
            small.append((p, power))

    def symbol(p):
        if p == 2:
            return -1  # residual remains 3 mod 8
        value = pow((-residual) % p, (p-1)//2, p)
        return -1 if value == p-1 else value

    corr = Fraction(1)
    for p, power in small:
        corr *= 1 + Fraction((1-symbol(p))*(power-1), power*(p-1))

    lo = hi = scale
    floor_prefix, ceil_prefix = None, None
    for p in primes:
        if p >= Q:
            floor_prefix = lo if floor_prefix is None else min(floor_prefix, lo)
            ceil_prefix = hi if ceil_prefix is None else max(ceil_prefix, hi)
        den = p - symbol(p)
        lo = lo*p // den
        hi = ceiling(hi*p, den)
    # Including the last prefix also covers the endpoint if 2Q-1 is composite.
    lo = min(lo, floor_prefix) if floor_prefix is not None else lo
    hi = max(hi, ceil_prefix) if ceil_prefix is not None else hi

    b = m.bit_length()
    log_q_lower = Fraction(69, 100)*(Q.bit_length()-1)
    error = ((Fraction(6593, 1000)*Fraction(7, 10)*b + Fraction(19321, 1000))
             / (isqrt(Q)*log_q_lower) + Fraction(b, 2*Q-1) + Fraction(1, b*b))
    if error >= 1:
        return 0, m
    root = isqrt(m*scale*scale)
    lower = Fraction(3*root*lo, scale*scale)*corr*(1-error)/pi[1]
    upper = Fraction(3*(root+1)*hi, scale*scale)*corr/(1-error)/pi[0]
    return ceiling(lower.numerator, lower.denominator), upper.numerator // upper.denominator


def high_quotient(m, interval, extra_bits=0):
    k = max(0, (m.bit_length()-1)//2 - extra_bits)
    l, u = interval
    return (l >> k) if l <= u and l >> k == u >> k else None


if __name__ == "__main__":
    samples = list(range(8195, 16384, 8))
    # Include powers of 3, additional ramification, split/inert square factors and a large unseen factor.
    samples += [3**13, 3*5**4, 3*7**4, 11*13**4, 3*10007**2, 59*10009**2]
    Q = int(sys.argv[1]) if len(sys.argv) > 1 else 5000
    primes = primes_below(2*Q)
    scale = 1 << 96
    pi = pi_bounds(96)
    cmd = f"foreach({samples},m,print(3*qfbhclassno(m)))\n"
    reference = subprocess.run(["gp","-fq"], input=cmd, text=True, capture_output=True, check=True)
    assert not reference.stderr
    counts = list(map(int, reference.stdout.splitlines()))
    assert len(counts) == len(samples)
    decisions = [0, 0, 0]
    extra_decisions = 0
    for m, count in zip(samples, counts):
        bounds = count_interval(m, Q, primes, scale, pi)
        assert bounds[0] <= count <= bounds[1], (m, count, bounds)
        quotient = high_quotient(m, bounds)
        extra = high_quotient(m, bounds, 1)
        if extra is not None:
            assert extra == count >> (((m.bit_length()-1)//2)-1)
            extra_decisions += 1
        if quotient is None:
            decisions[2] += 1
        else:
            assert quotient == count >> ((m.bit_length()-1)//2)
            decisions[quotient & 1] += 1
    assert all(decisions)
    print("inputs, certified zero/one, abstentions, extra-bit quotients",
          len(samples), decisions, extra_decisions)
    for h in [4, 5, 16, 17, 64, 65, 256, 257]:
        q = 1 << h
        sign = 1 if h % 2 else -1
        s = q*q + sign*q + 1
        m = 3*s*s
        assert s % 3 == 1 and (m.bit_length()-1)//2 == 2*h
        assert (s >> (2*h)) == (sign == 1)
        assert abs(s - q*q) <= 2*q
    print("eight explicit near-boundary indices")
