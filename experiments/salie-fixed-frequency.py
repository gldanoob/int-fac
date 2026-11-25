"""Check reduction to frequency one using integer signs and local cosines."""

from functools import lru_cache
from math import cos, gcd, isqrt, log, pi, prod


def strip_three(n):
    power = 1
    while n % 3 == 0:
        power *= 3
        n //= 3
    return power, n


def odd_representative(residue, modulus):
    residue %= modulus
    return residue if residue % 2 else modulus - residue


def frequency_plan(n, t):
    """Return (modulus, frequency, log coefficient) for queries and known 3-powers."""
    if n <= 0 or n % 2 == 0 or gcd(n, t) != 1:
        raise ValueError("The modulus must be positive and odd and the frequency a unit")
    queries, known = [], []
    block, n = strip_three(n)
    if block > 1:
        known.append((block, t * pow(n, -1, block) % block, 1))
    if n == 1:
        return queries, known
    t = t * pow(block, -1, n) % n
    coefficient = 1
    while n > 1:
        residue = pow(t, -1, n)
        m = odd_representative(residue, n)
        block = 1
        if 4*m > 3*n:
            divisible, _ = strip_three(n - m)
            block = 3*divisible
            m = odd_representative(residue * pow(block, -1, n), n)
        extra, m = strip_three(m)
        block *= extra
        assert 4*m <= 3*n and (t*block*m % n) in {1, n-1}
        queries.append((n*block*m, 1, coefficient))
        if block > 1:
            known.append((block, pow(n*m, -1, block), -coefficient))
        if m == 1:
            break
        t, n = pow(n*block, -1, m), m
        coefficient = -coefficient
    return queries, known


@lru_cache(maxsize=20000)
def prime_powers(n):
    blocks, divisor = [], 3
    while divisor*divisor <= n:
        block = 1
        while n % divisor == 0:
            n //= divisor
            block *= divisor
        if block > 1:
            blocks.append(block)
        divisor += 2
    if n > 1:
        blocks.append(n)
    return blocks


def local_sign(residue, modulus):
    return 1 if 4*min(residue % modulus, -residue % modulus) < modulus else -1


def trace(n, t):
    sign, log_magnitude = 1, 0.0
    for block in prime_powers(n):
        residue = 2*t*pow(n//block, -1, block) % block
        sign *= local_sign(residue, block)
        log_magnitude += log(abs(2*cos(2*pi*(residue / block))))
    return sign, log_magnitude


def check_fixed_frequency_distribution():
    limit = 1000003
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = b"\0\0"
    for d in range(2, isqrt(limit) + 1):
        if sieve[d]:
            sieve[d*d::d] = bytes((limit - d*d)//d + 1)
    primes = [p for p in range(2, limit + 1) if sieve[p]]
    for q in (1009, 10007, 100003, limit):
        total = above = 0
        for p in primes:
            if p >= q:
                break
            if 2*p <= q:
                continue
            n = p*q
            root = 2*p*pow(p, -1, q) - 1
            z = 2*root % n
            inside = 3*min(z, n-z) < n
            magnitude = abs(2*cos(4*pi/n) + 2*cos(2*pi*z/n))
            assert inside == (magnitude > 1)
            total += 1
            above += inside
        print(f"q={q}, {above}/{total} fixed-frequency magnitudes above one")
    count = negative = 0
    for p in (11, 9*25, 101*103, 7*11*13):
        for r in primes:
            if r >= 2000:
                break
            if r <= 8 or gcd(p, r) != 1:
                continue
            b = pow(r, -1, p)
            fixed, _ = trace(p*r, 1)
            assert fixed == trace(p, b)[0]*local_sign(2*b, p)
            count += 1
            negative += fixed < 0
    print(f"{count} prime lifts, {negative} negative fixed-frequency signs")


def main():
    cases = [(n, t) for n in range(3, 260, 2) for t in range(1, n) if gcd(n, t) == 1]
    # These force the first odd representative near the modulus, with large 3-adic valuations.
    for n in (10007, 10009, 30011, 65537):
        for gap in (2, 6, 18, 162, 1458):
            if gcd(gap, n) == 1:
                cases.append((n, pow(n-gap, -1, n)))
    literal_checked = set()
    longest = 0
    for n, t in cases:
        queries, known = frequency_plan(n, t)
        longest = max(longest, len(queries))
        assert all(u == 1 and m <= n**3 for m, u, _ in queries)
        assert all(strip_three(m)[1] == 1 for m, _, _ in known)
        signs, logs = [], []
        for m, u, exponent in queries + known:
            sign, magnitude = trace(m, u)
            signs.append(sign)
            logs.append(exponent*magnitude)
            if not (m <= 500 and u == 1 and m not in literal_checked):
                continue
            literal = sum(cos(4*pi*w/m) for w in range(m) if w*w % m == 1)
            assert (1 if literal > 0 else -1) == sign
            assert abs(log(abs(literal)) - magnitude) < 1e-9
            literal_checked.add(m)
        sign, magnitude = trace(n, t)
        assert prod(signs) == sign
        assert abs(sum(logs) - magnitude) < 1e-8
    print(f"{len(cases)} frequency transfers, {len(literal_checked)} literal root sums, "
          f"longest list {longest} queries")


if __name__ == "__main__":
    main()
    check_fixed_frequency_distribution()
