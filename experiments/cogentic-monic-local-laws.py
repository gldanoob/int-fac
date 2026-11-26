"""Verify the monic pair's local laws and compressed prime-power roots."""

from collections import Counter
from fractions import Fraction
from importlib import import_module
from math import comb, gcd, prod

monic_pair = import_module("cogentic-monic-pair").monic_pair


def evaluate(coefficients, x):
    value = 0
    for coefficient in reversed(coefficients):
        value = value*x+coefficient
    return value


def norm(coefficients, a, b):
    degree = len(coefficients)-1
    return sum(coefficient*a**i*b**(degree-i) for i, coefficient in enumerate(coefficients))


def valuation(value, p, limit):
    for exponent in range(limit):
        if value % p:
            return exponent
        value //= p
    return limit


def root_cylinders(coefficients, p, exponent):
    """Represent roots by disjoint pairs (residue, modulus) with modulus dividing p**exponent."""
    degree = len(coefficients)-1
    pending = [(coefficients, 0, 1, exponent)]
    roots = []
    visited = 0
    while pending:
        coefficients, residue, modulus, remaining = pending.pop()
        visited += 1
        content = min(valuation(c, p, remaining) for c in coefficients)
        if content == remaining:
            roots.append((residue, modulus))
            continue
        coefficients = [c//p**content for c in coefficients]
        remaining -= content
        reduced_degree = max(i for i, c in enumerate(coefficients) if c % p)
        for r in range(p) if reduced_degree else ():
            if evaluate(coefficients, r) % p:
                continue
            shifted = tuple(
                p**j*sum(c*comb(i, j)*r**(i-j)
                         for i, c in enumerate(coefficients) if i >= j)
                for j in range(len(coefficients))
            )
            pending.append((shifted, residue+modulus*r, modulus*p, remaining))
    assert visited <= 1+degree*exponent
    return roots


def difference_cylinders(m, degree, p, threshold):
    if threshold == 0:
        return [(0, 1)]
    s = valuation(m, p, m.bit_length())
    if threshold <= (degree+1)*s:
        return [(0, p**((threshold+degree)//(degree+1)))]
    return [(0, p**((threshold-s+degree-1)//degree)), (m, p**(threshold-degree*s))]


def intersection_size(left, right, modulus):
    return sum(modulus//max(u, v) for a, u in left for b, v in right
               if (a-b) % min(u, v) == 0)


def verify_prime_powers(n, degree, p, level):
    m, f, g = monic_pair(n, degree)
    modulus = p**level
    exact = Counter((valuation(evaluate(f, x), p, level),
                     valuation(evaluate(g, x), p, level)) for x in range(modulus))
    roots = [{k: root_cylinders(poly, p, k) for k in range(level+1)} for poly in (f, g)]
    for i, polynomial in enumerate((f, g)):
        for k in range(level+1):
            q = p**k
            expanded = [x for r, step in roots[i][k] for x in range(r, q, step)]
            assert sorted(expanded) == [x for x in range(q) if evaluate(polynomial, x) % q == 0]
    for threshold in range(level+1):
        classes = difference_cylinders(m, degree, p, threshold)
        assert {x for x in range(modulus) if any((x-r) % q == 0 for r, q in classes)} == {
            x for x in range(modulus) if (x-m)*x**degree % p**threshold == 0
        }
    for u in range(level+1):
        for v in range(level+1):
            anchor = roots[0] if u >= v else roots[1]
            intersected = intersection_size(anchor[max(u, v)],
                                            difference_cylinders(m, degree, p, min(u, v)),
                                            modulus)
            assert intersected == sum(count for (i, j), count in exact.items() if i >= u and j >= v)
            if p == 2 and max(u, v) > 1:
                assert intersected == 0
            if u and v and p == 2 and max(u, v) == 1:
                assert intersected == modulus//2
            if u == v and u and n % p == 0 and f[0] % p != 0:
                assert intersected == (modulus//p**u if n % p**u == 0 else 0)
            if u == v and u and n % p and f[0] % p == 0 and f[1] % p:
                cutoff = degree*valuation(f[0], p, abs(f[0]).bit_length())
                assert intersected == (modulus//p**u if u <= cutoff else 0)
    return (level+1)**2


def verify_marks(n, degree):
    m, f, g = monic_pair(n, degree)
    checked = 0
    for a in range(-48, 49):
        for b in range(49):
            if gcd(a, b) != 1:
                continue
            first, second = norm(f, a, b), norm(g, a, b)
            common = gcd(first, second)
            assert n*abs(f[0])**degree % common == 0
            if gcd(a-m*b, n) == 1:
                assert common == gcd(first, a**degree)
                assert abs(f[0])**degree % common == 0
                for p in (2, 3, 5, 7, 11, 13):
                    assert (common % p == 0) == (a % p == f[0] % p == 0)
            checked += 1
    return checked


def verify_crt(n, degree, levels):
    m, f, g = monic_pair(n, degree)
    modulus = prod(p**k for p, k in levels)
    factors = []
    independent = []
    for p, k in levels:
        q = p**k
        roots_f = root_cylinders(f, p, k)
        roots_g = root_cylinders(g, p, 1)
        excluded = [(m, p)] if n % p == 0 else []
        c_f = intersection_size(roots_f, [(0, 1)], q)-intersection_size(roots_f, excluded, q)
        c_g = intersection_size(roots_g, [(0, 1)], q)-intersection_size(roots_g, excluded, q)
        common = intersection_size(roots_f, difference_cylinders(m, degree, p, 1), q)
        common -= intersection_size(roots_f, excluded, q)
        projective_size = q if excluded else q+q//p
        factors.append((projective_size-c_f-c_g+common)*(q-q//p))
        independent.append(Fraction((projective_size-c_f)*(projective_size-c_g), projective_size**2))
        assert Fraction(projective_size-c_f-c_g+common, projective_size) == (
            independent[-1]+Fraction(common, projective_size)-Fraction(c_f*c_g, projective_size**2)
        )
    eligible_n_part = gcd(n, modulus)
    count = sum(
        gcd(gcd(a, b), modulus) == 1 and gcd(a-m*b, eligible_n_part) == 1
        and all(norm(f, a, b) % p**k and norm(g, a, b) % p for p, k in levels)
        for a in range(modulus) for b in range(modulus)
    )
    assert count == prod(factors)


def verify_sieve(n, degree, height, primes):
    m, f, g = monic_pair(n, degree)
    marks = [(a, b) for b in range(1, height+1) for a in range(-height, height+1)
             if gcd(a, b) == gcd(a-m*b, n) == 1]
    accepted = []
    for coefficients in (f, g):
        values = {mark: abs(norm(coefficients, *mark)) for mark in marks}
        residuals = values.copy()
        for p in primes:
            for root in range(p):
                if evaluate(coefficients, root) % p:
                    continue
                for b in range(1, height+1):
                    if b % p == 0:
                        continue
                    first = -height+(root*b+height) % p
                    for a in range(first, height+1, p):
                        if (a, b) in residuals:
                            value = residuals[a, b]
                            assert value % p == 0
                            while value % p == 0:
                                value //= p
                            residuals[a, b] = value
        direct = {mark for mark, value in values.items()
                  if value == prod(p**valuation(value, p, value.bit_length()) for p in primes)}
        sieved = {mark for mark, value in residuals.items() if value == 1}
        assert direct == sieved
        accepted.append(sieved)
    return len(accepted[0] & accepted[1])


def main():
    fixtures = [(27, 3), (49, 3), (129, 3), (131, 3), (139, 3), (323, 3), (729, 3),
                (3**8+2, 8), (5**13+236, 13)]
    primes = ((2, 9), (3, 7), (5, 4), (7, 3), (11, 3))
    tails = sum(verify_prime_powers(n, d, p, level)
                for n, d in fixtures for p, level in primes)
    marks = sum(verify_marks(n, d) for n, d in fixtures)
    for n, degree in fixtures:
        verify_crt(n, degree, ((2, 2), (3, 1), (5, 1)))
    sieve_marks = sum(verify_sieve(n, d, 24, (2, 3, 5, 7, 11, 13, 17, 19, 23, 29))
                      for n, d in fixtures)
    assert sieve_marks > 0
    # A deep singular root should stay in one cylinder.
    assert root_cylinders((0,)*13+(1,), 3, 120) == [(0, 3**10)]
    print(f"Verified {tails:,} mixed valuation tails, {marks:,} primitive marks, "
          f"and {len(fixtures)} complete CRT boxes through degree 13")
    print(f"Verified the exact small-prime sieve, with {sieve_marks} simultaneous smooth marks")


if __name__ == "__main__":
    main()
