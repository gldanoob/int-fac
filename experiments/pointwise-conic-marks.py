"""Check the rational character marks independently at each pair of toy primes."""

from fractions import Fraction
from functools import cache
from itertools import permutations, product
from math import gcd, isqrt


def prime_numbers(limit):
    return [n for n in range(2, limit + 1) if all(n % d for d in range(2, isqrt(n) + 1))]


def character(x, p):
    residue = pow(x % p, (p - 1) // 2, p)
    return -1 if residue == p - 1 else residue


@cache
def small_point(e, f):
    for u, v in product(range(1, isqrt(f) + 1), range(1, isqrt(e) + 1)):
        square = e * u * u - f * v * v
        if square <= 0:
            continue
        w = isqrt(square)
        if w * w == square:
            common = gcd(u, gcd(v, w))
            return u // common, v // common, w // common
    raise AssertionError(("Holzer box empty", e, f))


def signs(point, e, f, p, q, sign):
    u, v, w = point
    assert e * u * u == f * v * v + w * w
    assert gcd(u * v * w, p * q) == 1
    c = Fraction(e * u * u, w * w)
    for prime in (p, q):
        value = c.numerator * pow(c.denominator, -1, prime) % prime
        if prime == p:
            assert character(value, p) == character(value - 1, p) == sign
        else:
            assert character(value * (value - 1), q) == -1
    return max(c.numerator, c.denominator)


def witness(e, f, p, q, sign):
    b = small_point(e, f)
    if gcd(b[0] * b[1] * b[2], p * q) == 1:
        return False, signs(b, e, f, p, q, sign)
    for t in product(range(13), repeat=3):
        form = e * t[0] * t[0] - f * t[1] * t[1] - t[2] * t[2]
        cross = e * t[0] * b[0] - f * t[1] * b[1] - t[2] * b[2]
        reflected = tuple(form * bi - 2 * cross * ti for bi, ti in zip(b, t))
        u, v, w = reflected
        if gcd(u * v * w, p * q) == 1:
            return True, signs(reflected, e, f, p, q, sign)
    raise AssertionError(("no unit point after reflection", b, p, q))


def main():
    primes = prime_numbers(12000)
    candidates = [r for r in primes if r % 8 == 1]
    cases = rescued = largest_height = 0
    for p, q in permutations([r for r in primes if 13 <= r < 90], 2):
        for sign in (-1, 1):
            e = next(r for r in candidates if character(r, p) == sign and character(r, q) == 1)
            f = next(r for r in candidates if character(r, p) == sign and character(r, q) == -1
                     and character(r, e) == 1)
            changed, height = witness(e, f, p, q, sign)
            cases += 1
            rescued += changed
            largest_height = max(largest_height, height)
    print(f"ordered signed cases = {cases}, nonunit Holzer points repaired = {rescued}, "
          f"largest reduced rational height = {largest_height}")


if __name__ == "__main__":
    main()
