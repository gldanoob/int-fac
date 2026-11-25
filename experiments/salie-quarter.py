"""Check the original-modulus Salié formula, quarter bit and first negative sign."""

import cmath
from math import gcd, isqrt, sqrt, tau


def character(x, n):
    return cmath.exp(1j * tau * ((x % n) / n))


def jacobi(x, n):
    sign = 1
    x %= n
    while x:
        while x % 2 == 0:
            x //= 2
            if n % 8 in (3, 5):
                sign = -sign
        if x % 4 == n % 4 == 3:
            sign = -sign
        x, n = n % x, x
    return sign if n == 1 else 0


def negative_sign(q, t):
    """Difference-of-squares sign test. The modulus has two odd prime types."""
    assert gcd(t, q) == 1
    residue = 2 * t % q
    bound = 2 * min(residue, q - residue)
    # Odd squares are one modulo eight.
    first = (bound * bound - 1) * pow(q, -1, 8) % 8
    for k in range(first, bound * bound // q + 1, 8):
        square = bound * bound - k * q
        z = isqrt(square)
        if z * z == square and z % q not in (bound % q, -bound % q):
            return True
    return False


def check_sums():
    counts = [0, 0, 0]
    for n in range(3, 182, 2):
        roots = [w for w in range(n) if w * w % n == 1]
        units = [u for u in range(1, n) if gcd(u, n) == 1]
        terms = [(jacobi(u, n), (u + pow(u, -1, n)) % n) for u in units]
        phases = [character(a, n) for a in range(n)]
        gauss = (1 if n % 4 == 1 else 1j) * sqrt(n)
        for t in units:
            direct = sum(sign * phases[t * a % n] for sign, a in terms)
            normalized = direct * jacobi(t, n) / gauss
            reference = sum(phases[2 * t * w % n] for w in roots)
            assert abs(normalized - reference) < 1e-10
            counts[0] += 1
            if len(roots) == 4:
                assert (normalized.real < 0) == negative_sign(n, t)
                counts[1] += 1

        if len(roots) == 4:
            jmax = (n.bit_length() + 1) // 2
            scale = 1 << jmax
            a, radius = scale * scale * n, n // 4
            denominator = a * n + 1
            for j in range(jmax - 1):
                c = 1 << j
                t = c * pow(2, -1, n) % n
                direct = sum(sign * phases[t * v % n] for sign, v in terms)
                residual = (direct * jacobi(t, n) / gauss - 2 * phases[c % n].real).real
                center = scale * n * c
                total = sum(a * x*x // denominator
                            for x in range(center - radius, center + radius + 1))
                parity = (total - a * center*center // denominator) % 2
                known = int(min(c % n, -c % n) <= radius)
                assert parity == (known ^ int(residual > 0))
                if 16 * c*c < n:
                    assert abs(residual) >= 2 / sqrt(n) - 1e-10
                counts[2] += 1
    print(f'literal unit sums={counts[0]}, integer sign checks={counts[1]}, '
          f'centered floor parities={counts[2]}')


def check_first_negative():
    count = 0
    for a, b in ((3, 5), (3, 11), (5, 11), (9, 11), (11, 13),
                 (11, 17), (13, 19), (11, 25), (25, 27)):
        n = a * b
        q = n*n
        small, large = sorted((a*a, b*b))
        expected = (7 * small + large) // 8
        actual = next(t for t in range(1, expected + 1)
                      if gcd(t, n) == 1 and negative_sign(q, t))
        assert actual == expected
        discriminant = (8*actual)**2 - 28*q
        s = isqrt(discriminant)
        assert s*s == discriminant
        candidates = [(8*actual + d) // 14 for d in (-s, s)
                      if (8*actual + d) % 14 == 0]
        assert [u for u in candidates if u > 1 and q % u == 0] == [small]
        # A direct sum at the two sides of the first change for the smallest base.
        if n == 15:
            previous = max(t for t in range(1, actual) if gcd(t, n) == 1)
            for t in (previous, actual):
                value = sum(character(t * (u + pow(u, -1, q)), q)
                            for u in range(1, q) if gcd(u, n) == 1)
                assert (value.real < 0) == (t == actual)
        count += 1
    print(f'first negative unit frequencies={count}')


if __name__ == '__main__':
    check_sums()
    check_first_negative()
