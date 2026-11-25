"""Check the original-modulus Salié formula, quarter bit and first negative sign."""

import cmath
from math import gcd, isqrt, prod, sqrt, tau


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


def cosine_sign(a, d):
    return 1 if 4 * min(a % d, -a % d) < d else -1


def odd_triangle(u, v):
    """Count positive odd i,j with i/u + j/v < 1 by a Euclidean floor sum."""
    bound = (u*v - u - v - 1) // 2
    if bound < 0:
        return 0
    last_row, intercept = divmod(bound, v)
    n, a, m = last_row + 1, v, u
    count = n
    while True:
        slope, a = divmod(a, m)
        height, intercept = divmod(intercept, m)
        count += slope * n*(n-1)//2 + height*n
        n, intercept = divmod(a*n + intercept, m)
        if n == 0:
            return count
        m, a = a, m


def check_frequencies():
    for blocks in (((3, 2), (5, 2)), ((7, 2), (11, 2)), ((101, 1), (103, 1)),
                   ((103, 1), (107, 1)), ((3, 3), (7, 2), (11, 2)),
                   ((13, 1), (17, 1), (19, 1), (23, 1))):
        orders = [p**e for p, e in blocks]
        q = prod(orders)
        inverses = [pow(q // d, -1, d) for d in orders]
        negative = agreements = mixed_agreements = 0
        if len(orders) == 2:
            u, v = orders
            first = (u + v) // 2
            exceptions = {k for start in range(first, q//2+1, u)
                          for k in range(start, q//2+1, v) if gcd(k, q) == 1}
            assert min(exceptions) == first
        for c in range(1, q):
            if gcd(c, q) != 1:
                continue
            local = [c*a % d for a, d in zip(inverses, orders)]
            sign = prod(cosine_sign(x, d) for x, d in zip(local, orders))
            public = cosine_sign(c, q)
            negative += sign < 0
            agreements += public == sign
            if len(orders) == 2:
                k = min(2*c % q, -2*c % q)
                assert (public != sign) == (k in exceptions)
                mixed_agreements += public == cosine_sign(v*local[0] - u*local[1], q)

        phi = prod(d - d//p for d, (p, _) in zip(orders, blocks))
        chi4 = lambda d: 1 if d % 4 == 1 else -1
        assert phi - 2*negative == prod(chi4(d)-chi4(d//p)
                                        for d, (p, _) in zip(orders, blocks))
        if all(e % 2 == 0 for _, e in blocks):
            n = isqrt(q)
            assert (2*negative + n-1)//n == phi//n
        if len(orders) == 2:
            u, v = orders
            p, l = (p for p, _ in blocks)
            triangle = (odd_triangle(u, v) - odd_triangle(u//p, v)
                        - odd_triangle(u, v//l) + odd_triangle(u//p, v//l))
            assert phi-agreements == 2*triangle
            assert mixed_agreements == 2*agreements-phi
        print(f'orders={orders} units={phi} negatives={negative} public agreements={agreements}')


def check_sqrt_windows():
    primes = [p for p in range(101, 201) if all(p % d for d in range(2, isqrt(p) + 1))]
    tested = hits = first = 0
    for i, p in enumerate(primes):
        for q in primes[i+1:]:
            for e in (1, 2):
                u, v = p**e, q**e
                order = u*v
                for a in range(1, 5):
                    center = isqrt(a*a*order)
                    for k in range(center-1, center+2):
                        if gcd(k, order) != 1:
                            continue
                        c = k * pow(2, -1, order) % order
                        actual = cosine_sign(c*pow(v, -1, u), u) * cosine_sign(c*pow(u, -1, v), v)
                        wrong = actual != cosine_sign(c, order)
                        squares = (k*k-j*order for j in range(1, k*k//order+1, 2))
                        assert wrong == any(isqrt(n)**2 == n for n in squares)
                        if e == a == 1 and k == center+1:
                            assert wrong == (2*k == p+q) == (q <= p+2+isqrt(8*p))
                            first += wrong
                        hits += wrong
                        tested += 1
    print(f'square-root window units={tested}, disagreements={hits}, first Fermat successes={first}')


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
    check_frequencies()
    check_sqrt_windows()
