"""Exact finite Gaussian factorization and convolution tests on two affine marks."""

from collections import defaultdict
from fractions import Fraction


def integer_convolution(left, right):
    if not left or not right:
        return {}
    i0, j0 = min(left), min(right)
    span = max(left) - i0 + max(right) - j0 + 1
    slot = max(left.values()).bit_length() + max(right.values()).bit_length()
    slot += min(len(left), len(right)).bit_length() + 1
    first = sum(x << (slot * (i - i0)) for i, x in left.items())
    second = sum(x << (slot * (j - j0)) for j, x in right.items())
    product = first * second
    mask = (1 << slot) - 1
    return {
        i0 + j0 + k: coefficient
        for k in range(span)
        if (coefficient := (product >> (slot * k)) & mask)
    }


def allowed(v, primes):
    n = abs(v)
    if n == 0:
        return False
    for p in primes:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return False
    return n == 1


def replay():
    fibers = masses = nonzero = 0
    for a, b in ((1, 2), (1, 3), (2, 3), (2, 5), (3, 5)):
        delta = b - a
        w = a * b * delta
        y_max = 10
        for x_max in (7, 10):
            for q in (1, 2, 3):
                for shift in range(q):
                    def condition(t, k):
                        return (2 * t + 3 * k - shift) % q == 0

                    xs = [x for x in range(-x_max, x_max + 1) if allowed(31 + 3 * x, (2, 3, 5, 7, 11, 13, 17, 19, 23, 31))]
                    ys = [y for y in range(-y_max, y_max + 1) if allowed(17 - 2 * y, (2, 3, 5, 7, 11, 13, 17, 19, 23, 31))]
                    packed = defaultdict(int)
                    for r in range(delta):
                        for ci in range(q):
                            for cj in range(q):
                                if not condition(r + b * ci - a * cj, cj - ci):
                                    continue
                                left = {
                                    b * i: 1 << (b * x * x)
                                    for x in xs
                                    if (x - r) % delta == 0 and (i := (x - r) // delta) % q == ci
                                }
                                right = {
                                    -a * j: 1 << (a * (y_max * y_max - y * y))
                                    for y in ys
                                    if (y - r) % delta == 0 and (j := (y - r) // delta) % q == cj
                                }
                                for k, value in integer_convolution(left, right).items():
                                    packed[r + k] += value
                    for t in range(-12, 13):
                        got = Fraction(packed[t], 1 << (a * y_max * y_max + delta * t * t))
                        direct = sum(
                            (Fraction(1, 1 << (w * k * k))
                             for k in range(-25, 26) if condition(t, k) and t + a*k in xs and t + b*k in ys),
                            Fraction(0),
                        )
                        assert got == direct
                        masses += 1
                        nonzero += got > 0
                    fibers += 1
    return fibers, masses, nonzero


if __name__ == "__main__":
    print("mark and congruence cases, all fiber masses, positive masses:", *replay())
