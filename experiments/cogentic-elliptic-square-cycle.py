#!/usr/bin/env python3
"""Check the fixed square-cycle sextic and its elliptic source of rational marks."""

from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).parent
GRAPH = run_path(str(HERE / "cogentic-unramified-mark-graph.py"))
binary_rank, divide_monic, evaluate, multiply = (
    GRAPH[name] for name in ("binary_rank", "divide_monic", "evaluate", "multiply")
)

MARKS = (51, 95, 57, 85)
K = prod(a - MARKS[0] for a in MARKS[1:])
SEED = (K, -942480)
CURVE = (80568576, 753984, 1964, 1)


def polynomial_remainder(dividend, monic, prime):
    _, remainder = divide_monic(dividend, monic)
    remainder = [c % prime for c in remainder]
    while remainder and remainder[-1] == 0:
        remainder.pop()
    return remainder


def polynomial_gcd(a, b, prime):
    while b:
        inverse = pow(b[-1], -1, prime)
        b = [c * inverse % prime for c in b]
        a, b = b, polynomial_remainder(a, b, prime)
    return a


def check_irreducibility():
    a = multiply([-51, 1], [-95, 1])
    b = multiply([-57, 1], [-85, 1])
    f = multiply(multiply(a, b), [a[0] - 1, *a[1:]])
    f[1] += 1
    assert [u - v for u, v in zip(a, b, strict=True)] == [0, -4, 0]
    s = [1 - 2*a[0], -2*a[1], -2*a[2]]
    b_s_squared = multiply(b, multiply(s, s))
    assert [u - v for u, v in zip(a + [0]*4, b_s_squared, strict=True)] == [-4*c for c in f]
    prime = 13
    f = [c % prime for c in f]
    assert f == [c % prime for c in (-2, 4, -5, -1, 3, -5, 1)]
    x = [0, 1]
    expected = {2: (6, 2, -3, -4, 3, 5), 3: (5, -1, -5, -4, 2, 4), 6: ()}
    for k in range(1, 7):
        power = [1]
        for _ in range(prime):
            power = polynomial_remainder(multiply(power, x), f, prime)
        x = power
        if k in expected:
            difference = x + [0]*max(0, 2 - len(x))
            difference[1] -= 1
            difference = polynomial_remainder(difference, f, prime)
            assert difference == [c % prime for c in expected[k]]
            assert polynomial_gcd(f, difference, prime) == (f if k == 6 else [1])


def add(left, right, prime=None):
    if left is None:
        return right
    if right is None:
        return left
    x, y = left
    u, v = right
    if x == u:
        opposite = (y + v) % prime == 0 if prime else y + v == 0
        if opposite:
            return None
        dy, dx = 3*x*x + 2*CURVE[2]*x + CURVE[1], 2*y
    else:
        dy, dx = v - y, u - x
    slope = dy * pow(dx, -1, prime) % prime if prime else dy / dx
    w = slope*slope - CURVE[2] - x - u
    z = slope*(x - w) - y
    return (w % prime, z % prime) if prime else (w, z)


def multiple(n, point):
    result = None
    for bit in bin(n)[2:]:
        result = add(result, result)
        if bit == "1":
            result = add(result, point)
    return result


def check_curve():
    roots = [K // (MARKS[0] - a) for a in MARKS[1:]]
    cubic = [1]
    quartic = [1]
    for root in roots:
        cubic = multiply(cubic, [-root, 1])
    for a in MARKS:
        quartic = multiply(quartic, [-K, MARKS[0] - a])
    # This homogeneous identity gives y^2=A(m)B(m) under the rational map.
    assert cubic == list(CURVE) and quartic[:-1] == [K*K*c for c in cubic] and quartic[-1] == 0
    discriminant = 16 * prod((a - b)**2 for a, b in combinations(roots, 2))
    quartic_discriminant = prod((a - b)**2 for a, b in combinations(MARKS, 2))
    assert discriminant == 16*quartic_discriminant == 2**20 * (3*5*7*11*17*19)**2
    assert SEED[1]**2 == evaluate(CURVE, SEED[0])

    orders = {13: 10, 23: 16, 29: 18, 31: 5, 313: 81}
    for prime, order in orders.items():
        assert discriminant % prime
        seed = tuple(c % prime for c in SEED)
        point = seed
        for _ in range(1, order):
            assert point is not None
            point = add(point, seed, prime)
        assert point is None
    # At odd good primes the 2-primary part of rational torsion injects on reduction.
    assert (orders[23] & -orders[23], orders[29] & -orders[29]) == (16, 2)
    return orders


def check_descent():
    points = [(-1496, 0), (-264, 0), (-1344, 13680), (-544, 9520), (-280, 1216)]
    primes = (2, 7, 11, 17, 19)
    masks = []
    for x, y in points:
        assert y*y == evaluate(CURVE, x)
        value = x + 1496 or (1496 - 264)*(1496 - 204)
        mask = 0
        for i, prime in enumerate(primes):
            while value % prime == 0:
                mask ^= 1 << i
                value //= prime
        masks.append(mask)
    assert binary_rank(masks) == len(points)
    return len(points)


def specialization(point):
    x, y = point
    assert y*y == evaluate(CURVE, x)
    m, root = MARKS[0] - K/x, -K*y/(x*x)
    a = (m - 51)*(m - 95)
    b = (m - 57)*(m - 85)
    f, s = m + a*b*(a - 1), 1 - 2*a
    assert a - b == -4*m and a - b*s*s == -4*f and a*b == root*root
    return m, root, f, b*s


def reduce_fraction(value, modulus):
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def search(modulus, limit):
    point = None
    seed = tuple(map(Fraction, SEED))
    for index in range(1, limit + 1):
        point = add(point, seed)
        m, root, value, algebraic = specialization(point)
        if value.numerator % modulus or gcd(m.denominator * root.denominator, modulus) != 1:
            continue
        integer_root = reduce_fraction(root, modulus)
        algebraic_root = reduce_fraction(algebraic, modulus)
        assert (algebraic_root**2 - integer_root**2) % modulus == 0
        factors = tuple(gcd(algebraic_root + sign*integer_root, modulus) for sign in (-1, 1))
        if all(1 < factor < modulus for factor in factors):
            return index, factors
    return None


def check_balanced(seed):
    m, root, f, _ = specialization(multiple(161, seed))
    u, w = m.as_integer_ratio()
    a, b = (u - 51*w)*(u - 95*w), (u - 57*w)*(u - 85*w)
    v, z = isqrt(a//5), isqrt(b//5)
    assert 5*v*v == a and 5*z*z == b
    s = w*w - 2*a
    f_h = u*w**5 + a*b*(a - w*w)
    assert f_h == f.numerator and f.denominator == w**6

    plus, minus = -z*s + v*w*w, -z*s - v*w*w
    assert 5*plus*minus == 4*f_h
    left, left_remainder = divmod(minus, 38812)
    right, right_remainder = divmod(plus, 10)
    n, remainder = divmod(f_h, 485150)
    assert not (left_remainder or right_remainder or remainder)
    assert 1 < left < right < 4096*left and left*right == n and gcd(left, right) == 1
    assert gcd(n, 2*3*5*7*11*13*17*19*23*29*31*313) == 1
    assert root*w*w == 5*v*z and gcd(n, w*v*z) == 1
    assert (gcd(n, b*s + 5*v*z*w*w), gcd(n, b*s - 5*v*z*w*w)) == (left, right)
    return n.bit_length(), (left.bit_length(), right.bit_length())


def replay():
    check_irreducibility()
    orders = check_curve()
    descent_rank = check_descent()
    seed = tuple(map(Fraction, SEED))
    assert specialization(seed) == (50, 105, 485150, -21805)
    assert search(9703, 1) == (1, (313, 31))

    assert multiple(2, seed) == (Fraction(16120, 9), Fraction(-3134528, 27))
    m, root, value, algebraic = specialization(multiple(2, seed))
    assert (m, root) == (Fraction(92667, 2015), Fraction(1318852656, 4060225))
    modulus = 33873417617833492629436999
    assert modulus.bit_length() == 85 and value.numerator == 51*modulus
    assert reduce_fraction(algebraic / root, modulus) == 7774315739127991393880527
    assert search(modulus, 1) is None
    index, factors = search(modulus, 4)
    assert index == 2 and set(factors) == {5829071504407, 5811117189457} and prod(factors) == modulus
    bits, lengths = check_balanced(seed)
    print(f"Sextic irreducible modulo 13, seed orders {orders}, descent rank {descent_rank}.")
    print("m=50 splits 9703 into 31 and 313.")
    print(f"Seed scan splits the 85-bit input at {index}P into {factors}.")
    print(f"161P gives a {bits}-bit modulus after dividing F_h by 485150, with coprime factors of {lengths} bits.")


if __name__ == "__main__":
    replay()
