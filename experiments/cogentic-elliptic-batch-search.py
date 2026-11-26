#!/usr/bin/env python3
"""Replay two-list sextic detection on the fixed elliptic curve."""

from functools import cache
from math import gcd, prod
from pathlib import Path
from runpy import run_path

from sage.all import PolynomialRing, ZZ, Zmod


CYCLE = run_path(str(Path(__file__).with_name("cogentic-elliptic-square-cycle.py")))
CURVE = CYCLE["CURVE"]
SEED = CYCLE["SEED"]
add_over_prime = CYCLE["add"]
EXCEPTIONAL = (2, 3, 5, 7, 11, 17, 19)
SIGNS = (1, -1)
LEAF_DEGREE = 15


def sextic(x):
    numerator = 51*x - 8976
    a = (numerator - 51*x)*(numerator - 95*x)
    b = (numerator - 57*x)*(numerator - 85*x)
    return numerator*x**5 + a*b*(a - x*x)


def translation_coefficients(x, u):
    p = sum(coefficient*u**i for i, coefficient in enumerate(CURVE))
    derivative = 3*u*u + 2*CURVE[2]*u + CURVE[1]
    delta = x - u
    s = 2*p + derivative*delta + u*delta**2
    k = (derivative**2 - 4*p*(2*u + CURVE[2])
         + (2*derivative*u - 4*p)*delta + u*u*delta**2)
    return delta, s, k


@cache
def addition_resultant():
    ring = PolynomialRing(ZZ, names=("x", "u", "t"))
    x, u, t = ring.gens()
    delta, s, k = translation_coefficients(x, u)
    quadratic = delta**2*t*t - 2*s*t + k
    resultant = sextic(t).resultant(quadratic, t)
    return [(i, j, int(value)) for (i, j, _), value in resultant.dict().items()]


def leaf_polynomial(ring, baby):
    x = ring.gen()
    if baby is None:
        return x**3 * sextic(x)**2
    u = ring.base_ring()(baby[0])
    delta, _, at_zero = translation_coefficients(x, u)
    resultant = sum(coefficient*u**j*x**i for i, j, coefficient in addition_resultant())
    return delta * at_zero * resultant


def product_tree(leaves):
    levels = [leaves]
    while len(levels[-1]) > 1:
        row = levels[-1]
        levels.append([prod(row[i:i+2]) for i in range(0, len(row), 2)])
    return levels


def value_tree(ring, points):
    return product_tree([ring.gen() - point for point in points])


def evaluate_many(polynomial, tree):
    remainders = [polynomial % tree[-1][0]]
    for row in reversed(tree[:-1]):
        remainders = [remainders[i//2] % divisor for i, divisor in enumerate(row)]
    return [remainder[0] for remainder in remainders]


def collision_factor(ring, modulus, points):
    if len(points) < 2:
        return None
    tree = value_tree(ring, points)
    for i, value in enumerate(evaluate_many(tree[-1][0].derivative(), tree)):
        divisor = gcd(int(value), modulus)
        if divisor == 1:
            continue
        if divisor < modulus:
            return divisor
        point, node = points[i], i
        for level, row in enumerate(tree[:-1]):
            sibling = node ^ 1
            node //= 2
            if sibling >= len(row):
                continue
            divisor = gcd(int(row[sibling](point)), modulus)
            if divisor != 1:
                break
        else:
            raise AssertionError("a nonunit derivative has a nonunit sibling product")
        while divisor == modulus and level:
            level -= 1
            sibling *= 2
            divisor = gcd(int(tree[level][sibling](point)), modulus)
            if divisor == 1:
                sibling += 1
                divisor = gcd(int(tree[level][sibling](point)), modulus)
        assert 1 < divisor < modulus
        return divisor
    return None


def add_mod(left, right, modulus):
    if left is None or right is None:
        return (right if left is None else left), None
    x, y = left
    u, v = right
    numerator, denominator = v - y, u - x
    divisor = gcd(denominator, modulus)
    if divisor == modulus:
        divisor = gcd(y + v, modulus)
        if divisor == modulus:
            return None, None
        numerator, denominator = 3*x*x + 2*CURVE[2]*x + CURVE[1], 2*y
    if divisor != 1:
        return None, divisor
    slope = numerator*pow(denominator, -1, modulus) % modulus
    w = (slope*slope - CURVE[2] - x - u) % modulus
    return (w, (slope*(x - w) - y) % modulus), None


def check_chart(point, modulus):
    if point is None:
        return None, False
    x, y = point
    divisor = gcd(x, modulus)
    if divisor == modulus:
        return None, False
    if divisor != 1:
        return divisor, False
    divisor = gcd(sextic(x), modulus)
    if divisor == 1:
        return None, False
    if divisor < modulus:
        return divisor, False
    inverse = pow(x, -1, modulus)
    m = (51 - 8976*inverse) % modulus
    a = (m - 51)*(m - 95) % modulus
    b = (m - 57)*(m - 85) % modulus
    root = -8976*y*inverse**2 % modulus
    comparison = b*(1 - 2*a) % modulus
    assert (comparison**2 - root**2) % modulus == 0
    divisor = gcd(comparison - root, modulus)
    return (divisor, False) if 1 < divisor < modulus else (None, True)


def batch_search(modulus, babies, giants):
    """Return a factor or the signed global hits, with duplicate baby x's coalesced."""
    if modulus <= 1:
        raise ValueError("expected a modulus greater than one")
    exceptional = next((p for p in EXCEPTIONAL if modulus % p == 0), None)
    if exceptional is not None:
        if exceptional == modulus:
            raise ValueError("expected good odd reduction")
        return exceptional, set()
    if not babies or not giants:
        return None, set()
    for points in (babies, giants):
        for point in points:
            if point is not None:
                x, y = point
                if (y*y - sum(c*x**j for j, c in enumerate(CURVE))) % modulus:
                    raise ValueError("point is not on the fixed curve modulo the input")
    ring = PolynomialRing(Zmod(modulus), "x")
    representatives = {}
    for i, baby in enumerate(babies):
        x = None if baby is None else baby[0] % modulus
        if x is not None and x in representatives:
            divisor = gcd(baby[1] - babies[representatives[x]][1], modulus)
            if 1 < divisor < modulus:
                return divisor, set()
        representatives.setdefault(x, i)
    indices = list(representatives.values())
    divisor = collision_factor(ring, modulus, [x for x in representatives if x is not None])
    if divisor is not None:
        return divisor, set()
    tree = product_tree([leaf_polynomial(ring, babies[i]) for i in indices])
    hits = set()
    active = {0: list(range(len(giants)))}
    for level in reversed(range(len(tree))):
        next_active = {}
        for node, queries in active.items():
            polynomial = tree[level][node]
            finite = [j for j in queries if giants[j] is not None]
            if finite:
                evaluation = value_tree(ring, [giants[j][0] for j in finite])
                values = dict(zip(finite, evaluate_many(polynomial, evaluation), strict=True))
            else:
                values = {}
            count = min(2**level, len(indices) - node*2**level)
            for j in queries:
                value = values[j] if j in values else polynomial[LEAF_DEGREE*count]
                divisor = gcd(int(value), modulus)
                if divisor == 1:
                    continue
                if divisor < modulus:
                    return divisor, hits
                if level:
                    for child in range(2*node, min(2*node + 2, len(tree[level - 1]))):
                        next_active.setdefault(child, []).append(j)
                    continue
                i = indices[node]
                baby = babies[i]
                for sign in SIGNS:
                    signed_baby = None if baby is None else (baby[0], sign*baby[1] % modulus)
                    point, divisor = add_mod(giants[j], signed_baby, modulus)
                    if divisor is not None:
                        return divisor, hits
                    divisor, hit = check_chart(point, modulus)
                    if divisor is not None:
                        return divisor, hits
                    if hit:
                        hits.add((i, j, sign))
        active = next_active
    return None, hits


def local_hits(prime, babies, giants):
    def reduce_point(point):
        return None if point is None else tuple(value % prime for value in point)

    hits = set()
    for i, baby in enumerate(map(reduce_point, babies)):
        for j, giant in enumerate(map(reduce_point, giants)):
            for sign in SIGNS:
                signed_baby = None if baby is None else (baby[0], sign*baby[1] % prime)
                point = add_over_prime(giant, signed_baby, prime)
                if point is not None and sextic(point[0]) % prime == 0:
                    hits.add((i, j, sign))
    return hits


def crt_point(left, right, p, q):
    return tuple((a + p*((b - a)*pow(p, -1, q) % q)) % (p*q)
                 for a, b in zip(left, right, strict=True))


def replay():
    p, q = 23, 47
    modulus = p*q
    giant = tuple(value % modulus for value in SEED)
    left = crt_point((8, 21), (1, 7), p, q)
    right = crt_point((3, 0), (35, 35), p, q)
    exact = crt_point((8, 21), (35, 35), p, q)
    mixed = crt_point((8, 21), (35, 12), p, q)
    inert = crt_point((0, 6), (2, 6), p, q)
    assert local_hits(p, [left, right], [giant]) == {(0, 0, 1)}
    assert local_hits(q, [left, right], [giant]) == {(1, 0, 1)}
    ring = PolynomialRing(Zmod(modulus), "x")
    product = prod(leaf_polynomial(ring, baby) for baby in (left, right))
    assert gcd(int(product(giant[0])), modulus) == modulus
    assert batch_search(modulus, [left, right], [giant])[0] in (p, q)
    assert batch_search(modulus, [mixed], [giant])[0] in (p, q)
    assert batch_search(modulus, [left, inert], [giant])[0] == p
    assert batch_search(modulus, [exact, inert], [giant]) == (None, {(0, 0, 1)})
    productive = crt_point((18, 10), (13, 11), p, q)
    assert batch_search(modulus, [productive], [None])[0] in (p, q)
    target = crt_point((18, 10), (13, 36), p, q)
    assert batch_search(modulus, [target], [None]) == (None, {(0, 0, 1), (0, 0, -1)})
    assert batch_search(modulus, [None], [target]) == (None, {(0, 0, 1), (0, 0, -1)})
    zero_abscissa = crt_point((0, 6), (1, 7), p, q)
    assert batch_search(modulus, [zero_abscissa], [None])[0] == p
    equal_abscissa = crt_point((6, 14), (1, 7), p, q)
    assert not local_hits(p, [equal_abscissa], [giant])
    assert not local_hits(q, [equal_abscissa], [giant])
    assert batch_search(modulus, [equal_abscissa], [giant])[0] == p
    two_torsion = (-204 % modulus, 0)
    assert batch_search(modulus, [two_torsion], [two_torsion]) == (None, set())
    collision = crt_point((8, 2), (2, 6), p, q)
    assert batch_search(modulus, [left, collision], [giant])[0] == p
    collision_q = crt_point((3, 0), (1, 7), p, q)
    assert batch_search(modulus, [left, collision, collision_q], [giant])[0] in (p, q)
    assert batch_search(modulus, [exact, mixed], [giant])[0] == p

    x, y = 8, 21
    error = sum(c*x**j for j, c in enumerate(CURVE)) - y*y
    lifted_left = crt_point((x, y + p*(error//p * pow(2*y, -1, p) % p)), (1, 7), p*p, q)
    powered_modulus = p*p*q
    assert batch_search(powered_modulus, [lifted_left], [SEED])[0] in (p, p*p)

    p, q = 71, 101
    double_hit = crt_point((41, 13), (31, 8), p, q)
    opposite = (double_hit[0], -double_hit[1] % (p*q))
    assert batch_search(p*q, [double_hit], [double_hit]) == (None, {(0, 0, 1)})
    assert batch_search(p*q, [double_hit], [opposite]) == (None, {(0, 0, -1)})

    checked = 0
    for prime in (23, 47, 53, 71):
        points = [None] + [(x, y) for x in range(prime) for y in range(prime)
                           if (y*y - sum(c*x**j for j, c in enumerate(CURVE))) % prime == 0]
        babies = list({None if point is None else point[0]: point for point in points}.values())
        ring = PolynomialRing(Zmod(prime), "x")
        for baby in babies:
            polynomial = leaf_polynomial(ring, baby)
            for giant in points:
                retained = baby is not None and giant is not None and baby[0] == giant[0]
                for sign in SIGNS:
                    signed_baby = None if baby is None else (baby[0], sign*baby[1] % prime)
                    result = add_over_prime(giant, signed_baby, prime)
                    retained |= result is not None and (result[0] == 0 or sextic(result[0]) % prime == 0)
                value = polynomial[LEAF_DEGREE] if giant is None else polynomial(giant[0])
                assert (value == 0) == retained
        assert batch_search(prime, babies, points) == (None, local_hits(prime, babies, points))
        checked += len(babies)*len(points)
    print(f"Batch detector matches exhaustive addition on {checked} pairs over four good primes.")
    print("Composite fixtures cover split leaves, signed hits, square splits, poles, and collisions.")


if __name__ == "__main__":
    replay()
