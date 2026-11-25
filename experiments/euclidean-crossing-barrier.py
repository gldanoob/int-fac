"""Exact geometry and tensor-power controls for the Euclidean crossing deduction."""

from fractions import Fraction
from itertools import product
from math import comb, prod
from random import Random


def check_geometry():
    checked = 0
    for a, b, hypotenuse in ((3, 4, 5), (4, 3, 5), (5, 12, 13), (12, 5, 13)):
        cosine = Fraction(a, hypotenuse)
        sine = Fraction(b, hypotenuse)
        assert cosine ** 2 + sine ** 2 == 1
        # In half-angle coordinates the row hubs lie on the first axis.
        terminals = ((cosine, sine), (cosine, -sine), (-cosine, sine), (-cosine, -sine))
        for pair, other in ((0, 3), (1, 2)):
            assert sum((x - y) ** 2 for x, y in zip(terminals[pair], terminals[other])) == 4
        for t in (Fraction(1, 127), Fraction(1, 4), Fraction(1, 2), Fraction(2, 3)):
            for h, direction, signs in ((cosine, (1, 0), (1, 1, -1, -1)),
                                        (sine, (0, 1), (1, -1, 1, -1))):
                for (x, y), sign in zip(terminals, signs):
                    squared = (x - sign * t * direction[0]) ** 2 + (y - sign * t * direction[1]) ** 2
                    assert squared == 1 - 2 * h * t + t ** 2
                    upper = 1 - h * t + t ** 2 / 2
                    assert upper >= 0 and upper ** 2 >= squared
                    checked += 1
    return checked


def rank(rows, prime):
    rows = [row.copy() for row in rows]
    size = len(rows)
    pivots = 0
    for col in range(size):
        pivot = next((i for i in range(pivots, size) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[pivots], rows[pivot] = rows[pivot], rows[pivots]
        inverse = pow(rows[pivots][col], -1, prime)
        for i in range(pivots + 1, size):
            multiplier = rows[i][col] * inverse % prime
            if multiplier:
                rows[i] = [(a - multiplier * b) % prime for a, b in zip(rows[i], rows[pivots])]
        pivots += 1
    return pivots


def cuts(tensor, d, prime):
    row = [[0] * (d * d) for _ in range(d * d)]
    col = [[0] * (d * d) for _ in range(d * d)]
    for (x, y, u, v), value in tensor.items():
        row[d * x + y][d * u + v] = value
        col[d * x + u][d * y + v] = value
    return rank(row, prime), rank(col, prime)


def integer_root(n, degree):
    lo, hi = 0, 1 << ((n.bit_length() + degree - 1) // degree)
    while hi - lo > 1:
        mid = (hi + lo) // 2
        if mid ** degree <= n:
            lo = mid
        else:
            hi = mid
    return hi if hi ** degree <= n else lo


def verify_moments(ranks, d):
    scale = 10 ** 4
    for a, b, h in ((3, 4, 5), (4, 3, 5), (5, 12, 13), (12, 5, 13)):
        degree = a + b
        floored = sum(integer_root(scale ** degree * r ** a * c ** b, degree) for r, c in ranks)
        assert floored ** degree >= scale ** degree * d ** (2 * h)
    geometric = sum(integer_root(scale ** 2 * r * c, 2) for r, c in ranks)
    assert 577 ** 2 - 2 * 408 ** 2 == 1
    assert geometric ** 408 > scale ** 408 * d ** 577


def check_types():
    rng = Random(20261124)
    count = 0
    for prime in (2, 3, 5):
        for example in (0, 1):
            pieces = [dict(), dict(), dict()]
            for x, y, u, v in product(range(2), repeat=4):
                coord = (x, y, u, v)
                # The first seed contains rank-one pieces on the two competing cuts.
                if example == 0:
                    first = int(x == y and u == v)
                    second = int(x == u and y == v)
                else:
                    first, second = rng.randrange(prime), rng.randrange(prime)
                for i, value in enumerate((first, second, (x == v and y == u) - first - second)):
                    pieces[i][coord] = value % prime
            seed = [cuts(piece, 2, prime) for piece in pieces]
            verify_moments(seed, 2)
            for n in (2, 3):
                d = 2 ** n
                types = {}
                for word in product(range(3), repeat=n):
                    key = tuple(word.count(i) for i in range(3))
                    entries = types.setdefault(key, {})
                    for coord in product(range(d), repeat=4):
                        bits = [tuple((value >> j) & 1 for value in coord) for j in range(n)]
                        val = prod(pieces[i][index] for i, index in zip(word, bits))
                        entries[coord] = (entries.get(coord, 0) + val) % prime
                assert len(types) == comb(n + 2, 2)
                for x, y, u, v in product(range(d), repeat=4):
                    assert sum(t[x, y, u, v] for t in types.values()) % prime == (x == v and y == u)
                ranks = []
                for mult, tensor in types.items():
                    r, c = cuts(tensor, d, prime)
                    ways = comb(n, mult[0]) * comb(n - mult[0], mult[1])
                    assert r <= ways * prod(pair[0] ** h for pair, h in zip(seed, mult))
                    assert c <= ways * prod(pair[1] ** h for pair, h in zip(seed, mult))
                    if r:
                        ranks.append((r, c))
                    count += 1
                verify_moments(ranks, d)
    return count


if __name__ == '__main__':
    geometries = check_geometry()
    groups = check_types()
    print(f'{geometries} exact terminal distances and {groups} literal type groups passed over F2, F3 and F5.')
