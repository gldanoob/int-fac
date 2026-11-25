"""Exact all-field crossing rank certificate using nested rectangular flags."""

from math import isqrt
from random import Random


def flag_area(d, maps):
    """Extend one source line in the current source and target quotient."""
    target = d
    area = 0
    for source in range(d, 0, -1):
        if not target:
            break
        lo, hi = -1, min(maps, target)
        while hi - lo > 1:
            rank = (lo + hi) // 2
            if (maps - rank) * (target - rank) < source:
                hi = rank
            else:
                lo = rank
        target -= hi
        area += target
    return area


def lower_hull(points):
    hull = []
    for x, y in points:
        while len(hull) >= 2:
            a, b = hull[-2]
            c, e = hull[-1]
            if (e - b) * (x - c) < (y - e) * (c - a):
                break
            hull.pop()
        hull.append((x, y))
    return hull


def integral_bounds(d, scale):
    curve = [(m, flag_area(d, m)) for m in range(2 * d)]
    hull = lower_hull(curve)
    assert hull[0] == (0, d * d) and hull[-1] == (2 * d - 1, 0)
    lo, hi = 0, 0
    last_x, last_y = hull[0]
    for x, y in hull[1:]:
        delta_m, delta_f = x - last_x, last_y - y
        if delta_f < delta_m:
            break
        radicand = scale * scale * delta_m * delta_f
        root = isqrt(radicand)
        lo += 2 * root
        hi += 2 * (root + (root * root != radicand))
        last_x, last_y = x, y
    offset = scale * (last_y - last_x)
    return lo + offset, hi + offset


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            bit = row.bit_length()
            if bit not in pivots:
                pivots[bit] = row
                break
            row ^= pivots[bit]
    return len(pivots)


def binary_control():
    """All 2-by-2-by-2-by-2 binary tensors in their two literal cuts."""
    table = [flag_area(2, m) for m in range(5)]
    for tensor in range(1 << 16):
        row = [0] * 4
        col = [0] * 4
        for index in range(16):
            x, y, u, v = ((index >> shift) & 1 for shift in (3, 2, 1, 0))
            value = (tensor >> index) & 1
            col[2 * x + u] |= value << (2 * y + v)
            row[2 * x + y] |= (value ^ (x == v and y == u)) << (2 * u + v)
        assert binary_rank(row) >= table[binary_rank(col)]


def field_rank(rows, prime):
    rows = [row.copy() for row in rows]
    rank = 0
    for col in range(len(rows[0])):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inverse = pow(rows[rank][col], -1, prime)
        for i in range(rank + 1, len(rows)):
            coefficient = rows[i][col] * inverse % prime
            if coefficient:
                rows[i] = [(a - coefficient * b) % prime for a, b in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def triangular_controls():
    rng = Random(20261125)
    checks = 0
    for prime in (2, 3, 5):
        for d in range(3, 9):
            for maps in range(1, 6):
                # Arbitrary weakly increasing output dimensions, including ties.
                widths = sorted(rng.randrange(d + 1) for _ in range(d))
                first = [[[rng.randrange(prime) if x < widths[u] else 0
                           for u in range(d)] for x in range(d)] for _ in range(maps)]
                second = [[[rng.randrange(prime) for _ in range(d)]
                            for _ in range(d)] for _ in range(maps)]
                cells = [(u, v) for u in range(d) for v in range(widths[u], d)]
                if not cells:
                    continue
                rows = []
                for y, x in cells:
                    row = []
                    for u, v in cells:
                        term = sum(p[x][u] * q[y][v] for p, q in zip(first, second))
                        value = ((x == v and y == u) - term) % prime
                        if u <= y:
                            assert value == (x == v and y == u)
                        row.append(value)
                    rows.append(row)
                assert field_rank(rows, prime) == len(cells)
                checks += 1
    return checks


def main():
    binary_control()
    triangular = triangular_controls()
    scale = 10 ** 7
    assert 577 ** 2 - 2 * 408 ** 2 == 1
    for d in range(2, 325):
        lo, hi = integral_bounds(d, scale)
        assert lo ** 408 > d ** 577 * scale ** 408, d
        if d in (98, 128, 256, 324):
            print(f'd={d}, integral numerator in [{lo}, {hi}] / {scale}')
    lo, hi = integral_bounds(325, scale)
    assert 1393 ** 2 - 2 * 985 ** 2 == -1
    assert hi ** 985 < 325 ** 1393 * scale ** 985
    print(f'd=325, integral numerator in [{lo}, {hi}] / {scale}')
    print(f'All 323 dimensions certified, 65536 binary tensors and {triangular} triangular submatrices checked.')


if __name__ == '__main__':
    main()
