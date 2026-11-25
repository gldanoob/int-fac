"""Exact controls for the masked crossing and the low/high digit cut."""

from collections import defaultdict
from itertools import product
from math import gcd


def sparse_rank(rows, prime):
    pivots = {}
    for row in rows:
        row = dict(row)
        while row:
            j = min(row)
            first = row[j]
            if j not in pivots:
                inverse = pow(first, -1, prime)
                pivots[j] = {key: value * inverse % prime for key, value in row.items()}
                break
            for key, coefficient in pivots[j].items():
                value = (row.get(key, 0) - first * coefficient) % prime
                if value:
                    row[key] = value
                else:
                    row.pop(key, None)
    return len(pivots)


def check_masked_tensor():
    entries = blocks = 0
    for width in range(1, 5):
        odds = range(1, 2 ** width, 2)
        for w in range(1, width + 1):
            modulus = 2 ** w
            for target in range(1, modulus, 2):
                def decode(value, inverse_side):
                    residue = value % modulus
                    if inverse_side:
                        residue = target * pow(residue, -1, modulus) % modulus
                    return (residue - 1) // 2, value // modulus

                for x, y, u, v in product(odds, repeat=4):
                    rx, hx = decode(x, False)
                    ry, hy = decode(y, True)
                    ru, hu = decode(u, True)
                    rv, hv = decode(v, False)
                    arith = x == v and y == u and (x * y - target) % modulus == 0
                    factored = rx == ry == ru == rv and hx == hv and hy == hu
                    assert arith == factored
                    entries += 1
                blocks += 1
    return blocks, entries


def line_parameters(k, m, target):
    low_modulus = 2 ** k
    high_modulus = 2 ** m
    for a in range(1, low_modulus, 2):
        b = target * pow(a, -1, low_modulus) % low_modulus
        inverse = pow(a, -1, high_modulus)
        slope = -b * inverse % high_modulus
        intercept = (target - a * b) // low_modulus * inverse % high_modulus
        yield a, b, slope, intercept


def check_digit_cuts():
    row_count = private_minors = tested_ranks = private_columns = 0
    for k, h in ((3, 3), (4, 4), (3, 5), (5, 3), (5, 5), (6, 6), (7, 6)):
        m = min(k, h)
        modulus = 2 ** m
        for target in (1, 9, 15, 35, 105, 255, 691):
            all_rows = []
            projected_rows = {}
            for a, b, slope, intercept in line_parameters(k, m, target):
                projected = defaultdict(int)
                for x in range(modulus):
                    # The omitted high x bits are pinned to zero. Aggregate
                    # all high y values in each residue class by exact addition.
                    full_x = a + (x << k)
                    for y in range(2 ** h):
                        full_y = b + (y << k)
                        if (full_x * full_y - target) % (1 << (k + h)) == 0:
                            projected[x, y % modulus] += 1
                predicted = {(x, (slope * x + intercept) % modulus): 1 for x in range(modulus)}
                assert projected == predicted
                projected_rows.setdefault(slope, predicted)
                all_rows.append(projected)
                row_count += 1

            start = -target % 8
            expected = list(range(start, modulus, 8))
            assert sorted(projected_rows) == expected
            t = 0
            while 2 ** (t + 1) <= len(expected) and 4 * (t + 1) * 2 ** (t + 1) < modulus:
                t += 1
            slopes = expected[:2 ** t]
            for slope in slopes:
                others = set()
                intersections = 0
                for other_slope in slopes:
                    if other_slope != slope:
                        other = projected_rows[other_slope].keys()
                        overlap = len(projected_rows[slope].keys() & other)
                        assert overlap <= gcd(slope - other_slope, modulus)
                        intersections += gcd(slope - other_slope, modulus)
                        others.update(other)
                assert intersections == 4 * t * 2 ** t
                assert projected_rows[slope].keys() - others
                private_columns += 1
            private_minors += 1
            for prime in (2, 3, 5):
                rank = sparse_rank(all_rows, prime)
                assert rank >= (2 ** t if prime == 2 else len(expected))
                tested_ranks += 1
    return row_count, private_minors, private_columns, tested_ranks


if __name__ == "__main__":
    print("masked tensors, literal entries", *check_masked_tensor())
    print("projected rows, private minors, private columns, field ranks", *check_digit_cuts())
