"""Search a bounded unit chart for local collisions by monic multipoint evaluation."""

import argparse
import json
from itertools import combinations
from math import gcd

from sage.all import PolynomialRing, Zmod


def product_tree(leaves):
    layers = [leaves]
    while len(layers[-1]) > 1:
        row = layers[-1]
        layer = [row[i]*row[i+1] for i in range(0, len(row)-1, 2)]
        if len(row) % 2:
            layer.append(row[-1])
        layers.append(layer)
    return layers


def evaluate(poly, tree):
    residues = [poly % tree[-1][0]]
    for row in reversed(tree[:-1]):
        residues = [residues[j//2] % modulus for j, modulus in enumerate(row)]
    return [int(value[0]) for value in residues]


def indexed_residues(n, values):
    indices = {}
    for i, value in enumerate(values):
        indices.setdefault(value % n, i)
    return indices


def local_collision(n, left, right):
    """Return a witnessed proper gcd from a nonidentical cross difference."""
    if n < 2:
        raise ValueError("require modulus N >= 2")
    left = indexed_residues(n, left)
    right = indexed_residues(n, right)
    if not left or not right:
        return None

    ring = PolynomialRing(Zmod(n), "X", implementation="NTL")
    x = ring.gen()
    polynomial = product_tree([x-y for y in right])[-1][0]
    tree = product_tree([x-a for a in left])
    values = evaluate(polynomial, tree)
    derivatives = evaluate(polynomial.derivative(), tree)

    for (a, i), value, derivative in zip(left.items(), values, derivatives, strict=True):
        exact = a in right
        bucket = gcd(derivative if exact else value, n)
        if bucket == 1:
            continue
        # Recover a pair even when the product gcd is saturated.
        for b, j in right.items():
            if a == b:
                continue
            divisor = gcd(a-b, n)
            if 1 < divisor < n:
                return dict(factor=divisor, left_index=i, right_index=j,
                            left=a, right=b, bucket_gcd=bucket, exact_root=exact)
        raise ArithmeticError("nonunit bucket contained no nonidentical local hit")
    return None


def square_alignment(n, left, right):
    """Find any globally equal squares and any such pair with a proper signed gcd."""
    if n < 2:
        raise ValueError("require modulus N >= 2")
    by_square = {}
    for j, y in enumerate(right):
        y %= n
        group = by_square.setdefault(y*y % n, {})
        # With two distinct sign classes, at least one differs from any left root.
        if len(group) < 2:
            group.setdefault(min(y, -y % n), (j, y))
    aligned = None
    for i, x in enumerate(left):
        x %= n
        for j, y in by_square.get(x*x % n, {}).values():
            pair = dict(i=i, j=j, x=x, y=y)
            if aligned is None:
                aligned = pair
            for sign in (1, -1):
                divisor = gcd(x-sign*y, n)
                if 1 < divisor < n:
                    return aligned, dict(pair, sign=sign, factor=divisor)
    return aligned, None


def progression(n, first, multiplier, length):
    values = []
    for _ in range(length):
        values.append(first)
        first = first*multiplier % n
    return values


def search(n, t, left_length, right_length):
    if n < 2 or min(left_length, right_length) < 0:
        raise ValueError("require N >= 2 and nonnegative progression lengths")
    result = dict(n=n, t=t, left_length=left_length, right_length=right_length)
    if n == 2:
        return dict(result, status="prime")
    if n % 2 == 0:
        return dict(result, status="even", factor=2, cofactor=n//2)
    parameter_checks = [("t", t), ("t-1", t-1), ("t+1", t+1), ("t^2+1", t*t+1)]
    gcds = [(name, gcd(value, n)) for name, value in parameter_checks]
    for name, divisor in gcds:
        if 1 < divisor < n:
            return dict(result, status="parameter-gcd", parameter_check=name,
                        factor=divisor, cofactor=n//divisor)
    if any(divisor == n for _, divisor in gcds):
        return dict(result, status="ineligible")

    left_base = t*(t-1)*pow(t+1, -1, n) % n
    right_base = left_base*pow(t*t, -1, n) % n
    inverse_two = pow(2, -1, n)
    left = progression(n, (left_base+1)*inverse_two % n, left_base, left_length)
    right = progression(n, (right_base-1)*inverse_two % n, right_base, right_length)
    aligned, aligned_split = square_alignment(n, left, right)
    hit = local_collision(n, left, (signed for y in right for signed in (y, -y)))
    result.update(global_alignment=aligned, global_split=aligned_split)
    if hit is None:
        if aligned_split is not None:
            raise ArithmeticError("globally aligned split missing from local search")
        return dict(result, status="box-exhausted")
    i = hit["left_index"]
    j, sign_bit = divmod(hit["right_index"], 2)
    x, y = left[i], right[j]
    divisor = hit["factor"]
    return dict(result, status="local-split", factor=divisor, cofactor=n//divisor,
                witness=dict(i=i, j=j, sign=1-2*sign_bit, x=x, y=y,
                             globally_aligned=(x*x-y*y) % n == 0,
                             bucket_gcd=hit["bucket_gcd"], exact_root=hit["exact_root"]))


def replay():
    assert local_collision(35, [], [2]) is None and local_collision(35, [2], []) is None
    assert local_collision(35, [2, 37], [2, 2, 37]) is None
    hit = local_collision(35, [2], [2, 2, 9])
    assert hit["factor"] == 7 and hit["right_index"] == 2 and hit["exact_root"]
    hit = local_collision(35, [1], [6, 8])
    assert hit["factor"] == 5 and hit["bucket_gcd"] == 35
    hit = local_collision(35, [2], [2, 7, 9])
    assert hit["factor"] == 5 and hit["bucket_gcd"] == 35 and hit["exact_root"]
    hit = local_collision(125, [1], [6, 26])
    assert hit["factor"] == 5 and hit["bucket_gcd"] == 125
    p, q = (1 << 32)+15, (1 << 32)+61
    assert local_collision(p*q, [1], [1+p])["factor"] == p
    assert square_alignment(15, [2], [7])[1]["factor"] == 5
    assert square_alignment(25, [5], [5])[1]["factor"] == 5

    checked = 0
    for n in (2, 4, 6, 8, 9):
        lists = [values for size in range(3) for values in combinations(range(n), size)]
        for left in lists:
            for right in lists:
                expected = {gcd(x-y, n) for x in left for y in right} - {1, n}
                hit = local_collision(n, left, right)
                assert (hit is not None) == bool(expected)
                if hit:
                    assert hit["factor"] in expected
                pairs = [(x, y) for x in left for y in right if (x*x-y*y) % n == 0]
                aligned, aligned_split = square_alignment(n, left, right)
                assert (aligned is not None) == bool(pairs)
                assert (aligned_split is not None) == any(
                    1 < gcd(x-sign*y, n) < n for x, y in pairs for sign in (1, -1))
                checked += 1
    result = search(341, 2, 3, 3)
    assert result["status"] == "local-split" and result["factor"] in (11, 31)
    assert result["global_split"]["i"] == result["global_split"]["j"] == 2
    assert result["global_split"]["factor"] in (11, 31)
    local_only = search(77, 2, 3, 3)
    assert local_only["factor"] == 11 and local_only["global_alignment"] is None
    assert search(77, 2, 0, 3)["status"] == "box-exhausted"
    assert search(35, 2, 3, 3)["status"] == "parameter-gcd"
    print(f"{checked} brute-force comparisons plus duplicate, saturation, prime-power and unit controls")
    print(json.dumps(result))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="?", help="modulus, or omit to replay the fixed checks")
    parser.add_argument("--t", type=int, default=2, help="unit chart parameter")
    parser.add_argument("--left", type=int, default=256, help="number of left exponents starting at zero")
    parser.add_argument("--right", type=int, default=256, help="number of right exponents starting at zero")
    args = parser.parse_args()
    if args.n is None:
        replay()
    else:
        try:
            print(json.dumps(search(args.n, args.t, args.left, args.right)))
        except ValueError as error:
            parser.error(str(error))
