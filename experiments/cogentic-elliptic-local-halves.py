#!/usr/bin/env python3
"""Check the seven elliptic doubling targets over small good prime fields."""

from collections import deque
from itertools import permutations, product
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).parent
EXACT = run_path(str(HERE / "cogentic-elliptic-square-cycle.py"))
CURVE, add, binary_rank, evaluate = (
    EXACT[name] for name in ("CURVE", "add", "binary_rank", "evaluate")
)
MODULAR = run_path(str(HERE / "cogentic-elliptic-cycle-split.py"))
add_mod = MODULAR["add"]
AXES = ((-1344, 13680), (-544, 9520), (-280, 1216))
ROOTS = (-1496, -264, -204)
CLASSES = ((2*19, 2*7*17, 19), (-2*3*5, -2*5*7, -1))


def good_primes(limit):
    for p in range(3, limit, 2):
        if p not in MODULAR["BAD_PRIMES"] and all(p % d for d in range(3, isqrt(p) + 1, 2)):
            yield p


def check_class_rank():
    generators = (2, 3, 5, 7, 17, 19)
    for root, classes in zip(ROOTS[:2], CLASSES, strict=True):
        for (x, y), value in zip(AXES, classes, strict=True):
            ratio, remainder = divmod(x - root, value)
            assert not remainder and ratio > 0 and isqrt(ratio)**2 == ratio
            assert y*y == evaluate(CURVE, x)
    masks = [((value < 0) << len(generators))
             | sum(1 << j for j, p in enumerate(generators) if value % p == 0)
             for row in CLASSES for value in row]
    assert binary_rank(masks) == 6


def kummer(point, p):
    if point is None:
        return (0, 0)
    x, _ = point
    values = [x - root if (x - root) % p else prod(root - other for other in ROOTS if other != root)
              for root in ROOTS[:2]]
    return tuple(int(pow(value, (p - 1)//2, p) == p - 1) for value in values)


def targets(axes, plus):
    points = [None]
    for axis in axes:
        points += [plus(point, axis) for point in points]
    return points


def generated(axes, plus, p):
    words = {None: ()}
    queue = deque([None])
    signed_axes = (*axes, *((x, -y % p) for x, y in axes))
    while queue:
        point = queue.popleft()
        for i, axis in enumerate(signed_axes):
            next_point = plus(point, axis)
            if next_point not in words:
                words[next_point] = (*words[point], i)
                queue.append(next_point)
    return words


def local_table(p):
    def plus(left, right):
        return add(left, right, p)

    axes = tuple((x % p, y % p) for x, y in AXES)
    points = {None} | {(x, y) for x, y in product(range(p), repeat=2)
                       if (y*y - evaluate(CURVE, x)) % p == 0}
    doubles = {plus(point, point) for point in points}
    assert doubles == {point for point in points if kummer(point, p) == (0, 0)}
    rows = tuple(sum(int(pow(value, (p - 1)//2, p) == p - 1) << j
                     for j, value in enumerate(row)) for row in CLASSES)
    sums = targets(axes, plus)
    words = generated(axes, plus, p)
    witnessed = {}
    for point, word in words.items():
        doubled = plus(point, point)
        if doubled not in witnessed or len(word) < len(witnessed[doubled]):
            witnessed[doubled] = word
    halves = {}
    for s, point in enumerate(sums[1:], 1):
        assert (point in doubles) == all((s & row).bit_count() % 2 == 0 for row in rows)
        if point in witnessed:
            halves[s] = witnessed[point]
    assert halves
    return rows, sums, halves


def sextic_rootless(p):
    for m in range(p):
        a, b = (m - 51)*(m - 95), (m - 57)*(m - 85)
        if (m + a*b*(a - 1)) % p == 0:
            return False
    return True


def half_gcd(p, q, s, word):
    n = p*q
    axes = tuple((x % n, y % n) for x, y in AXES)
    signed_axes = (*axes, *((x, -y % n) for x, y in axes))
    target = None
    for j, axis in enumerate(axes):
        if s & (1 << j):
            target = add_mod(target, axis, n)
    half = None
    for j in word:
        half = add_mod(half, signed_axes[j], n)
    doubled = add_mod(half, half, n)
    assert doubled is not None and target is not None
    return gcd(doubled[0] - target[0], doubled[1] - target[1], n)


def replay():
    check_class_rank()
    total = sum(binary_rank(rows) == 3 for rows in product(range(8), repeat=4))
    assert total == 2520
    tables = {p: local_table(p) for p in good_primes(150)}
    separated = 0
    for p, q in permutations(tables, 2):
        rows_p, _, halves = tables[p]
        rows_q, sums_q, _ = tables[q]
        if binary_rank((*rows_p, *rows_q)) < 3:
            continue
        separated += 1
        for s in halves:
            assert any((s & row).bit_count() % 2 for row in rows_q)
            assert kummer(sums_q[s], q) != (0, 0)
    print(f"Rank-three matrix stacks: {total}/4096 = 315/512.")
    print(f"Checked every target at {len(tables)} good primes and {separated} ordered rank-three prime pairs.")

    p, q = 149, 131
    assert sextic_rootless(p) and sextic_rootless(q)
    assert binary_rank((*tables[p][0], *tables[q][0])) == 3
    # Double R1 + 2R2 - R3 onto R3 mod p, and double 2R3 onto R1 mod q.
    for prime, s, word in ((p, 4, (0, 1, 1, 5)), (q, 1, (2, 2))):
        assert tables[prime][2][s] == word
        divisor = half_gcd(p, q, s, word)
        assert divisor == prime
        print(f"Rootless sextic at {p} and {q}: target {s}, word {word}, direct equality gcd {divisor}.")


if __name__ == "__main__":
    replay()
