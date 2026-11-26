#!/usr/bin/env python3
"""Check elliptic doubling targets with and without rational two-torsion."""

from collections import Counter, deque
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
TORSION_AXES = (*AXES, (-1496, 0), (-264, 0))
TORSION_CLASSES = ((*CLASSES[0], 7*11*17*19, 7*11), (*CLASSES[1], -7*11, -3*5*7*11))
SQUARECLASS_PRIMES = (2, 3, 5, 7, 11, 17, 19)


def good_primes(limit):
    for p in range(3, limit, 2):
        if p not in MODULAR["BAD_PRIMES"] and all(p % d for d in range(3, isqrt(p) + 1, 2)):
            yield p


def root_derivative(root):
    return prod(root - other for other in ROOTS if other != root)


def class_mask(value):
    return ((value < 0) << len(SQUARECLASS_PRIMES)) | sum(
        1 << j for j, p in enumerate(SQUARECLASS_PRIMES) if value % p == 0
    )


def check_class_ranks():
    for root, classes in zip(ROOTS[:2], TORSION_CLASSES, strict=True):
        for (x, y), value in zip(TORSION_AXES, classes, strict=True):
            ratio, remainder = divmod(x - root or root_derivative(root), value)
            assert not remainder and ratio > 0 and isqrt(ratio)**2 == ratio
            assert y*y == evaluate(CURVE, x)
    assert binary_rank(class_mask(value) for row in CLASSES for value in row) == 6
    assert binary_rank(class_mask(value) for row in TORSION_CLASSES for value in row) == 8


def nonsquare(value, p):
    return int(pow(value, (p - 1)//2, p) == p - 1)


def kummer(point, p):
    if point is None:
        return (0, 0)
    x, _ = point
    return tuple(nonsquare(x - root if (x - root) % p else root_derivative(root), p)
                 for root in ROOTS[:2])


def parity_row(row, bit):
    return sum(bit(value) << j for j, value in enumerate(row))


def check_matrix_distribution():
    masks = tuple(tuple(map(class_mask, row)) for row in TORSION_CLASSES)
    matrices = [tuple(parity_row(row, lambda value: (value & signs).bit_count() % 2)
                      for row in masks) for signs in range(256)]
    assert len(set(matrices)) == 256
    counts = Counter(binary_rank((*left, *right)) for left, right in product(matrices, repeat=2))
    assert counts == {0: 1, 1: 69, 2: 2298, 3: 23328, 4: 39840}
    assert (counts[3] + counts[4])*1024 == 987*256**2
    return dict(sorted(counts.items()))


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


def local_table(p, generators, classes):
    def plus(left, right):
        return add(left, right, p)

    axes = tuple((x % p, y % p) for x, y in generators)
    points = {None} | {(x, y) for x, y in product(range(p), repeat=2)
                       if (y*y - evaluate(CURVE, x)) % p == 0}
    doubles = {plus(point, point) for point in points}
    assert doubles == {point for point in points if kummer(point, p) == (0, 0)}
    rows = tuple(parity_row(row, lambda value: nonsquare(value, p)) for row in classes)
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
    if generators == TORSION_AXES:
        assert len(halves) == 7 and binary_rank(halves) == 3
    return rows, sums, halves


def sextic_rootless(p):
    for m in range(p):
        a, b = (m - 51)*(m - 95), (m - 57)*(m - 85)
        if (m + a*b*(a - 1)) % p == 0:
            return False
    return True


def half_gcd(p, q, s, word, generators=AXES):
    n = p*q
    axes = tuple((x % n, y % n) for x, y in generators)
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
    check_class_ranks()
    matrix_counts = check_matrix_distribution()
    total = sum(binary_rank(rows) == 3 for rows in product(range(8), repeat=4))
    assert total == 2520
    tables = {p: local_table(p, AXES, CLASSES) for p in good_primes(150)}
    extended_tables = {p: local_table(p, TORSION_AXES, TORSION_CLASSES) for p in tables}
    separated = extended_separated = upgraded = below_rank = 0
    for p, q in permutations(tables, 2):
        rows_p, _, halves = tables[p]
        rows_q, sums_q, _ = tables[q]
        basic_rank = binary_rank((*rows_p, *rows_q))
        if basic_rank == 3:
            separated += 1
            for s in halves:
                assert kummer(sums_q[s], q) != (0, 0)
        extended_rows_p, _, extended_halves = extended_tables[p]
        extended_rows_q, extended_sums_q, opposite_halves = extended_tables[q]
        extended_rank = binary_rank((*extended_rows_p, *extended_rows_q))
        assert extended_rank >= basic_rank
        if extended_rank >= 3:
            extended_separated += 1
            upgraded += basic_rank < 3
            impossible = sum(kummer(extended_sums_q[s], q) != (0, 0) for s in extended_halves)
            assert impossible >= 8 - (1 << (5 - extended_rank))
        else:
            below_rank += any(s not in opposite_halves for s in extended_halves)
    assert (separated, extended_separated, upgraded, below_rank) == (486, 746, 260, 2)
    print(f"Rank-three matrix stacks: {total}/4096 = 315/512.")
    print(f"Extended stacked rank counts: {matrix_counts}, success 987/1024.")
    print(f"Checked every target at {len(tables)} good primes.")
    print(f"Ordered prime pairs separated by stacked rank: {separated} original, {extended_separated} extended, {upgraded} upgraded.")
    print(f"Below the extended rank threshold, {below_rank} ordered pairs still have a one-sided half mask.")

    p, q = 149, 131
    assert sextic_rootless(p) and sextic_rootless(q)
    assert binary_rank((*tables[p][0], *tables[q][0])) == 3
    # Double R1 + 2R2 - R3 onto R3 mod p, and double 2R3 onto R1 mod q.
    for prime, s, word in ((p, 4, (0, 1, 1, 5)), (q, 1, (2, 2))):
        assert tables[prime][2][s] == word
        divisor = half_gcd(p, q, s, word)
        assert divisor == prime
        print(f"Rootless sextic at {p} and {q}: target {s}, word {word}, direct equality gcd {divisor}.")

    p, q = 131, 43
    assert sextic_rootless(p) and sextic_rootless(q)
    assert binary_rank((*tables[p][0], *tables[q][0])) == 1
    assert binary_rank((*extended_tables[p][0], *extended_tables[q][0])) == 3
    # Double -2R2 onto R1 + T1 + T2 at p only.
    s, word = 25, (6, 6)
    assert extended_tables[p][2][s] == word and s not in extended_tables[q][2]
    assert half_gcd(p, q, s, word, TORSION_AXES) == p
    print(f"Rootless sextic at {p} and {q}: torsion upgrades stacked rank 1 to 3 and gives gcd {p}.")

    p, q = 137, 113
    assert binary_rank((*extended_tables[p][0], *extended_tables[q][0])) == 2
    # Double -R1 onto R1 + T1 at p only.
    s, word = 9, (5,)
    assert extended_tables[p][2][s] == word and s not in extended_tables[q][2]
    assert half_gcd(p, q, s, word, TORSION_AXES) == p
    print(f"Stacked rank two at {p} and {q} still gives a direct equality gcd {p}.")


if __name__ == "__main__":
    replay()
