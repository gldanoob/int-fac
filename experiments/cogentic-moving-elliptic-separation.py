#!/usr/bin/env python3
"""Check and search moving elliptic curves from imaginary quadratic norms."""

import argparse
import sys
from fractions import Fraction
from functools import cache
from itertools import combinations, permutations, product
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).parent
TORUS = run_path(str(HERE / "cogentic-varying-norm-torus.py"))
norm_generator, primes_through, smooth_exponent, weighted_class_number = (
    TORUS[name] for name in ("norm_generator", "primes_through", "smooth_exponent", "weighted_class_number")
)
FactorFound, add, checked_gcd = (TORUS["saturation"][name] for name in ("FactorFound", "add", "checked_gcd"))
binary_rank = run_path(str(HERE / "cogentic-sparse-kernel.py"))["binary_rank"]
INDICES = range(4)
PAIRS = tuple(combinations(INDICES, 2))
GOOD_LABELS = (
    {(1, 2), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2)},
    {(1, 2), (1, 3), (2, 0), (2, 3), (3, 0), (3, 2)},
    {(1, 0), (1, 3), (2, 1), (2, 3), (3, 0), (3, 1)},
    {(1, 0), (1, 2), (2, 0), (2, 1), (3, 1), (3, 2)},
)


def curve(positions, omitted):
    marked = positions[omitted]
    remaining = tuple(x for i, x in enumerate(positions) if i != omitted)
    d = prod(marked - x for x in remaining)
    return tuple(d*x for x in remaining), (d*marked, d*d)


def label_rows(labels, z, omitted):
    def difference(i, j):
        return labels[j, i] ^ z if j < i else labels[i, j]

    i, j, k = (r for r in INDICES if r != omitted)
    di, dj, dk = (difference(r, omitted) for r in (i, j, k))
    d = di ^ dj ^ dk
    return ((difference(j, i) ^ difference(k, i), d ^ difference(i, j), d ^ di),
            (d ^ difference(j, i), difference(i, j) ^ difference(k, j), d ^ dj))


def separation_rank(rows):
    return binary_rank(sum(((label >> prime) & 1) << j for j, label in enumerate(row))
                       for prime in (0, 1) for row in rows)


def separating(labels, z):
    return any(separation_rank(label_rows(labels, z, m)) == 3 for m in INDICES)


def check_boolean():
    for z in INDICES:
        robust = set()
        for a, h in product(INDICES, repeat=2):
            cases = (dict(zip(PAIRS, (0, a, c0, h, c1, c2), strict=True))
                     for c0, c1, c2 in product(INDICES, repeat=3))
            if all(separating(labels, z) for labels in cases):
                robust.add((a, h))
            if (a, h) in GOOD_LABELS[z]:
                for two, b_plus_one in product(INDICES, repeat=2):
                    labels = dict(zip(PAIRS, (0, a, z, h, z ^ two, z ^ b_plus_one), strict=True))
                    assert separating(labels, z)
        assert robust == GOOD_LABELS[z]


def menu(primes):
    for s in primes:
        if s % 4 != 3:
            continue
        h = int(weighted_class_number(-s) * (6 if s == 3 else 2))
        assert h % 2 == 1
        for ell in primes:
            if ell in (2, s):
                continue
            generator = norm_generator(s, ell, h)
            if generator is None:
                continue
            a, v = generator
            u = 2*a + v
            assert u and v and u*u + s*v*v == 4*ell**h
            yield s, ell, (0, u*u, 4*ell**h, -u*u)


def pair_label(value, p, q):
    value = Fraction(value)
    bits = 0
    for i, prime in enumerate((p, q)):
        residue = value.numerator * pow(value.denominator, -1, prime) % prime
        assert residue
        bits |= (pow(residue, (prime - 1)//2, prime) == prime - 1) << i
    return bits


def check_rational(positions, p, q, labels):
    scale = positions[1]
    assert scale > 0 and gcd(scale, p*q) == 1
    rational = tuple(Fraction(x, scale) for x in positions)
    assert rational[0] == 0 and rational[3] == -1 and rational[2] > 1
    z = pair_label(-1, p, q)
    for omitted in INDICES:
        roots, marked = curve(rational, omitted)
        scaled_roots, scaled_marked = curve(positions, omitted)
        assert scaled_roots == tuple(scale**4*x for x in roots)
        assert scaled_marked == (scale**4*marked[0], scale**6*marked[1])
        assert marked[1] > 0 and marked[1]**2 == prod(marked[0] - root for root in roots)
        rows = tuple(tuple(pair_label(x - root if x != root else
                                     prod(root - other for other in roots if other != root), p, q)
                           for x in (roots[0], roots[1], marked[0])) for root in roots[:2])
        assert rows == label_rows(labels, z, omitted)


def multiply(exponent, marked, modulus, a2, a4):
    point = None
    for bit in bin(exponent)[2:]:
        point = add(point, point, modulus, a2, a4)
        if bit == "1":
            point = add(point, marked, modulus, a2, a4)
    return point


def coefficients(roots, modulus):
    return -sum(roots) % modulus, sum(a*b for a, b in combinations(roots, 2)) % modulus


def split_curve(roots, marked, exponent, modulus):
    a2, a4 = coefficients(roots, modulus)
    marked = tuple(c % modulus for c in marked)
    point = multiply(exponent, marked, modulus, a2, a4)
    for _ in range((4*modulus).bit_length()):
        if point is None:
            return
        doubled = add(point, point, modulus, a2, a4)
        if doubled is None:
            # The final nonzero double can land at different rational torsion roots.
            for root in roots:
                checked_gcd(point[0] - root, modulus)
            return
        point = doubled


@cache
def batch_tools():
    try:
        batch = run_path(str(HERE / "cogentic-elliptic-batch-search.py"))
    except ModuleNotFoundError as error:
        if error.name == "sage":
            raise ValueError("residual-order search requires SageMath Python") from error
        raise
    return tuple(batch[name] for name in ("PolynomialRing", "Zmod", "value_tree", "evaluate_many"))


def signed_multiple(first, second, i, j, modulus):
    assert first[0] == second[0] and i != j
    if first[1] == second[1]:
        return abs(i - j)
    checked_gcd(first[1] - second[1], modulus)
    assert (first[1] + second[1]) % modulus == 0
    return i + j


def bounded_multiple(point, modulus, a2, a4, bound):
    """Return a positive global multiple, raise a proper gcd, or report a miss."""
    if point is None:
        return 1
    width = isqrt(bound - 1) + 1
    # A local order r <= bound has r = j*width-i with 0 <= i < width.
    babies = {}
    baby = None
    for i in range(1, width):
        baby = add(baby, point, modulus, a2, a4)
        if baby is None:
            return i
        if baby[0] in babies:
            j, previous = babies[baby[0]]
            return signed_multiple(baby, previous, i, j, modulus)
        babies[baby[0]] = i, baby

    step = add(baby, point, modulus, a2, a4)
    if step is None:
        return width
    if not babies:
        return None
    giants = []
    giant = None
    for j in range(1, width + 1):
        giant = add(giant, step, modulus, a2, a4)
        if giant is None:
            return j*width
        giants.append(giant)

    polynomial_ring, residue_ring, value_tree, evaluate_many = batch_tools()
    ring = polynomial_ring(residue_ring(modulus), "x")
    baby_tree = value_tree(ring, babies)
    giant_tree = value_tree(ring, [giant[0] for giant in giants])
    values = evaluate_many(baby_tree[-1][0], giant_tree)
    for j, (giant, value) in enumerate(zip(giants, values, strict=True), 1):
        if checked_gcd(int(value), modulus) == 1:
            continue
        node = 0
        for row in reversed(baby_tree[:-1]):
            node *= 2
            if checked_gcd(int(row[node](giant[0])), modulus) == 1:
                node += 1
        assert baby_tree[0][node](giant[0]) == 0
        i, baby = babies[giant[0]]
        return signed_multiple(giant, baby, j*width, i, modulus)
    return None


def residual_multiple(roots, marked, exponent, modulus, bound):
    a2, a4 = coefficients(roots, modulus)
    point = multiply(exponent, tuple(c % modulus for c in marked), modulus, a2, a4)
    for _ in range((4*modulus).bit_length()):
        if point is None:
            return 1
        point = add(point, point, modulus, a2, a4)
    return bounded_multiple(point, modulus, a2, a4, bound)


def find_split(modulus, exponent, menu_bound, residual_order=None):
    """Search the public moving curves and return a divisor and its source."""
    if modulus < 3 or modulus % 2 == 0 or exponent < 1 or exponent % 2 == 0 or menu_bound < 3:
        raise ValueError("need odd N >= 3, a positive odd exponent and a menu bound >= 3")
    if residual_order is not None and residual_order < 1:
        raise ValueError("residual order bound must be positive")
    root = isqrt(modulus)
    if root*root == modulus:
        return root, "square input"
    primes = primes_through(menu_bound)
    stage = "trial division"
    try:
        for prime in primes:
            if checked_gcd(prime, modulus) == modulus:
                return None, "menu limit"
        for _, _, positions in menu(primes):
            stage = "root difference"
            positions = tuple(x % modulus for x in positions)
            if max(checked_gcd(positions[j] - positions[i], modulus) for i, j in PAIRS) == modulus:
                continue
            for omitted in INDICES:
                roots, marked = curve(positions, omitted)
                stage = "elliptic group"
                split_curve(roots, marked, exponent, modulus)
                if residual_order is not None:
                    stage = "residual-order collision"
                    relation = residual_multiple(roots, marked, exponent, modulus, residual_order)
                    if relation is not None and relation > 1:
                        stage = "residual-order continuation"
                        odd_part = relation // (relation & -relation)
                        split_curve(roots, marked, exponent*odd_part, modulus)
    except FactorFound as found:
        divisor, = found.args
        assert 1 < divisor < modulus and modulus % divisor == 0
        return divisor, stage
    return None, "menu limit"


def check_small_pairs():
    choices = tuple(menu(primes_through(127)))
    checked = gcd_cases = 0
    for p, q in permutations(primes_through(73)[1:], 2):
        checked += 1
        modulus = p*q
        if min(p, q) == 3:
            assert find_split(modulus, 1, 3) == (3, "trial division")
            gcd_cases += 1
            continue
        z = pair_label(-1, p, q)
        for s, ell, positions in choices:
            if gcd(s*ell, modulus) != 1:
                continue
            a, h = pair_label(ell, p, q), pair_label(s, p, q)
            # Use two independent labels for z=0 and a trivial s label otherwise.
            if a in (0, h, z) or bool(h) == bool(z):
                continue
            assert (a, h) in GOOD_LABELS[z]
            common = max(gcd(positions[j] - positions[i], modulus) for i, j in PAIRS)
            if common > 1:
                assert common in (p, q)
                gcd_cases += 1
                break
            labels = {(i, j): pair_label(Fraction(positions[j] - positions[i], positions[1]), p, q)
                      for i, j in PAIRS}
            assert (labels[0, 2], labels[1, 2]) == (a, h) and separating(labels, z)
            check_rational(positions, p, q, labels)
            break
        else:
            raise AssertionError((p, q, "no separating chart"))
    return checked, gcd_cases


def check_group_split():
    positions = (0, 49, 52, -49)
    assert (3, 13, positions) in menu(primes_through(13))
    roots, marked = curve(positions, 0)
    modulus, exponent = 37*41, 55
    labels = {(i, j): pair_label(positions[j] - positions[i], 37, 41) for i, j in PAIRS}
    assert separation_rank(label_rows(labels, 0, 0)) == 3
    for prime, root_index in ((37, 1), (41, 2)):
        a2, a4 = coefficients(roots, prime)
        local = tuple(c % prime for c in marked)
        point = None
        for _ in range(exponent):
            point = add(point, local, prime, a2, a4)
        assert point == (roots[root_index] % prime, 0)
    a2, a4 = coefficients(roots, modulus)
    point = multiply(exponent, tuple(c % modulus for c in marked), modulus, a2, a4)
    assert point is not None and point[1] == 0 and add(point, point, modulus, a2, a4) is None
    try:
        split_curve(roots, marked, exponent, modulus)
    except FactorFound as found:
        assert found.args == (37,)
    else:
        raise AssertionError("different final torsion roots should expose 37")
    assert find_split(modulus, exponent, 31) == (41, "elliptic group")
    assert find_split(modulus, smooth_exponent(modulus, 3), 31) == (41, "elliptic group")
    assert find_split(101, 1, 31) == (None, "menu limit")
    assert find_split(53**2, 1, 31) == (53, "square input")


def replay():
    check_boolean()
    checked, gcd_cases = check_small_pairs()
    check_group_split()
    print(f"Verified Boolean coverage and {checked} ordered prime pairs through 73, including {gcd_cases} direct gcd cases.")
    print("N=1517 splits in the elliptic group. With E=55 the selected chart has different final torsion roots.")


def replay_stage_two():
    assert find_split(2983, 1, 7) == (None, "menu limit")
    assert find_split(2983, 1, 7, 5) == (19, "residual-order collision")

    modulus = 269*283
    roots, marked = curve((0, 25, 28, -25), 0)
    a2, a4 = coefficients(roots, modulus)
    start = tuple(c % modulus for c in marked)
    point = multiply(3 << (4*modulus).bit_length(), start, modulus, a2, a4)
    assert point == (67725, 23665)
    assert multiply(11, point, modulus, a2, a4) is None
    left = multiply(8, point, modulus, a2, a4)
    right = multiply(3, point, modulus, a2, a4)
    assert left[0] == right[0] and (left[1] + right[1]) % modulus == 0
    assert residual_multiple(roots, marked, 3, modulus, 1) is None
    assert residual_multiple(roots, marked, 3, modulus, 11) == 11
    assert find_split(modulus, 3, 7) == (None, "menu limit")
    assert find_split(modulus, 3, 7, 11) == (269, "residual-order continuation")
    print("Stage two splits 2983 by a batched collision and 76127 after a shared residual relation of 11.")


def main():
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?", help="odd integer to split, or omit to run the replay")
    options = parser.add_mutually_exclusive_group()
    options.add_argument("--exponent", type=int, help="public odd multiplier")
    options.add_argument("--bound", type=int, default=11, help="odd smoothness cutoff, defaults to 11")
    parser.add_argument("--menu", type=int, default=31, help="maximum discriminant prime and split prime")
    parser.add_argument("--residual-order", type=int, help="stage-two residual odd order bound (requires SageMath)")
    parser.add_argument("--replay-stage-two", action="store_true", help="run the stage-two regression fixtures")
    args = parser.parse_args()
    if args.replay_stage_two:
        if args.N is not None:
            parser.error("--replay-stage-two runs without N")
        replay_stage_two()
        return
    if args.N is None:
        replay()
        return
    try:
        exponent = args.exponent if args.exponent is not None else smooth_exponent(args.N, args.bound)
        divisor, stage = find_split(args.N, exponent, args.menu, args.residual_order)
    except ValueError as error:
        parser.error(str(error))
    if divisor is None:
        print("No split in the specified menu.")
        raise SystemExit(1)
    print(f"{args.N} = {divisor} * {args.N // divisor} ({stage})")


if __name__ == "__main__":
    main()
