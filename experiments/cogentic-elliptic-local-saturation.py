#!/usr/bin/env python3
"""Try a public odd multiplier and saturate the elliptic relation lattice at 2."""

import argparse
import sys
from itertools import combinations, product
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).parent
MODULAR = run_path(str(HERE / "cogentic-elliptic-cycle-split.py"))
AXES = (*MODULAR["AXES"], (-280, 1216))
GENERATORS = (*AXES, (-1496, 0), (-264, 0))
BAD_PRIMES, FactorFound, add, checked_gcd, negate = (
    MODULAR[name] for name in ("BAD_PRIMES", "FactorFound", "add", "checked_gcd", "negate")
)
primes_through = run_path(str(HERE / "cogentic-scalar-progression-sieve.py"))["primes_through"]


def smooth_exponent(modulus, bound):
    """Multiply the largest powers at most 4N of odd primes at most bound."""
    if modulus < 3 or modulus % 2 == 0 or bound < 1:
        raise ValueError("need an odd modulus at least 3 and a positive smoothness bound")
    limit = 4*modulus
    powers = []
    for prime in primes_through(min(bound, limit)):
        if prime == 2:
            continue
        power = prime
        while power * prime <= limit:
            power *= prime
        powers.append(power)
    while len(powers) > 1:
        if len(powers) % 2:
            powers.append(1)
        powers = [a*b for a, b in zip(powers[::2], powers[1::2], strict=True)]
    return powers[0] if powers else 1


def minimize_annihilator(annihilator, is_identity):
    """Strip prime factors from a verified global annihilator.

    The predicate tests global identity and can raise on a one-sided identity.
    If every test passes or fails at all primes together, the remaining
    exponent is the exact global order.
    """
    if annihilator < 1:
        raise ValueError("require a positive annihilator")
    factors = []
    remaining, candidate = annihilator, 2
    while candidate*candidate <= remaining:
        if remaining % candidate == 0:
            factors.append(candidate)
            while remaining % candidate == 0:
                remaining //= candidate
        candidate += 1
    if remaining > 1:
        factors.append(remaining)
    for prime in factors:
        while annihilator % prime == 0 and is_identity(annihilator // prime):
            annihilator //= prime
    return annihilator


def multiple(n, point, modulus):
    result = None
    for bit in bin(n)[2:]:
        result = add(result, result, modulus)
        if bit == "1":
            result = add(result, point, modulus)
    return result


def word(coefficients, points, modulus):
    result = None
    for coefficient, point in zip(coefficients, points, strict=True):
        result = add(result, multiple(coefficient, point, modulus), modulus)
    return result


def find_split(modulus, exponent, *, generators=GENERATORS):
    """Return (proper divisor or None, search stage) for an odd input and multiplier."""
    if modulus < 3 or modulus % 2 == 0 or exponent < 1 or exponent % 2 == 0:
        raise ValueError("need an odd modulus at least 3 and a positive odd exponent")

    stage = "bad reduction"
    try:
        for prime in BAD_PRIMES:
            if checked_gcd(prime, modulus) == modulus:
                return None, stage

        stage = "odd multiplier"
        points = [multiple(exponent, tuple(c % modulus for c in point), modulus) for point in generators]
        stage = "individual doubling"
        basis = []
        indices = range(len(points))
        limit = (4*modulus).bit_length()
        for i, point in enumerate(points):
            depth = 0
            while point is not None and depth < limit:
                point = add(point, point, modulus)
                depth += 1
            if point is not None:
                return None, "depth limit"
            basis.append(tuple((1 << depth) if i == j else 0 for j in indices))

        stage = "mixed saturation"
        subsets = tuple(cols for size in range(1, len(points) + 1) for cols in combinations(indices, size))
        while True:
            for columns in subsets:
                total = tuple(sum(basis[i][j] for i in columns) for j in indices)
                if any(c % 2 for c in total):
                    continue
                half = tuple(c // 2 for c in total)
                if word(half, points, modulus) is None:
                    # The replaced column has coefficient 1/2 in this relation.
                    basis[columns[0]] = half
                    break
            else:
                return None, "saturated"
    except FactorFound as found:
        divisor, = found.args
        assert 1 < divisor < modulus and modulus % divisor == 0
        return divisor, stage


def finite_relations(prime, exponent, generators=GENERATORS):
    cycles = []
    for x, y in generators:
        generator = multiple(exponent, (x % prime, y % prime), prime)
        cycle = [None]
        point = generator
        while point is not None:
            cycle.append(point)
            point = add(point, generator, prime)
        cycles.append(cycle)
    orders = tuple(map(len, cycles))
    assert all(order & (order - 1) == 0 for order in orders)

    last = {point: k for k, point in enumerate(cycles[-1])}
    relations = set()
    for terms in product(*(enumerate(cycle) for cycle in cycles[:-1])):
        point = None
        for _, term in terms:
            point = add(point, term, prime)
        need = negate(point, prime)
        if need in last:
            relations.add((*[i for i, _ in terms], last[need]))
    return orders, relations


def replay():
    assert minimize_annihilator(1, lambda _: False) == 1
    assert minimize_annihilator(3**4 * 5**2 * 11, lambda e: e % 45 == 0) == 45
    exponent = smooth_exponent(89*199, 5)
    assert exponent == 922640625
    assert finite_relations(89, exponent, AXES) == ((2, 2, 2), {(0, 0, 0), (1, 1, 0)})
    assert finite_relations(199, exponent, AXES) == ((2, 2, 2), {(0, 0, 0), (0, 1, 1)})
    assert find_split(89*199, exponent) == (89, "mixed saturation")
    assert finite_relations(23, 11)[0] == finite_relations(367, 11)[0] == (16, 8, 16, 2, 2)
    assert find_split(23*367, 11) == (23, "mixed saturation")

    modulus = 179*349
    exponent = smooth_exponent(modulus, 11)
    assert finite_relations(179, exponent, AXES) == finite_relations(349, exponent, AXES)
    assert find_split(modulus, exponent, generators=AXES) == (None, "saturated")
    relation = (0, 0, 1, 0, 1)
    assert relation in finite_relations(179, exponent)[1]
    assert relation not in finite_relations(349, exponent)[1]
    assert find_split(modulus, exponent) == (349, "mixed saturation")

    assert find_split(115, 1) == (5, "bad reduction")
    assert find_split(23, 1) == (None, "saturated")
    assert find_split(29, 1) == (None, "depth limit")

    primes = [p for p in primes_through(151) if p > 19]
    exponent = smooth_exponent(151**2, 43)
    local = {p: finite_relations(p, exponent) for p in primes}
    checked = forced = 0
    for p, q in combinations(primes, 2):
        divisor, stage = find_split(p*q, exponent)
        if local[p] != local[q]:
            assert divisor in (p, q)
            forced += 1
        assert divisor in (p, q) or (divisor is None and stage == "saturated")
        checked += 1
    print(f"Checked {checked} prime pairs and split all {forced} with different local relations.")
    print("N=17711 with B=5 split at mixed saturation despite identical individual doubling depths.")
    print("N=62471 with B=11 split at mixed saturation after adding the two rational torsion points.")


def main():
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?", help="odd integer to split, or omit to run the replay")
    options = parser.add_mutually_exclusive_group()
    options.add_argument("--exponent", type=int, help="public odd multiplier")
    options.add_argument("--bound", type=int, help="smoothness bound for the public multiplier")
    args = parser.parse_args()
    if args.N is None and args.exponent is None and args.bound is None:
        replay()
        return
    if args.N is None or (args.exponent is None and args.bound is None):
        parser.error("provide N and either --exponent or --bound")
    try:
        exponent = args.exponent if args.bound is None else smooth_exponent(args.N, args.bound)
        divisor, stage = find_split(args.N, exponent)
    except ValueError as error:
        parser.error(str(error))
    if divisor is None:
        print(f"No split found ({stage}).")
        raise SystemExit(1)
    print(f"{args.N} = {divisor} * {args.N // divisor} ({stage})")


if __name__ == "__main__":
    main()
