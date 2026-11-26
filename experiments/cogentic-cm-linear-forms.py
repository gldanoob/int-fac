#!/usr/bin/env python3
"""Search rational markings of quadratic twists of the fixed j=1728 curve."""

import argparse
from itertools import product
from math import gcd, lcm
from pathlib import Path
from runpy import run_path


MOVING = run_path(str(Path(__file__).with_name("cogentic-moving-elliptic-separation.py")))
FactorFound, checked_gcd, curve, separation_rank, smooth_exponent, split_curve, residual_multiple = (
    MOVING[name] for name in (
        "FactorFound", "checked_gcd", "curve", "separation_rank", "smooth_exponent",
        "split_curve", "residual_multiple",
    )
)


def find_split(modulus, smooth_bound, height, residual_bound=None):
    """Return a divisor and its public parameter or a bounded miss."""
    if modulus < 3 or modulus % 2 == 0 or min(smooth_bound, height) < 1:
        raise ValueError("require odd N >= 3 and positive search bounds")
    if residual_bound is not None and residual_bound < 1:
        raise ValueError("residual bound must be positive")
    exponent = smooth_exponent(modulus, smooth_bound)
    for v in range(1, height + 1):
        for u in range(-height, height + 1):
            if u in (0, v, -v) or gcd(u, v) != 1:
                continue
            stage = "parameter gcd"
            try:
                if max(checked_gcd(value, modulus) for value in (v, u, u-v, u+v)) == modulus:
                    continue
                roots, marked = curve((0, v, -v, u), 3)
                stage = "smooth multiplier"
                split_curve(roots, marked, exponent, modulus)
                if residual_bound is not None:
                    stage = "residual collision"
                    multiple = residual_multiple(roots, marked, exponent, modulus, residual_bound)
                    if multiple is not None and multiple > 1:
                        stage = "residual continuation"
                        odd_part = multiple // (multiple & -multiple)
                        split_curve(roots, marked, exponent*odd_part, modulus)
            except FactorFound as found:
                divisor = found.args[0]
                assert 1 < divisor < modulus and modulus % divisor == 0
                return divisor, (u, v), stage
    return None


def check_table():
    for z, w in product(range(4), repeat=2):
        counts = [0]*4
        for a, b, c in product(range(4), repeat=3):
            twist = a ^ b ^ c
            rows = ((z, twist, twist ^ a), (z ^ twist, w, twist ^ b))
            counts[twist] += separation_rank(rows) == 3
        expected = set(range(4))
        if z == 0:
            expected.remove(0)
        elif w == 0:
            expected -= {0, z}
        assert {twist for twist, count in enumerate(counts) if count} == expected
        assert all(counts[twist] == 12 for twist in expected)
        for bit in (0, 1):
            feasible = any((twist & 1) == bit for twist in expected)
            assert feasible == ((z, w, bit) != (2, 0, 0))


def check_heights():
    from sage.all import EllipticCurve, GF

    # Each prime class has representatives for every marking profile.
    primes = (257, 281, 251, 283, 269, 293, 263, 271)
    local = {}
    for prime in primes:
        field = GF(prime)
        profiles = {}
        for c in range(2, prime - 1):
            a, b, k = (int(not field(value).is_square()) for value in (c, c-1, c+1))
            twist = a ^ b ^ k
            vector = (twist ^ a, twist ^ b)
            if (twist, vector) in profiles:
                continue
            d = field(c*(c*c-1))
            elliptic = EllipticCurve(field, [-d*d, 0])
            point = elliptic(d*c, d*d)
            order = int(point.order())
            exponent = lcm(*(int(gen.order()) for gen in elliptic.gens()))
            profiles[twist, vector] = (order & -order, exponent & -exponent)
        assert len(profiles) == 8
        local[prime] = {}
        for twist in (0, 1):
            choices = {vector: profiles[twist, vector] for vector in product(range(2), repeat=2)}
            maximum = max(exponent for _, exponent in choices.values())
            assert all(exponent == maximum for _, exponent in choices.values())
            zero_height = choices[0, 0][0]
            highest = max(height for vector, (height, _) in choices.items() if vector != (0, 0))
            assert zero_height < highest == maximum
            local[prime][twist] = zero_height, highest

    comparisons = 0
    for p, q in product(primes, repeat=2):
        if p >= q:
            continue
        for p_twist, q_twist in product(range(2), repeat=2):
            p_zero, p_max = local[p][p_twist]
            q_zero, q_max = local[q][q_twist]
            if p_max >= q_max:
                assert p_max > q_zero
            else:
                assert q_max > p_zero
            comparisons += 1
    return comparisons


def replay():
    from sage.all import EllipticCurve, GF

    check_table()
    comparisons = check_heights()
    p, q, bound = 157, 43, 5
    assert find_split(p*q, bound, 7) == (p, (-7, 1), "smooth multiplier")
    exponent = smooth_exponent(p*q, bound)
    for prime in (p, q):
        field = GF(prime)
        size = int(EllipticCurve(field, [-1, 0]).cardinality())
        for order in (size, prime - 1, prime + 1):
            odd_part = order // (order & -order)
            assert exponent % odd_part != 0
    assert EllipticCurve(GF(p), [-(7*48)**2, 0]).cardinality() == 180
    assert find_split(1247, 3, 2) is None
    assert find_split(1247, 3, 2, 5) == (29, (-2, 1), "residual collision")
    print(f"Checked 1,024 sign patterns and {comparisons} prescribed twist pairs.")
    print("Split 6751 outside the untwisted and torus promises, and 1247 by residual search.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?", help="omit to run the replay")
    parser.add_argument("--smooth-bound", type=int, default=5)
    parser.add_argument("--height", type=int, default=7)
    parser.add_argument("--residual-bound", type=int)
    args = parser.parse_args()
    if args.N is None:
        replay()
        return
    try:
        result = find_split(args.N, args.smooth_bound, args.height, args.residual_bound)
    except ValueError as error:
        parser.error(str(error))
    if result is None:
        print("No split found within the public bounds.")
        raise SystemExit(1)
    divisor, (u, v), stage = result
    print(f"{args.N} = {divisor} * {args.N // divisor} (c={u}/{v}, {stage})")


if __name__ == "__main__":
    main()
