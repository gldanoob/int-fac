#!/usr/bin/env python3
"""Replay the consecutive-Jacobi separation on rational congruent-number twists."""

from math import prod
from pathlib import Path
from runpy import run_path

from sage.all import EllipticCurve, GF, jacobi_symbol, prime_range


modular = run_path(str(Path(__file__).with_name("cogentic-elliptic-cycle-split.py")))
FactorFound, checked_gcd, add = (modular[name] for name in ("FactorFound", "checked_gcd", "add"))


def multiply(point, exponent, d, modulus):
    result = None
    for bit in bin(exponent)[2:]:
        result = add(result, result, modulus, 0, -d*d)
        if bit == "1":
            result = add(result, point, modulus, 0, -d*d)
    return result


def odd_smooth_scalar(modulus, cutoff):
    powers = []
    for prime in map(int, prime_range(3, min(cutoff, 2*modulus) + 1)):
        power = prime
        while power*prime <= 2*modulus:
            power *= prime
        powers.append(power)
    return prod(powers)


def find_split(modulus, smooth_cutoff, search_limit=None):
    """Try the first distinguishing triple, returning a proper divisor on a hit."""
    if modulus < 3 or modulus % 2 == 0 or smooth_cutoff < 1:
        raise ValueError("require an odd modulus >= 3 and positive smooth cutoff")
    if search_limit is None:
        search_limit = modulus.bit_length()**4
    limit = min(search_limit, modulus - 1)
    try:
        for t in range(2, limit + 1):
            checked_gcd(t, modulus)
        for t in range(2, limit):
            if sum(jacobi_symbol(v, modulus) == -1 for v in (t-1, t, t+1)) != 2:
                continue
            d = t*(t*t - 1) % modulus
            point = (d*t % modulus, d*d % modulus)
            result = multiply(point, odd_smooth_scalar(modulus, smooth_cutoff), d, modulus)
            if result is not None:
                for torsion_x in (0, d, -d):
                    checked_gcd(result[0] - torsion_x, modulus)
            return None
    except FactorFound as found:
        return found.args[0]
    return None


def replay():
    label = {
        (0, 0, 0): 0, (1, 1, 1): 0,
        (0, 0, 1): 1, (0, 1, 1): 1,
        (0, 1, 0): 2, (1, 1, 0): 2,
        (1, 0, 0): 3, (1, 0, 1): 3,
    }
    for left, first in label.items():
        for right, second in label.items():
            if sum(a != b for a, b in zip(left, right, strict=True)) == 2:
                assert first != second

    checked = 0
    seen = set()
    for r in prime_range(11, 257):
        if r % 8 != 3:
            continue
        field = GF(r)
        for t in range(2, r - 1):
            d = field(t*(t*t - 1))
            curve = EllipticCurve(field, [-d*d, 0])
            point = curve(d*t, d*d)
            bits = tuple(not field(v).is_square() for v in (t, t-1, t+1))
            torsion = (curve(0), curve(d, 0), curve(0, 0), curve(-d, 0))
            assert ((r + 1)//4)*point == torsion[label[bits]]
            seen.add(bits)
            checked += 1
    assert seen == label.keys()

    assert odd_smooth_scalar(209, 3) == 243
    assert multiply((210*6 % 209, 210**2 % 209), 3, 210, 209) == (43, 33)
    assert find_split(209, 3, search_limit=7) == 11
    assert find_split(209, 1, search_limit=7) is None
    assert find_split(473, 7, search_limit=10) == 11
    print(f"{checked} torsion projections agreed with the table; public search split 209 and 473.")


if __name__ == "__main__":
    replay()
