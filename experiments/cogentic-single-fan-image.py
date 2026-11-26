"""Compute the complete sign image of one integer's quadratic polynomial fan."""

import argparse
from fractions import Fraction
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path
from secrets import randbits


MATCH = run_path(str(Path(__file__).with_name("cogentic-rational-root-matching.py")))
SQUARES, GRID = MATCH["SQUARES"], MATCH["GRID"]


def sign_image(n, roots):
    """Partition the odd prime powers by their signs, then find rank modulo global sign."""
    if n < 3 or n % 2 == 0:
        raise ValueError("expected an odd modulus greater than one")
    roots = tuple(roots)
    blocks = [n]
    for root in roots:
        if root*root % n != 1:
            raise ValueError("expected a square root of unity")
        refined = []
        for block in blocks:
            piece = gcd(root-1, block)
            if piece > 1:
                refined.append(piece)
            if piece < block:
                refined.append(block//piece)
        blocks = refined
    words = []
    for root in roots:
        reference = root % blocks[0] == 1
        words.append(sum(1 << j for j, block in enumerate(blocks[1:])
                         if (root % block == 1) != reference))
    nullity = len(GRID["eliminate"](words, (1 << j for j in range(len(words)))))
    return sorted(blocks), len(words)-nullity


def prepare(n, height=13, denominators=3, shifts=3, bound=13):
    if n < 3 or n % 2 == 0 or min(height, denominators, shifts, bound) < 1:
        raise ValueError("expected an odd N >= 3 and positive search parameters")
    m = isqrt(n)
    linear, remainder = divmod(n-m*m, m)
    primes = tuple(GRID["primes_through"](bound))
    fields, generators = [], []
    mark_count = 0
    for shift in range(1, shifts+1):
        trace_coefficient = linear + shift
        constant = remainder - shift*m
        d = trace_coefficient**2 - 4*constant
        if gcd(2*d, n) != 1 or (d >= 0 and isqrt(d)**2 == d):
            continue
        elements, labels = [], []
        for b in range(1, denominators+1):
            for a in range(-height, height+1):
                r = a-b*m
                norm = a*a + trace_coefficient*a*b + constant*b*b
                if gcd(a, b) != 1 or gcd(r*norm, n) != 1:
                    continue
                if any(GRID["factor_bounded"](v, primes, bound) is None for v in (r, norm)):
                    continue
                elements.append((a+Fraction(trace_coefficient*b, 2), Fraction(-b, 2)))
                labels.append(r)
        mark_count += len(labels)
        for mask in SQUARES["square_masks"](d, elements):
            value = prod(labels[j] for j in GRID["support"](mask))
            generators.append((len(fields), mask, value))
        fields.append((d, 2*m+trace_coefficient, elements, labels))
    words = SQUARES["rational_words"](value for _, _, value in generators)
    basis = GRID["eliminate"](words, (1 << j for j in range(len(words))))
    return mark_count, fields, generators, basis


def lift(n, fields, generators, mask):
    field_masks = [0]*len(fields)
    for column in GRID["support"](mask):
        field_index, local, _ = generators[column]
        field_masks[field_index] ^= local
    rational, residue = 1, 1
    for indices, (d, radical, elements, labels) in zip(field_masks, fields, strict=True):
        if not indices:
            continue
        value = SQUARES["masked_product"](d, elements, indices)
        x, y = SQUARES["square_root"](d, value)
        assert SQUARES["multiply"](d, (x, y), (x, y)) == value
        root = x + radical*y
        residue = residue*root.numerator*pow(root.denominator, -1, n) % n
        rational *= prod(labels[j] for j in GRID["support"](indices))
    scale = isqrt(rational)
    assert scale*scale == rational
    unit = residue*pow(scale, -1, n) % n
    assert unit*unit % n == 1
    return unit


def analyze(n, height=13, denominators=3, shifts=3, bound=13):
    count, fields, generators, basis = prepare(n, height, denominators, shifts, bound)
    blocks, rank = sign_image(n, (lift(n, fields, generators, mask) for mask in basis))
    return count, len(basis), rank, blocks


def sample(n, height, denominators, shifts, bound, draws):
    if draws < 1:
        raise ValueError("supply a positive number of draws")
    count, fields, generators, basis = prepare(n, height, denominators, shifts, bound)
    masks = (GRID["combine"](randbits(len(basis)), basis) for _ in range(draws))
    blocks, rank = sign_image(n, (lift(n, fields, generators, mask) for mask in masks))
    return dict(marks=count, dimension=len(basis), draws=draws, observed_rank=rank, blocks=blocks)


def self_check():
    # Two independent directions, one duplicate and a global sign, with repeated primes.
    n = 9*25*49*11
    roots = [next(r for r in range(1, n, a) if r % (n//a) == n//a-1)
             for a in (9*25, 9*49)]
    assert sign_image(n, [*roots, roots[0], n-1]) == ([9, 11, 25, 49], 2)
    assert sign_image(45, []) == ([45], 0)
    for n, expected in [(119, (16, 4, 0, [119])), (341, (23, 6, 1, [11, 31]))]:
        result = analyze(n)
        assert result == expected, (n, result)
        _, fields, generators, basis = prepare(n)
        roots = [lift(n, fields, generators, GRID["combine"](bits, basis)) for bits in range(1 << len(basis))]
        assert sum(z not in (1, n-1) for z in roots) == (0 if n == 119 else 32)
        print(n, result)
    assert analyze(119, 23, 5, 5, 23) == (57, 28, 1, [7, 17])
    assert analyze(341, 23, 5, 5, 23) == (91, 48, 1, [11, 31])
    assert analyze(4199, 33, 7, 7, 43) == (62, 17, 2, [13, 17, 19])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?")
    parser.add_argument("--height", type=int, default=13)
    parser.add_argument("--denominators", type=int, default=3)
    parser.add_argument("--shifts", type=int, default=3)
    parser.add_argument("--bound", type=int, default=13)
    parser.add_argument("--samples", type=int, help="lift this many independent uniform dependencies")
    args = parser.parse_args()
    if args.N is None:
        self_check()
    elif args.samples is not None:
        print(sample(args.N, args.height, args.denominators, args.shifts, args.bound, args.samples))
    else:
        print(analyze(args.N, args.height, args.denominators, args.shifts, args.bound))
