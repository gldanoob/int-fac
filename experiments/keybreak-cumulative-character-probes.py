#!/usr/bin/env python3
"""Finite replay of prime proposal slots, character multiplication and binary compression."""

from itertools import product
from math import isqrt


def prime(p):
    return p >= 2 and all(p % k for k in range(2, isqrt(p) + 1))


def legendre_bit(a, p):
    sign = pow(a % p, (p - 1) // 2, p)
    assert sign in (1, p - 1)
    return int(sign == p - 1)


def compressed(bits, masks):
    image = 0
    for bit, mask in zip(bits, masks, strict=True):
        if bit:
            image ^= mask
    return image


def main():
    x = 256
    slots = []
    for p in range(isqrt(x) + 1, x + 1):
        if prime(p):
            roots = [u for u in range(p) if pow(u, 3, p) == 2]
            slots.extend((p, u) for u in roots)
            assert len(roots) <= 3
    # The source's three slots per proposed integer give every root one preimage.
    assert len(slots) == len(set(slots))
    assert any(prime(p) and all(q != p for q, _ in slots) for p in range(17, x + 1))
    assert any(sum(q == p for q, _ in slots) == 3 for p, _ in slots)

    probes = [next(pair for pair in slots if pair[0] == p) for p in (17, 23, 29)]
    atoms = [(1, 1), (2, 1), (3, 2), (1, 0)]
    for atom, other in product(atoms, repeat=2):
        for p, u in probes:
            a = atom[0] - atom[1] * u
            b = other[0] - other[1] * u
            assert legendre_bit(a*b, p) == legendre_bit(a, p) ^ legendre_bit(b, p)

    for width in (2, 3):
        mask_range = range(2**width)
        maps = list(product(mask_range, repeat=len(probes)))
        for bits in product((0, 1), repeat=len(probes)):
            images = [compressed(bits, masks) for masks in maps]
            if any(bits):
                assert all(images.count(image) == len(maps) // len(mask_range)
                           for image in mask_range)
            else:
                assert set(images) == {0}
    print(f"{len(slots)} degree-one proposal slots; 48 sign products and 576 binary maps checked.")


if __name__ == "__main__":
    main()
