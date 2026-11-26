#!/usr/bin/env python3
"""Check weighted character identities for squarefree band counts modulo 15."""

from fractions import Fraction
from itertools import product
from math import gcd, isqrt

q = 15
units = [r for r in range(q) if gcd(r, q) == 1]
g = len(units)
log_base_two_mod_five = {pow(2, k, 5): k for k in range(4)}
fourth_roots = (1, 1j, -1, -1j)


def character(a, b, r):
    return (-1) ** (a * (r % 3 - 1)) * fourth_roots[b * log_base_two_mod_five[r % 5] % 4]


characters = list(product(range(2), range(4)))
nonprincipal = characters[1:]
jacobi = (1, 2)
band = [
    p for p in range(11, 101)
    if all(p % d for d in range(2, isqrt(p) + 1))
]


def accepted(n):
    for p in band:
        if n % p == 0:
            n //= p
    return n == 1


def transform(profile, a, b):
    return sum(profile[r] * character(a, b, r) for r in units)


T = 600
counts = {
    r: sum(accepted(n) for n in range(q + r, (T + 1) * q, q))
    for r in units
}
total = sum(counts.values())
assert total > 0
principal = Fraction(total, g)
twisted = {key: transform(counts, *key) for key in characters}
assert twisted[(0, 0)] == total
twisted_energy = sum(int(twisted[key].real) ** 2 + int(twisted[key].imag) ** 2
                     for key in nonprincipal)
assert sum((counts[r] - principal) ** 2 for r in units) == Fraction(twisted_energy, g)

for sign in (1, -1):
    coset = [r for r in units if character(*jacobi, r) == sign]
    assert len(coset) == g // 2
    indicator = {r: int(r in coset) for r in units}
    coset_transform = {key: transform(indicator, *key) for key in characters}
    assert {key for key, value in coset_transform.items() if value} == {(0, 0), jacobi}
    weighted = Fraction(sum(counts[r] for r in coset), len(coset))
    assert weighted - principal == Fraction(sign * int(twisted[jacobi].real), g)

assert character(*jacobi, 1) != character(*jacobi, 11)  # Same class modulo 5.
assert character(*jacobi, 1) != character(*jacobi, 7)   # Same class modulo 3.

base, increment, special = 97, 7, 2
flat = {r: base for r in units}
spike = {r: base - increment + g * increment * (r == special) for r in units}
assert sum(flat.values()) == sum(spike.values())
assert all(0 <= value <= T for value in spike.values())
for key in nonprincipal:
    assert transform(flat, *key) == 0
    assert transform(spike, *key) == g * increment * character(*key, special)

print(f"{total} band products across {g} residue classes. Coset and spike identities passed.")
