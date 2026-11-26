"""Pool verified element orders and replay against direct small 2-primary groups."""

from math import gcd
from random import Random


def pooled_split(n, certificates):
    def split(involution):
        divisor = gcd(involution-1, n)
        assert involution*involution % n == 1 and 1 < divisor < n and n % divisor == 0
        return divisor

    anchor, anchor_height = 1, 0
    for base, exponent in certificates:
        if exponent <= 0 or pow(base, exponent, n) != 1:
            raise ValueError("invalid order certificate")
        odd_part = exponent // (exponent & -exponent)
        projected = pow(base, odd_part, n)
        if projected == 1 or projected == anchor:
            continue
        height, top = 1, projected
        while top*top % n != 1:
            top = top*top % n
            height += 1
        if top != n-1:
            return split(top)
        if height > anchor_height:
            anchor, projected = projected, anchor
            anchor_height = height
        inverse_power = pow(anchor, -1, n)
        for bit in range(anchor_height):
            if projected == 1:
                break
            probe = pow(projected, 1 << (anchor_height-1-bit), n)
            if probe == n-1:
                projected = projected*inverse_power % n
            elif probe != 1:
                return split(probe)
            inverse_power = inverse_power*inverse_power % n
        assert projected == 1
    return None


def order(base, n):
    value, exponent = base, 1
    while value != 1:
        value = value*base % n
        exponent += 1
    return exponent


def prime_powers(n):
    factors = []
    for p in range(3, n+1, 2):
        exponent = 0
        while n % p == 0:
            exponent += 1
            n //= p
        if exponent:
            factors.append((p, exponent))
        if n == 1:
            break
    return factors


def replay():
    assert pooled_split(65, [(8, 12), (18, 20)]) in (5, 13)
    assert pooled_split(65, [(64, 2), (8, 4), (57, 8), (8, 4)]) is None
    assert pooled_split(65, [(16, 3), (1, 7)]) is None
    try:
        pooled_split(65, [(8, 2)])
    except ValueError:
        pass
    else:
        raise AssertionError("invalid certificate was accepted")
    rng = Random(3059)
    lists = signed_counts = 0
    for n in [*range(3, 160, 2), 175, 325]:
        units = [a for a in range(1, n) if gcd(a, n) == 1]
        group_size = len(units)
        odd_phi = group_size // (group_size & -group_size)
        projections = {a: pow(a, odd_phi, n) for a in units}
        orders = {a: order(a, n) for a in units}
        for length in (0, 1, 2, 3, 5, 8, 12):
            for _ in range(4):
                bases = rng.choices(units, k=length)
                certificates = [(a, orders[a]*rng.randrange(1, 16)) for a in bases]
                generated = {1}
                for a in bases:
                    g = projections[a]
                    generated = {x*pow(g, j, n) % n for x in generated for j in range(orders[g])}
                expected = any(z not in (1, n-1) and z*z % n == 1 for z in generated)
                assert (pooled_split(n, certificates) is not None) == expected
                lists += 1
        factors = prime_powers(n)
        if len(factors) < 2:
            continue
        heights = [((p-1) & -(p-1)).bit_length()-1 for p, _ in factors]
        height = min(heights)
        anchor = next(g for g in projections.values() if pow(g, 1 << (height-1), n) == n-1)
        cyclic = {pow(anchor, j, n) for j in range(1 << height)}
        admissible = [a for a in units if projections[a] in cyclic]
        assert len(admissible)*(1 << (sum(heights)-height)) == group_size
        negative = [a for a in admissible if sum(e for p, e in factors if pow(a, (p-1)//2, p) == p-1) % 2]
        assert len(negative) in (0, len(admissible)//2) and 4*len(negative) <= group_size
        if len(factors) == 2 and all(e == 1 for _, e in factors):
            assert 8*len(negative) <= group_size
            if heights[0] == heights[1]:
                assert not negative
        assert pooled_split(n, [(a, orders[a]*(2*j+1)) for j, a in enumerate(admissible)]) is None
        signed_counts += 1
    print(f"{lists} subgroup comparisons and {signed_counts} exact signed density checks")


if __name__ == "__main__":
    replay()
