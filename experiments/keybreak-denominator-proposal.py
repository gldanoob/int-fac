"""Check exact proposal weights and root multiplicities on small integer boxes."""
from collections import Counter
from fractions import Fraction
from math import gcd, isqrt


def check(modulus, width, scale):
    assert scale.bit_count() == 1 and width < modulus
    low, high = (width + 7) // 8, width // 4
    k_min = (low * low - 4 * scale**2 * width) // modulus
    k_max = high * high // modulus
    levels = scale.bit_length()
    numerator_weights = Counter()
    for level in range(levels):
        edge = 2**level
        for d in range(edge, 2 * edge):
            if any(d % (p*p) == 0 for p in range(2, isqrt(d) + 1)):
                continue
            for e in range(1, 2 * scale // edge + 1):
                t = d * e
                if scale <= t < 2 * scale and t % 2 and gcd(t, modulus) == 1:
                    numerator_weights[t] += 1
    mass = Counter()
    for t, choices in numerator_weights.items():
        square = t*t
        for k in range(k_min, k_max + 1):
            if gcd(k * modulus, t) != 1 or k * modulus + square * width < 0:
                continue
            roots = [r for r in range(square) if (r*r - k*modulus) % square == 0]
            if roots:
                assert len(roots) == choices
            start = max(low, isqrt(k * modulus) + 1 if k >= 0 else 0)
            end = min(high, isqrt(k * modulus + square * width))
            for r in roots:
                first = start + (r - start) % square
                candidates = range(first, end + 1, square)
                assert len(candidates) <= 8
                for h in candidates:
                    if gcd(h, modulus) == 1:
                        mass[t, h] += Fraction(choices, len(roots))
    ideal = Counter(
        (t, h) for t in range(scale, 2*scale)
        if t % 2 and gcd(t, modulus) == 1
        for h in range(low, high + 1)
        if gcd(h, t * modulus) == 1 and
        1 <= (h * pow(t, -1, modulus))**2 % modulus <= width
    )
    assert mass == ideal, (modulus,width,scale,mass-ideal,ideal-mass)
    return len(ideal)


if __name__ == "__main__":
    cases = [(n, x, t) for n, x in ((385, 184), (625, 345), (1001, 646), (4093, 1870))
             for t in (2, 4, 8)]
    print(f"{len(cases)} boxes, {sum(check(*case) for case in cases)} equal-mass representatives")
