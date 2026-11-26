"""Check exact root brackets for the two planted-unit perturbations."""

from fractions import Fraction
from math import gcd
from pathlib import Path
import runpy

PLANTED = runpy.run_path(str(Path(__file__).with_name("cogentic-planted-norm-two.py")))
evaluate = PLANTED["evaluate"]
multiply = PLANTED["multiply"]


def derivative(poly):
    return [i*c for i, c in enumerate(poly) if i]


def verify_bump(n, h, pair, sign_separation):
    m, cuts, f, g = pair
    r = len(cuts)
    p = [1]
    for t in cuts:
        p = multiply(p, [-t, 1])

    denominator = (8*h)**h
    epsilon = Fraction(1, denominator)
    coefficient = 2*(64*h)**(4*h)+8*denominator
    sign_poly = derivative(p) if sign_separation else [1]
    bump = multiply(p, [-m, 1])
    perturbation = multiply(bump, [coefficient*c for c in sign_poly])

    bracket_count = 0
    selected = False
    for shift in range(3):
        polys = []
        for original in (f, g):
            poly = original.copy()
            for i, c in enumerate(perturbation):
                poly[i] += c
            for i, c in enumerate(bump):
                poly[i] += 4*shift*c
            assert poly[-1] == 1 and poly[0] == 2 and all(c % 2 == 0 for c in poly[:-1])
            assert evaluate(poly, m) == evaluate(original, m)
            polys.append(poly)

            signatures = set()
            for j, t in enumerate(cuts):
                direction = 1 if sign_separation or (r-1-j) % 2 == 0 else -1
                inside = t+direction*epsilon
                outside = t-direction*epsilon
                assert evaluate(poly, t) == 2
                assert evaluate(poly, inside) < 0 < evaluate(poly, outside)
                signature = sum(1 << k for k in range(r-1)
                                if cuts[k] < inside < cuts[k+1])
                if sign_separation:
                    assert signature == (1 << j if j < r-1 else 0)
                signatures.add(signature)
                bracket_count += 1
            expected_rank = r-1 if sign_separation else (r-1)//2
            assert len(signatures-{0}) == expected_rank

        divisors = [gcd(evaluate(derivative(poly), m), n) for poly in polys]
        selected |= all(d == 1 for d in divisors) or any(1 < d < n for d in divisors)

    assert selected
    return bracket_count


def main():
    cases = [(n, 4) for n in range(81, 231, 2)]
    cases.extend(((2**127-1, 8), (2**521-1, 12), ((1 << 1536)-17, 16)))
    pairs = brackets = 0
    largest = 0
    for n, h in cases:
        result = PLANTED["monic_plants"](n, h)
        if isinstance(result, int):
            assert 1 < result < n and n % result == 0
            continue
        brackets += sum(verify_bump(n, h, result, flag) for flag in (False, True))
        pairs += 1
        largest = max(largest, len(result[1]))
    assert pairs > 10 and largest >= 6
    n = 85
    m, cuts, _, _ = PLANTED["monic_plants"](n, 4)
    image = (m-cuts[1])*pow(m-cuts[0], -1, n) % n
    square_root = pow(image, 8, n)
    assert square_root == 16 and square_root**2 % n == 1
    assert gcd(n, square_root-1) == 5

    print(f"Verified {brackets:,} exact real brackets and signature rows on {pairs} pairs")
    print(f"Largest verified signature matrix had {largest} rows including -1")


if __name__ == "__main__":
    main()
