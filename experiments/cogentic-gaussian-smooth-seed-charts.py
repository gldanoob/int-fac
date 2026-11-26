"""Split a recognized Pell family using fixed smooth seeds on Gaussian charts."""

import argparse
import json
from fractions import Fraction
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).resolve().parent
CHARTS = run_path(str(HERE / "cogentic-compatible-quadratic-charts.py"))
MATCHING, SQUARES = CHARTS["MATCHING"], CHARTS["SQUARES"]
CRT_RANK = run_path(str(HERE / "cogentic-mixed-lifted-rank.py"))["crt_rank"]


def split(n):
    """Recognize the unit family and recover two exact modular square certificates."""
    if n < 40001:
        return None
    r = isqrt(n-1)
    s = isqrt(r//2)
    t = isqrt(15*s*s-56)
    if r*r+1 != n or 2*s*s != r or s < 10 or t*t != 15*s*s-56 or gcd(t, n) != 1:
        return None

    charts = [
        ((1, 0, 1), r, (1, 1), (1, 0, 0, 1)),
        ((2, -2, 1), r+1, (-30, 97), (0, -2, 1, -1)),
        ((5, -4, 1), 2-r, (1, 1), (3, -1, 1, -1)),
    ]
    elements, labels = [], []
    for (v, u, _), m, (a, b), (p, q, h, k) in charts:
        discriminant, derivative = u*u-4*v, 2*m+u
        assert m*m+u*m+v == n and gcd(derivative, n) == 1 and gcd(a, b) == 1
        scale, factor = CHARTS["align"](n, (-4, 2*r), (discriminant, derivative))
        assert factor is None and scale is not None
        generator = Fraction(-u, 2), scale/2
        assert SQUARES["multiply"](-4, generator, (k, Fraction(h, 2))) == (q, Fraction(p, 2))
        assert gcd(p*k-q*h, n) == gcd(h*r+k, n) == 1
        argument = Fraction(p*r+q, h*r+k)
        element = CHARTS["coordinates"](u, scale, a, b)
        label = a-b*argument
        assert CHARTS["reduce_fraction"](label, n) == (a-b*m) % n
        assert CHARTS["reduce_fraction"](element[0]+2*r*element[1], n) == (a-b*m) % n
        elements.append(element)
        labels.append(label)
    assert [SQUARES["norm"](-4, element) for element in elements] == [2, 2*113**2, 2]
    assert not any(SQUARES["square_kernel"](-4, [element]) for element in elements)
    assert [mask for mask, _ in SQUARES["square_kernel"](-4, elements)] == [3, 5]

    witnesses = []
    for element, label, coefficient, scale in zip(elements[1:], labels[1:], (15, 1), (2*t, 2*s), strict=True):
        root = Fraction(1), Fraction(coefficient, 2)
        assert SQUARES["multiply"](-4, root, root) == SQUARES["multiply"](-4, elements[0], element)
        value, residue = labels[0]*label, (1+coefficient*r) % n
        assert value == scale**2 and residue*residue % n == scale**2 % n
        witnesses.append((value, residue))
    matches = MATCHING["matched_basis"](n, witnesses)
    assert [mask for mask, _ in matches] == [1, 2]
    ratios = [ratio for _, ratio in matches]
    rank = CRT_RANK(n, ratios)
    assert rank == 2
    blocks = [n]
    for ratio in ratios:
        refined = []
        for block in blocks:
            d = gcd(ratio-1, block)
            refined.extend(factor for factor in (d, block//d) if factor > 1)
        blocks = refined
    assert len(blocks) >= 3 and prod(blocks) == n
    return dict(n=n, r=r, t=t, s=s, smooth_norms=[2, 2*113**2, 2], crt_rank=rank,
                labels=[(label.numerator, label.denominator) for label in labels],
                ratios=ratios, coprime_factors=sorted(blocks))


def replay():
    t, s = 38, 10
    seen = []
    for k in range(17):
        if k in (0, 1, 2, 16):
            result = split(4*s**4+1)
            assert result is not None and result["crt_rank"] == 2
            seen.append(result["n"])
            if k == 0:
                assert result["ratios"] == [18461, 38011]
                assert result["coprime_factors"] == [13, 17, 181]
                r = result["r"]
                affine = (1-r, -127-97*r, r-1)
                assert all(SQUARES["rational_sqrt"](affine[i]*affine[j]) is None
                           for i, j in ((0, 1), (0, 2), (1, 2)))
                print(json.dumps(result))
            if k == 16:
                assert (t % 113, s % 113) == (38, 10)
        t, s = 4*t+15*s, t+4*s
    assert gcd(*seen) == 1 and not split(40003)
    print("Verified four constructed family cases, including the Pell return modulo 113")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", nargs="?", type=int, help="recognize and split a member of the Pell family")
    args = parser.parse_args()
    if args.n is None:
        replay()
    elif args.n < 2:
        parser.error("require N >= 2")
    else:
        print(json.dumps(split(args.n) or dict(n=args.n, status="not-in-family")))
