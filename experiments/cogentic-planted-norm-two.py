"""Build a monic pair with a growing row of prescribed norm-two marks."""

from itertools import combinations_with_replacement
from math import comb, gcd, prod
from pathlib import Path
import runpy

HERE = Path(__file__).parent
BASE = runpy.run_path(str(HERE / "cogentic-monic-pair.py"))


def evaluate(coeffs, x):
    value = 0
    for c in reversed(coeffs):
        value = value * x + c
    return value


def multiply(f, g):
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i+j] += a * b
    return out


def norm_two_quotient(poly, t):
    # Synthetic division of P(X)-2 by X-t.
    q = [poly[-1]]
    for c in reversed(poly[1:-1]):
        q.append(c + t*q[-1])
    assert poly[0] + t*q[-1] == 2
    return q[::-1]


def monic_plants(n, h):
    if n < 9 or n % 2 == 0 or h < 2:
        raise ValueError("need odd N >= 9 and h >= 2")
    m = BASE["integer_root"](n, h)
    m -= 1 - m % 2
    cuts = tuple(range(0, 2 * (h//2), 2))
    if m < 3 or m <= cuts[-1]:
        raise ValueError("the base must exceed every planted cut")
    p = [1]
    for t in cuts:
        common = gcd(m-t, n)
        if common > 1:
            return common
        p = multiply(p, [-t, 1])
    target = -2 * pow(evaluate(p, m), -1, n) % n
    if target % 2 == 0:
        target += n
    quotient = (target - m**h)//2
    q = []
    for _ in range(h-1):
        quotient, digit = divmod(quotient, m)
        q.append(2*digit)
    q.extend((2*quotient, 1))
    f = multiply(p, q)
    f[0] += 2
    bump = multiply(p, [-m, 1])
    for s in range(3):
        left = f.copy()
        for i, c in enumerate(bump):
            left[i] += 4*s*c
        right = left + [0]
        for i, c in enumerate(bump):
            right[h+i] += c
        for poly in (left, right):
            derivative = evaluate([i*c for i, c in enumerate(poly) if i], m)
            common = gcd(derivative, n)
            if 1 < common < n:
                return common
            if common == n:
                break
        else:
            return m, cuts, left, right
    raise AssertionError("three derivative shifts exhausted")


def run():
    inputs = [(n, BASE["scheduled_degree"](n)) for n in range(9, 2001, 2)]
    for bits in (1024, 4096, 14000):
        n = (1 << bits) - 17
        inputs.append((n, BASE["scheduled_degree"](n)))
    inputs.extend(((2**107-1, 6), (2**127-1, 8)))
    factors = pairs = products = 0
    largest = 0
    for n, h in inputs:
        result = monic_plants(n, h)
        if isinstance(result, int):
            assert 1 < result < n and n % result == 0
            factors += 1
            continue
        m, cuts, left, right = result
        largest = max(largest, len(cuts))
        assert len(left) == len(cuts)+h+1 and len(right) == len(left)+1
        assert evaluate(left, m) == evaluate(right, m) and evaluate(left, m) % n == 0
        for poly in (left, right):
            assert poly[-1] == 1 and poly[0] == 2 and all(c % 2 == 0 for c in poly[:-1])
            assert all(evaluate(poly, t) == 2 for t in cuts)
            assert gcd(evaluate([i*c for i, c in enumerate(poly) if i], m), n) == 1
            for t in cuts[1:]:
                unit = (1 + (t//2)*evaluate(norm_two_quotient(poly, 0), m)) % n
                inv = (1 - (t//2)*evaluate(norm_two_quotient(poly, t), m)) % n
                assert unit*m % n == (m-t) % n and unit*inv % n == 1
        # Include the zero cut as padding, so all numerators have degree h-1.
        if 2*(1+cuts[-1])**(h-1) < m:
            residues = {prod(m-t for t in ts) % n
                        for ts in combinations_with_replacement(cuts, h-1)}
            assert len(residues) == comb(h+len(cuts)-2, len(cuts)-1)
            products += len(residues)
        pairs += 1
    assert largest >= 4 and pairs and factors and products > 100
    print(f"{pairs} planted pairs, {factors} proper gcds, {products} distinct products across fixtures")


if __name__ == "__main__":
    run()
