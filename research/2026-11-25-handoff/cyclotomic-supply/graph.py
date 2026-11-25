"""Exact synthetic checks of line-factor slope aliases and floor levels."""
from collections import Counter
from math import gcd, isqrt

X, Q, ell = 2**16, 5, 43
H = Q * Q


def prime(n):
    return n >= 2 and all(n % j for j in range(2, isqrt(n) + 1))


p = next(t for t in range(X + 1, 2 * X)
         if (t*t + t + 1) % ell == 0 and prime(t))


def floor_root(x, n):
    lo, hi = 0, 1 << ((x.bit_length() + n - 1) // n)
    while hi - lo > 1:
        y = (hi + lo) // 2
        if y**n > x:
            hi = y
        else:
            lo = y
    return lo


def floor_graph(v, a, m, n):
    return floor_root((a*p*v)**m, n)


def tangent(v, a, m, n):
    for d in range(1, Q + 1):
        left = (d * Q * m)**n * (a*p)**m
        right = n**n * v**(n-m)
        u0 = floor_root(left // right, n) // Q
        for u in (u0, u0+1):
            if gcd(d, u) == 1 and (max(0, u*Q-1)**n * right
                                    <= left <= (u*Q+1)**n * right):
                return u, d
    raise ArithmeticError("Dirichlet approximation")


def check_tangents(a, m, n):
    slopes = [tangent(v, a, m, n) for v in range(X+1, 2*X+1, H)]
    classes = Counter(u * pow(d, -1, ell) % ell for u, d in set(slopes))
    bad_slope = max(classes, key=classes.get)
    assert classes[bad_slope] >= 2
    good_hits = bad_hits = max_lines = 0
    for start, (u, d) in zip(range(X+1, 2*X+1, H), slopes):
        bad = (u - bad_slope*d) % ell == 0
        lines = Counter()
        hits = Counter()
        for v in range(start, min(start+H, 2*X+1)):
            y = floor_graph(v, a, m, n)
            z = d*y-u*v
            lines[z] += 1
            if (y - bad_slope*v - 1) * (y*y+p*v+7) % ell == 0:
                hits[z] += 1
        max_lines = max(max_lines, len(lines))
        if bad:
            bad_hits += sum(hits.values())
        else:
            assert max(hits.values(), default=0) <= 3
            good_hits += sum(hits.values())
    print("tangent", a, m, n, "p", p, "ell", ell,
          "bad slope", bad_slope, "distinct aliases", classes[bad_slope],
          "good hits", good_hits, "exceptional hits", bad_hits, "max lines", max_lines)


def check_levels(a, m, n):
    levels = Counter()
    hits = Counter()
    for v in range(X+1, 2*X+1):
        y = floor_graph(v, a, m, n)
        levels[y] += 1
        if (y-2)*(p*v+3) % ell == 0:
            hits[y] += 1
    bad = [y for y in levels if y % ell == 2]
    for y, count in hits.items():
        assert count <= (levels[y] if y in bad else (levels[y]+ell-1)//ell)
    assert any((y in hits for y in bad))
    print("levels", a, m, n, "p", p, "ell", ell, "levels", len(levels),
          "exceptional levels", len(bad), "hits", sum(hits.values()),
          "exceptional hits", sum(hits[y] for y in bad))


if __name__ == "__main__":
    check_tangents(1, 4, 5)
    check_tangents(7, 3, 4)
    check_levels(1, 1, 3)
