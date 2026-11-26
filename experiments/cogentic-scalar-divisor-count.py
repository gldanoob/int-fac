"""Exact-integer checks for the scalar counting reduction and its logarithmic bins."""

from fractions import Fraction
from itertools import combinations, product
from math import gcd, isqrt, prod


def ceil_div(x, d):
    return -((-x) // d)


def prime_band(B):
    return [p for p in range(isqrt(B) + 1, B + 1)
            if all(p % j for j in range(2, isqrt(p) + 1))]


def in_class(lo, hi, r, mod):
    return range(lo + (r - lo) % mod, hi + 1, mod)


def divisor(P, n):
    return n != 0 and P % abs(n) == 0


def restricted_count(P, omit, c, d, ts):
    """Remove selected factors by restriction to progressions in the index."""
    total = 0
    for k in range(len(omit) + 1):
        for ps in combinations(omit, k):
            m = prod(ps)
            A, D = c + d * ts.start, d * ts.step
            g = gcd(D, m)
            if A % g:
                continue
            period = m // g
            r = (-A // g * pow(D // g, -1, period)) % period
            hit = sum(divisor(P, A + j * D) for j in range(r, len(ts), period))
            total += (-1)**k * hit
    return total


def panels(x, y, p, q, a, b, width):
    delta = b - a

    def limits(t):
        lower, upper = t + delta*y, t + delta*(y+q-1)
        if a:
            lower = max(lower, t + ceil_div(delta*(t-x-p+1), a))
            upper = min(upper, t + delta*(t-x)//a)
        return lower, upper

    lo, hi = x + a*y, x+p-1 + a*(y+q-1)
    for l in range(lo, hi + 1, width):
        r = min(hi, l + width - 1)
        yield l, r, limits(r)[0], limits(l)[1], limits(l)[0], limits(r)[1]


def projected(P, box, marks, mod, accept, tests, width):
    x, y, p, q = box
    a, b = marks
    delta = b - a
    period = mod * delta
    inner = outer = 0
    for l, r, il, ir, ol, ore in panels(*box, a, b, width):
        for t0 in range(period):
            ts = in_class(l, r, t0, period)
            left = restricted_count(P, *tests[0], ts)
            if not left:
                continue
            for v0 in range(t0 % delta, period, delta):
                y0 = (v0 - t0) // delta
                if not accept(t0 - a*y0, y0):
                    continue
                inner += left * restricted_count(P, *tests[1], in_class(il, ir, v0, period))
                outer += left * restricted_count(P, *tests[1], in_class(ol, ore, v0, period))
    return inner, outer


def check_geometry():
    P = prod(prime_band(13))
    masks = [((5,), 3, -2), ((7,), -1, 3)]
    exact = bounds = strict = 0
    for x, y, p, q, (a, b), mod in product(
        (-4, 1), (-2, 2), (3, 8, 13), (2, 5), ((0, 2), (1, 2), (2, 5)), (1, 3)
    ):
        box = x, y, p, q
        accept = lambda s, t: (s + 2*t - 1) % mod == 0
        def event(t, mask):
            omit, c, d = mask
            v = c+d*t
            return divisor(P, v) and gcd(v, prod(omit)) == 1
        true = sum(accept(s, t) and event(s + a*t, masks[0]) and event(s+b*t, masks[1])
                   for s in range(x, x+p) for t in range(y, y+q))
        assert projected(P, box, (a, b), mod, accept, masks, 1) == (true, true)
        exact += 1
        for width in (2, 4):
            lo, hi = projected(P, box, (a, b), mod, accept, masks, width)
            assert lo <= true <= hi
            assert hi-lo <= 2*b*(width-1)*(p+a*(q-1))
            bounds += 1
            strict += lo < hi
    assert strict > 0
    return exact, bounds, strict


def upper_bins(primes, q, residue, low, high, K):
    """Count a certified logarithmic-bin superset, using integer bit lengths."""
    W = high.bit_length()
    top = (high**K).bit_length()-1
    bottom = (low**K).bit_length()-1-W
    states = {(0, 1 % q): 1}
    for p in primes:
        weight = (p**K).bit_length()-1
        new = states.copy()
        for (j, r), count in states.items():
            if j + weight <= top:
                key = j+weight, (r*p) % q
                new[key] = new.get(key, 0)+count
        states = new
    return sum(count for (j, r), count in states.items()
               if j >= bottom and r == residue % q)


def check_bins():
    fixtures = loose = accurate = 0
    for B in (13, 23):
        primes = prime_band(B)
        divs = [prod(ps) for k in range(len(primes)+1) for ps in combinations(primes, k)]
        for q, first, T in product((1, 4, 9, 13), (1, 5, 37), (10, 31, 120)):
            high = first+q*(T-1)
            W = high.bit_length()
            expected = sum(first <= n <= high and (n-first) % q == 0 for n in divs)
            for K in (W+1, 4*(W+1)):
                upper = upper_bins(primes, q, first, first, high, K)
                assert expected <= upper <= expected + 4*Fraction(high*(W+1), K*q) + 2
                loose += upper > expected
                fixtures += 1
            eps = Fraction(1, 8)
            if T >= 4/eps:
                K = ceil_div(16*(W+1)*(q*T + high)*eps.denominator, q*T*eps.numerator)
                upper = upper_bins(primes, q, first, first, high, K)
                assert 0 <= upper-expected <= eps*T
                accurate += 1
    assert loose and accurate
    return fixtures, loose, accurate


if __name__ == "__main__":
    print("Projected two-mark counts, brackets, strict brackets", check_geometry())
    print("Log-bin bounds, strict overcounts, prescribed-accuracy checks", check_bins())
