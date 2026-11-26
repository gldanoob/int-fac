"""Replay Pell divisibility branches and a bounded Lucas scan."""

from math import gcd, isqrt
from pathlib import Path
from runpy import run_path


def power_four_factors(y, modulus, last):
    """Yield A_j, B_j modulo an odd modulus for j=1,4,...,4**last."""
    inverse_four = pow(4, -1, modulus)
    c = (y*y-4) % modulus
    trace, divided_trace = y % modulus, 1
    for _ in range(last+1):
        yield trace, ((c+1)*trace+2*c*divided_trace)*inverse_four % modulus
        for _ in range(2):
            trace, divided_trace = (
                (trace*trace-2) % modulus,
                trace*divided_trace % modulus,
            )


def bounded_split(n, *, require_embedding=False):
    for e, (a, b) in enumerate(power_four_factors(7, n, (n.bit_length()+1)//2)):
        factor = gcd(a, n)
        if 1 < factor < n and (not require_embedding or a*b % n == 0):
            return e, factor
    return None


def check():
    source = run_path(Path(__file__).with_name("cogentic-growing-pell-pair.py"))
    for m in (3, 5, 17):
        for e in range(4):
            c, u, v = source["pell_values"](m, 4**e)
            n = u*u+c
            a, b = list(power_four_factors(2*m+1, n, e))[-1]
            assert a*b == n
            assert (a, b) == (gcd(v-u, n), gcd(v+u, n))

    for p in range(3, 200, 2):
        if any(p % d == 0 for d in range(3, isqrt(p)+1, 2)):
            continue
        order = p-(1 if p % 4 == 1 else -1)
        counts = [0]*4
        for y in range(p):
            for e, (a, b) in enumerate(power_four_factors(y, p, 3)):
                counts[e] += a == 0
                assert a or b
                if p == 5:
                    assert b
        assert counts == [4**e if order % (4**(e+1)) == 0 else 0 for e in range(4)]

    for p, j, exponent, expected in ((7, 7, 2, 7), (7, 7, 3, 7), (19, 25, 1, 5)):
        modulus = p**exponent
        roots = 0
        for y in range(modulus):
            previous, trace = 2, y
            for _ in range(j-1):
                previous, trace = trace, (y*trace-previous) % modulus
            roots += trace == 0
        assert roots == expected

    assert [y for y in range(37) if 0 in list(power_four_factors(y, 37, 1))[-1]] == [21]
    assert list(power_four_factors(21, 37**2, 1))[-1][1] == 148
    assert all(0 not in list(power_four_factors(y, 37**2, 1))[-1] for y in range(37**2))
    assert bounded_split(2207*11) == (1, 2207)
    assert bounded_split(2207*11, require_embedding=True) is None
    assert bounded_split(72352081, require_embedding=True) == (1, 2207)
    print("Verified Pell factors, local trace counts, singular lifting and bounded splits")


if __name__ == "__main__":
    check()
