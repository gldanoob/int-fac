"""Batch weighted factor-gap windows for N=pQ, with Q allowed to be composite."""

import argparse
from bisect import bisect_left
from math import gcd, isqrt, lcm
from pathlib import Path
from runpy import run_path

from sage.all import PolynomialRing, Zmod, prime_range


COLLISIONS = run_path(str(Path(__file__).with_name("cogentic-unit-collision-search.py")))


def ceil_sqrt(value):
    return isqrt(value - 1) + 1 if value else 0


def exponent_windows(n, hypotheses):
    windows = []
    for a, b, gap in hypotheses:
        if min(a, b) < 1 or gap < 0:
            raise ValueError("require positive weights and a nonnegative gap")
        product = 4*a*b*n
        low_sum = ceil_sqrt(product)
        high_sum = isqrt(product + gap*gap)
        if low_sum <= high_sum:
            origin = a*n + b
            windows.append((origin-high_sum, origin-low_sum, a, b))
    return windows


def divisor_through(n, limit):
    """Find a divisor through limit by monic block products."""
    last = min(limit, isqrt(n))
    if last < 2:
        return None
    width = ceil_sqrt(last-1)
    starts = list(range(2, last+1, width))
    ring = PolynomialRing(Zmod(n), "x", implementation="NTL")
    x = ring.gen()
    block = COLLISIONS["product_tree"]([x+i for i in range(width)])[-1][0]
    tree = COLLISIONS["product_tree"]([x-a for a in starts])
    for start, value in zip(starts, COLLISIONS["evaluate"](block, tree), strict=True):
        if gcd(n, value) > 1:
            for a in range(start, min(start+width, last+1)):
                divisor = gcd(a, n)
                if 1 < divisor < n:
                    return divisor
    return None


def baby_basis(n, width):
    """Return a factor or bases whose joint order is at least width."""
    bases = []
    period = 1
    bit_length = n.bit_length()
    primes_seen = 0
    bound = min(bit_length**4, isqrt(n))
    for prime in prime_range(2, bound+1):
        base = int(prime)
        primes_seen += 1
        if n % base == 0:
            return base, []
        powers = COLLISIONS["progression"](n, 1, base, width+1)
        try:
            order = powers.index(1, 1)
        except ValueError:
            return None, [base]
        combined = lcm(period, order)
        if combined > period or not bases:
            bases.append(base)
        period = combined
        if period >= width:
            return None, bases

    if bound == isqrt(n):
        return None, []
    # More distinct small-prime products than the common exponent can
    # accommodate in any cyclic residue group force a small prime divisor.
    count = 1
    for k in range(1, primes_seen+1):
        count = count * (primes_seen-k+1) // k
        if count > period:
            return divisor_through(n, bound**k), []
    return divisor_through(n, isqrt(n)), []


def decode(n, a, b, exponent):
    total = a*n + b - exponent
    discriminant = total*total - 4*a*b*n
    if total <= 0 or discriminant < 0:
        return None
    root = isqrt(discriminant)
    if root*root != discriminant:
        return None
    for twice_bp in (total-root, total+root):
        p, remainder = divmod(twice_bp, 2*b)
        if not remainder and 1 < p < n and n % p == 0:
            return p
    return None


def search(n, hypotheses):
    if n < 2:
        raise ValueError("require N >= 2")
    windows = exponent_windows(n, hypotheses)
    if not windows:
        return None
    width = ceil_sqrt(sum(high-low+1 for low, high, _, _ in windows))
    if width >= isqrt(n):
        return divisor_through(n, isqrt(n))
    divisor, bases = baby_basis(n, width)
    if divisor is not None or not bases:
        return divisor
    starts = [(j, high, a, b) for low, high, a, b in windows
              for j in range(low, high+1, width)]
    baby_columns, giant_columns = [], []
    for base in bases:
        babies = COLLISIONS["progression"](n, 1, pow(base, -1, n), width)
        giants = [pow(base, j, n) for j, _, _, _ in starts]
        hit = COLLISIONS["local_collision"](n, babies, giants)
        if hit is not None:
            return hit["factor"]
        baby_columns.append(babies)
        giant_columns.append(giants)
    ordered = sorted((key, i) for i, key in enumerate(zip(*baby_columns, strict=True)))
    for key, (start, high, a, b) in zip(zip(*giant_columns, strict=True), starts, strict=True):
        pos = bisect_left(ordered, (key, -1))
        if pos < len(ordered) and ordered[pos][0] == key:
            exponent = start + ordered[pos][1]
            if exponent <= high:
                divisor = decode(n, a, b, exponent)
                if divisor is not None:
                    return divisor
    return None


def replay():
    assert divisor_through(121, 10) is None and divisor_through(121, 11) == 11
    assert baby_basis(17, 20) == (None, [])
    checked = 0
    for p in (7, 13, 31):
        for cofactor in (11, 19, 25, 49, 55, 91):
            n = p*cofactor
            for a, b in ((1, 1), (2, 3), (7, 1)):
                gap = abs(a*cofactor-b*p)
                result = search(n, [(3, 5, 1), (a, b, gap)])
                assert result is not None and 1 < result < n and n % result == 0
                checked += 1
    assert search(101, [(1, 1, 10)]) is None
    # The first global match is a decoy. The second window decodes 37.
    assert decode(2701, 6, 6, 15588) is None
    assert search(2701, [(6, 6, 40), (1, 2, 1)]) == 37
    print(f"{checked} weighted windows returned verified factors, including composite cofactors.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?")
    parser.add_argument("--window", type=int, nargs=3, action="append", metavar=("A", "B", "GAP"))
    args = parser.parse_args()
    if args.N is None:
        replay()
    elif not args.window:
        parser.error("supply at least one --window A B GAP")
    else:
        print(search(args.N, args.window))
