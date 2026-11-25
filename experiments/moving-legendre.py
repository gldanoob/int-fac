"""Replay the deterministic parameter search and check finite Hasse intervals."""

from collections import deque
from fractions import Fraction
from itertools import combinations, combinations_with_replacement
from math import gcd, isqrt


def primes_up_to(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            length = (limit - p * p) // p + 1
            sieve[p * p :: p] = bytes(length)
    return [p for p in range(2, limit + 1) if sieve[p]]


def odd_scalar(n, bound):
    scalar = 1
    for p in primes_up_to(bound)[1:]:
        power = p
        while power * p <= 2 * n:
            power *= p
        scalar *= power
    return scalar


class ProperFactor(Exception):
    pass


def checked_gcd(value, n):
    g = gcd(value, n)
    if 1 < g < n:
        raise ProperFactor(g)
    return g


def affine_sum(left, right, a2, a4, n):
    if left is None:
        return right
    if right is None:
        return left
    x1, y1 = left
    x2, y2 = right
    if checked_gcd(x2 - x1, n) == n:
        if checked_gcd(y1 + y2, n) == n:
            return None
        assert checked_gcd(y1 - y2, n) == n
        denominator = 2 * y1
        numerator = 3 * x1 * x1 + 2 * a2 * x1 + a4
    else:
        denominator = x2 - x1
        numerator = y2 - y1
    assert checked_gcd(denominator, n) == 1
    slope = numerator * pow(denominator, -1, n) % n
    x3 = (slope * slope - a2 - x1 - x2) % n
    return x3, (slope * (x1 - x3) - y1) % n


def scalar_product(point, scalar, a2, a4, n):
    product = None
    for bit in bin(scalar)[2:]:
        product = affine_sum(product, product, a2, a4, n)
        if bit == "1":
            product = affine_sum(product, point, a2, a4, n)
    return product


def moves(x, y):
    yield x + 2 * y, y
    yield x - 2 * y, y
    yield x, y + 2 * x
    yield x, y - 2 * x


def parameters(seed, n, depth):
    pending = deque([(seed, 1, 0)])
    seen = set()
    while pending:
        x, y, level = pending.popleft()
        if checked_gcd(y, n) == 1:
            lam = x * pow(y, -1, n) % n
            if lam in seen:
                continue
            seen.add(lam)
            if all(checked_gcd(value, n) == 1 for value in (lam, lam - 1)):
                yield lam, level
        # Infinity is an allowed intermediate projective point.
        if level < depth:
            pending.extend((u % n, v % n, level + 1) for u, v in moves(x, y))


def marks(c, count):
    seen = set()
    for t in range(4, 8 * count + 21):
        denominator = (c - 1) * t * t - c
        if denominator == 0:
            continue
        u = Fraction((c - 1) * (t - 1) ** 2 + 1, denominator)
        a = c * u * u
        if a not in (0, 1) and a not in seen:
            seen.add(a)
            yield a
            if len(seen) == count:
                return


def marked_product(a, lam, scalar, n):
    if checked_gcd(a.denominator, n) == n:
        return
    x = a.numerator * pow(a.denominator, -1, n) % n
    d = x * (x - 1) * (x - lam) % n
    if checked_gcd(d, n) == n:
        return
    point = (d * x % n, d * d % n)
    return scalar_product(point, scalar, -d * (1 + lam) % n, d * d * lam % n, n)


def split(n, bound, depth, mark_count, scaled_seeds=False):
    """The search uses only the composite integer and the finite search caps."""
    scalar = odd_scalar(n, bound)
    seeds = (n >> j for j in range(n.bit_length())) if scaled_seeds else (isqrt(n),)
    try:
        for seed in seeds:
            for lam, _ in parameters(seed, n, depth):
                for c in range(2, n.bit_length() + 1):
                    for a in marks(c, mark_count):
                        marked_product(a, lam, scalar, n)
    except ProperFactor as found:
        return found.args[0]
    return None


def character(x, p):
    residue = pow(x % p, (p - 1) // 2, p)
    return -1 if residue == p - 1 else residue


def target_witness(p, q, bound, depth, mark_count):
    """Independent local check of the proof witness, before any global gcd."""
    n = p * q
    scalar = odd_scalar(n, bound)
    seed = isqrt(n)
    # Enumerate local image of integer words as whole homogeneous pairs.
    pending = deque([(seed, 1, 0)])
    while pending:
        x, y, level = pending.popleft()
        if level < depth:
            pending.extend((u, v, level + 1) for u, v in moves(x, y))
        if gcd(y, n) != 1:
            continue
        lam = x * pow(y, -1, n) % n
        if gcd(lam * (lam - 1), n) != 1:
            continue
        trace = -sum(character(x * (x - 1) * (x - lam), p) for x in range(p))
        for c in range(2, n.bit_length() + 1):
            sign = character(c, p)
            if sign == 0 or character(c - 1, p) != sign or character(c * (c - 1), q) != -1:
                continue
            size = p + 1 - sign * trace
            if size % 8 != 4 or scalar % (size // 4) or trace == 0 or trace * trace > p:
                continue
            for a in marks(c, mark_count):
                if gcd(a.denominator, n) != 1:
                    continue
                v = a.numerator * pow(a.denominator, -1, n) % n
                if gcd(v * (v - 1) * (v - lam), n) != 1 or character(v - lam, p) != sign:
                    continue
                assert marked_product(a, lam, scalar, p) is None
                assert marked_product(a, lam, scalar, q) is not None
                try:
                    marked_product(a, lam, scalar, n)
                except ProperFactor as found:
                    assert found.args[0] in (p, q)
                    return level
                raise AssertionError("mixed identity did not expose a factor")
    return None


def check_hasse():
    primes = primes_up_to(20200)
    smooth = []
    for m in range(1, 5101, 2):
        residual = m
        for p in primes[1:]:
            if p > 17:
                break
            while residual % p == 0:
                residual //= p
        if residual == 1:
            smooth.append(4 * m)
    counts = []
    for p in primes:
        if 10000 < p <= 20000:
            counts.append(sum((p + 1 - n) ** 2 <= p for n in smooth))
    print(f"Hasse primes = {len(counts)}, maximum candidates = {max(counts)}, empty intervals = {counts.count(0)}")


def integer_root(n, exponent):
    low, high = 1, 1 << ((n.bit_length() + exponent - 1) // exponent)
    while low < high:
        mid = (low + high + 1) // 2
        if mid**exponent <= n:
            low = mid
        else:
            high = mid - 1
    return low


def toy_prime(n):
    # Exact Boolean primality test on these finite examples.
    return n >= 2 and all(n % trial for trial in range(2, isqrt(n) + 1))


def full_factor(n):
    if n < 2:
        return []
    if toy_prime(n):
        return [n]
    for exponent in range(2, n.bit_length()):
        base = integer_root(n, exponent)
        if base**exponent == n:
            return full_factor(base) * exponent
    factor = split(n, bound=11, depth=2, mark_count=4, scaled_seeds=True)
    assert factor and 1 < factor < n and n % factor == 0
    return sorted(full_factor(factor) + full_factor(n // factor))


def check_scaled_seeds(primes):
    checks = 0
    for p in primes:
        for a in (1, 17, p, p * 127, 3**21):
            level = (p * a).bit_length() - 1
            for z in (128, 256, 4096):
                values = [(p * a * q) >> level for q in range(z + 1, 2 * z + 1)]
                assert len(set(values)) == z
                occupancy = [0] * p
                for value in values:
                    occupancy[value % p] += 1
                assert max(occupancy) <= 1 + (2 * z + p - 1) // p
                checks += 1
    family = list(combinations_with_replacement(primes[:12], 3))
    family += [tuple(sorted((p, p, q, q, q))) for p, q in combinations(primes[:7], 2)]
    for expected in family:
        n = 1
        for p in expected:
            n *= p
        assert sorted(full_factor(n)) == list(expected)
    print(f"scaled-seed fiber checks = {checks}, complete recursive factorizations = {len(family)}")


def main():
    check_hasse()
    primes = [p for p in primes_up_to(199) if p > 100]
    pairs = list(combinations(primes, 2))
    for p, q in pairs:
        assert split(p * q, bound=11, depth=2, mark_count=4) in (p, q)
    depths = [target_witness(p, q, 11, 2, 4) for p, q in pairs]
    reached = [d for d in depths if d is not None]
    print(f"blind splits = {len(pairs)}, certified marked witnesses = {len(reached)}, "
          f"first witnesses by word length 0,1,2 = {[reached.count(d) for d in range(3)]}")
    check_scaled_seeds(primes)


if __name__ == "__main__":
    main()
