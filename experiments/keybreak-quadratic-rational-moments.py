"""Measure smooth quadratic values at independent synthetic primitive anchors."""

from collections import Counter
from math import gcd, inf, isqrt, prod
from random import Random


PARENT = 100_003
HEIGHT = 282
CUTOFFS = (251, 503, 1009)
ANCHORS_PER_DYAD = 2_048
SEED = 20261127


def primes_up_to(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[:2] = b"\0\0"
    for prime in range(2, isqrt(limit) + 1):
        if flags[prime]:
            flags[prime * prime :: prime] = bytes((limit - prime * prime) // prime + 1)
    return flags


def coefficient_ranges(height):
    leading = range(((height + 1) // 2) | 1, height + 1, 2)
    middle = range((-(height // 2)) | 1, height // 2 + 1, 2)
    constant = range(2 * ((height + 7) // 8), 3 * height // 4 + 1, 2)
    return leading, middle, constant


def root_marks(parent, height, slope, squarefree):
    leading, middle, constant = coefficient_ranges(height)
    # The box forces 4ac > b², and the parity forces D ≡ 1 mod 8.
    for a in leading:
        for b in middle:
            c = (-a * slope * slope - b * slope) % parent
            if c in constant and squarefree[4 * a * c - b * b]:
                yield a, b, c


def squarefree_up_to(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[0] = 0
    for base in range(2, isqrt(limit) + 1):
        square = base * base
        flags[square::square] = bytes(limit // square)
    return flags


def check_enumeration():
    parent, height = 31, 12
    flags = squarefree_up_to(4 * height**2)
    leading, middle, constant = coefficient_ranges(height)
    for slope in range(parent):
        expected = set()
        for a in leading:
            for b in middle:
                for c in constant:
                    discriminant = b * b - 4 * a * c
                    fundamental = discriminant < 0 and discriminant % 8 == 1 and all(
                        discriminant % (k * k) for k in range(2, isqrt(-discriminant) + 1)
                    )
                    vanishes = (a * slope**2 + b * slope + c) % parent == 0
                    if fundamental and gcd(a, gcd(b, c)) == 1 and vanishes:
                        expected.add((a, b, c))
        actual = list(root_marks(parent, height, slope, flags))
        assert len(actual) == len(expected) and set(actual) == expected
    print(f"self-check: modular enumeration equals brute force at all {parent} slopes")


def sample_anchor(rng, lower, parent):
    while True:
        q = rng.randrange(lower | 1, 2 * lower, 2)
        r = rng.randrange(57 * lower // 100, 126 * lower // 100 + 1)
        if 57 * q <= 100 * r <= 63 * q and q % parent and gcd(r, q) == 1:
            return r, q


def smooth_threshold(value, primes):
    largest = 1
    for prime in primes:
        if value == 1:
            return largest
        while value % prime == 0:
            value //= prime
            largest = prime
    return largest if value == 1 else inf


def report(rows, cutoff):
    raw = sum(len(row) for row in rows)
    raw_pairs = sum(len(row) * (len(row) - 1) for row in rows)
    smooth = [sum(largest <= cutoff for _, largest in row) for row in rows]
    hits = sum(count > 0 for count in smooth)
    pairs = sum(count * (count - 1) for count in smooth)
    density = sum(smooth) / raw
    # The second benchmark keeps each mark's cofactor-size bin fixed.
    strata = Counter(band for row in rows for band, _ in row)
    stratum_smooth = Counter(band for row in rows for band, largest in row if largest <= cutoff)
    probabilities = {band: stratum_smooth[band] / count for band, count in strata.items()}
    independent_pairs = independent_hits = 0.0
    for row in rows:
        rates = [probabilities[band] for band, _ in row]
        independent_pairs += sum(rates) ** 2 - sum(rate**2 for rate in rates)
        independent_hits += 1 - prod(1 - rate for rate in rates)
    size = len(rows)
    flat_pairs = density**2 * raw_pairs
    flat_hits = sum(1 - (1 - density) ** len(row) for row in rows)
    print(f"  B={cutoff:3}: S={sum(smooth):5}, mean={sum(smooth)/size:.4f}, smooth/raw={density:.4f}, "
          f"pairs={pairs:5} ({pairs/size:.4f}/anchor), flat={flat_pairs:.1f}, "
          f"by_size={independent_pairs:.1f}, pair_ratio={pairs/independent_pairs:.3f}, "
          f"hit={hits/size:.4f}, flat_hit={flat_hits/size:.4f}, by_size_hit={independent_hits/size:.4f}")


def main():
    check_enumeration()
    rng = Random(SEED)
    flags = primes_up_to(12 * PARENT)
    assert flags[PARENT]
    primes = [prime for prime in range(2, max(CUTOFFS) + 1) if flags[prime]]
    squarefree = squarefree_up_to(4 * HEIGHT**2)
    print(f"p={PARENT}, V={HEIGHT}, seed={SEED}, draws/dyad={ANCHORS_PER_DYAD}")
    for lower in (3 * PARENT, 6 * PARENT):
        rows = []
        composite_count = 0
        roots = set()
        min_value = inf
        max_value = 0
        for _ in range(ANCHORS_PER_DYAD):
            r, q = sample_anchor(rng, lower, PARENT)
            composite_count += not flags[q]
            slope = r * pow(q, -1, PARENT) % PARENT
            roots.add(slope)
            row = []
            for a, b, c in root_marks(PARENT, HEIGHT, slope, squarefree):
                value, remainder = divmod(a * r * r + b * r * q + c * q * q, PARENT)
                assert remainder == 0 and value > 0
                min_value = min(min_value, value)
                max_value = max(max_value, value)
                row.append((value.bit_length(), smooth_threshold(value, primes)))
            rows.append(row)
        size = len(rows)
        mean = sum(map(len, rows)) / size
        pairs = sum(len(row) * (len(row) - 1) for row in rows) / size
        print(f"Q=[{lower},{2*lower}), composite={composite_count}/{size}, roots={len(roots)}, "
              f"values=[{min_value},{max_value}], raw_total={sum(map(len, rows))}, "
              f"raw_mean={mean:.4f}, raw_pairs={pairs:.4f}, raw_pairs/mean^2={pairs/mean**2:.3f}")
        for cutoff in CUTOFFS:
            report(rows, cutoff)


if __name__ == "__main__":
    main()
