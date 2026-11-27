"""Measure smooth quadratic values at independent synthetic primitive anchors."""

from argparse import ArgumentParser
from collections import Counter
from functools import cache
from math import gcd, hypot, inf, isqrt, prod, sqrt
from random import Random
from statistics import fmean, stdev


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


def is_smooth(value, primorial):
    while value > 1:
        shared = gcd(value, primorial)
        if shared == 1:
            return False
        value //= shared
    return True


def draw_long_anchors(rng, size, lower, parent, marks, primorial):
    rows = []
    for _ in range(size):
        r, q = sample_anchor(rng, lower, parent)
        slope = r * pow(q, -1, parent) % parent
        rr, rq, qq = r * r, r * q, q * q
        raw = Counter()
        smooth = Counter()
        for a, b, c in marks(slope):
            value, remainder = divmod(a * rr + b * rq + c * qq, parent)
            assert remainder == 0 and value > 0
            band = value.bit_length()
            raw[band] += 1
            if is_smooth(value, primorial):
                smooth[band] += 1
        rows.append((raw, smooth))
    return rows


def report_long(calibration, reporting):
    calibration_raw = Counter()
    calibration_smooth = Counter()
    for raw, smooth in calibration:
        calibration_raw.update(raw)
        calibration_smooth.update(smooth)
    rates = {band: calibration_smooth[band] / count for band, count in calibration_raw.items()}

    size = len(reporting)
    raw_totals, smooth_totals, iid_means, iid_hits, iid_pairs = [], [], [], [], []
    gradient = Counter()
    for raw, smooth in reporting:
        raw_totals.append(raw.total())
        smooth_totals.append(smooth.total())
        iid_mean = sum(count * rates[band] for band, count in raw.items())
        iid_means.append(iid_mean)
        iid_hits.append(1 - prod((1 - rates[band]) ** count for band, count in raw.items()))
        iid_pairs.append(iid_mean**2 - sum(count * rates[band] ** 2 for band, count in raw.items()))
        for band, count in raw.items():
            gradient[band] += 2 * count * (iid_mean - rates[band]) / size

    observed_pairs = [count * (count - 1) for count in smooth_totals]
    pair_differences = [observed - iid for observed, iid in zip(observed_pairs, iid_pairs)]
    # Treat each anchor as a single sampling unit in both independent streams.
    calibration_size = len(calibration)
    calibration_weights = {
        band: slope * calibration_size / calibration_raw[band] for band, slope in gradient.items()
    }
    calibration_influence = [
        sum(weight * (smooth[band] - rates[band] * raw[band]) for band, weight in calibration_weights.items())
        for raw, smooth in calibration
    ]
    anchor_se = stdev(pair_differences) / sqrt(size)
    calibration_se = stdev(calibration_influence) / sqrt(calibration_size)
    diff = fmean(pair_differences)
    margin = 1.96 * hypot(anchor_se, calibration_se)
    print(f"  calibration raw={calibration_raw.total()} smooth={calibration_smooth.total()}; "
          f"report raw={sum(raw_totals)} smooth={sum(smooth_totals)}, raw/anchor={fmean(raw_totals):.4f}")
    print(f"  smooth/anchor={fmean(smooth_totals):.6f}, iid={fmean(iid_means):.6f}, "
          f"hit={fmean(count > 0 for count in smooth_totals):.6f}, iid_hit={fmean(iid_hits):.6f}")
    print(f"  ordered pairs={sum(observed_pairs)}, iid={sum(iid_pairs):.2f}, "
          f"pair-positive anchors={sum(count >= 2 for count in smooth_totals)}")
    print(f"  pairs/anchor={fmean(observed_pairs):.6f}, raw pairs/anchor="
          f"{fmean(count * (count - 1) for count in raw_totals):.4f}, iid_pairs/anchor={fmean(iid_pairs):.6f}, "
          f"difference={diff:.6f}, approx. 95% CI=[{diff-margin:.6f},{diff+margin:.6f}], "
          f"SE(anchor,calibration)=({anchor_se:.6f},{calibration_se:.6f})")


def run_long():
    parent, height, cutoff = 257, 232, 229
    calibration_size, reporting_size = 2_048, 4_096
    calibration_seed, reporting_seed = 20261128, 20261129
    flags = primes_up_to(parent)
    assert flags[parent] and cutoff < height < parent
    primes = [prime for prime in range(2, cutoff + 1) if flags[prime]]
    primorial = prod(primes)
    assert all(is_smooth(n, primorial) == (smooth_threshold(n, primes) <= cutoff) for n in range(1, 2_001))
    squarefree = squarefree_up_to(4 * height**2)

    @cache
    def marks(slope):
        return tuple(root_marks(parent, height, slope, squarefree))

    calibration_rng, reporting_rng = Random(calibration_seed), Random(reporting_seed)
    print(f"p={parent}, V={height}, B={cutoff}, calibration={calibration_size} seed={calibration_seed}, "
          f"reporting={reporting_size} seed={reporting_seed} per dyad")
    for power, lower in ((2, parent**2), (2.5, isqrt(parent**5))):
        calibration = draw_long_anchors(calibration_rng, calibration_size, lower, parent, marks, primorial)
        reporting = draw_long_anchors(reporting_rng, reporting_size, lower, parent, marks, primorial)
        print(f"Q≈p^{power}, Q=[{lower},{2*lower}), odd primitive anchors, 0.57≤r/Q≤0.63")
        report_long(calibration, reporting)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--long", action="store_true", help="use longer dyads and a held-out report")
    args = parser.parse_args()
    check_enumeration()
    if args.long:
        run_long()
        return
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
