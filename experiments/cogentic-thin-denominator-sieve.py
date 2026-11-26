"""Replay the segmented projective relation sieve on exact finite grids."""

from collections import Counter, defaultdict
from itertools import groupby
from math import gcd, prod
from pathlib import Path
from runpy import run_path

evaluate = run_path(str(Path(__file__).with_name("cogentic-variable-multiple-lattice.py")))["evaluate"]


def root_rows(fields, primes):
    rows = []
    for side, coefficients in enumerate(fields):
        derivative = [i * c for i, c in enumerate(coefficients) if i]
        for p in primes:
            for r in range(p):
                if evaluate(coefficients, (r, 1)) % p == 0:
                    simple = evaluate(derivative, (r, 1)) % p != 0
                    rows.append((side, p, r, simple))
            if coefficients[-1] % p == 0:
                # At infinity use the reversed polynomial at the origin.
                rows.append((side, p, None, coefficients[-2] % p != 0))
    return rows


def merged_intervals(menu):
    grouped = defaultdict(list)
    for b, lo, hi in menu:
        grouped[b].append((lo, hi))
    for b, intervals in sorted(grouped.items()):
        merged = []
        for lo, hi in sorted(intervals):
            if merged and lo <= merged[-1][1] + 1:
                start, stop = merged[-1]
                merged[-1] = (start, max(stop, hi))
            else:
                merged.append((lo, hi))
        for lo, hi in merged:
            yield b, lo, hi


def segmented(fields, primes, menu, n, m, excluded_cofactor, segment_size):
    """Yield each primitive mark's two gcds, side supports and joint eligibility."""
    if segment_size <= 0:
        raise ValueError("segment size must be positive")
    rows = root_rows(fields, primes)
    for b, lo, hi in merged_intervals(menu):
        for start in range(lo, hi + 1, segment_size):
            stop = min(start + segment_size, hi + 1)
            hits = []
            for side, p, r, simple in rows:
                if r is None:
                    if b % p:
                        continue
                    candidates = range(start, stop)
                else:
                    if b % p == 0:
                        continue
                    first = start + (r * b - start) % p
                    candidates = range(first, stop, p)
                hits.extend((a, side, p, simple) for a in candidates if gcd(a, b) == 1)
            by_mark = {
                a: list(records) for a, records in groupby(sorted(hits), key=lambda row: row[0])
            }
            for a in range(start, stop):
                if gcd(a, b) != 1:
                    continue
                local = [{} for _ in fields]
                for _, side, p, simple in by_mark.get(a, ()):
                    local[side][p] = simple
                supports = []
                for coefficients, factors in zip(fields, local):
                    value = abs(evaluate(coefficients, (a, b)))
                    supports.append(tuple(factors) if value == prod(factors) else None)
                g, h = gcd(a - m*b, n), gcd(a - m*b, excluded_cofactor)
                keep = (g == h == 1 and all(s is not None for s in supports)
                        and all(all(factors.values()) for factors in local)
                        and local[0].keys().isdisjoint(local[1]))
                yield (a, b), (g, h, tuple(supports), keep)


def exhaustive(fields, primes, menu, n, m, excluded_cofactor):
    marks = {(a, b) for b, lo, hi in menu for a in range(lo, hi + 1) if gcd(a, b) == 1}
    for a, b in sorted(marks, key=lambda mark: mark[::-1]):
        supports = []
        clean = []
        for coefficients in fields:
            residual = abs(sum(c * a**i * b**(len(coefficients) - 1 - i)
                               for i, c in enumerate(coefficients)))
            factors = []
            simple = True
            for p in primes:
                if not residual or residual % p:
                    continue
                residual //= p
                factors.append(p)
                # Primitive marks use one of the two projective charts modulo p.
                c = coefficients if b % p else coefficients[::-1]
                num, den = (a, b) if b % p else (b, a)
                slope = num * pow(den, -1, p) % p
                simple &= sum(i * x * slope**(i-1) for i, x in enumerate(c) if i) % p != 0
            supports.append(tuple(factors) if residual == 1 else None)
            clean.append(simple)
        delta = a - m*b
        g, h = gcd(n, delta), gcd(excluded_cofactor, delta)
        keep = (g == h == 1 and all(clean) and None not in supports
                and set(supports[0]).isdisjoint(supports[1]))
        yield (a, b), (g, h, tuple(supports), keep)


def replay():
    primes = (2, 3, 5, 7, 11, 13, 17, 19)
    menu = ((23, -9, 29), (29, 1, 28), (23, 5, 17), (23, -9, 29),
            (23, 37, 40), (3, -13, 21), (5, 1, 18), (0, -2, 2), (1, -15, 15))
    cases = (
        (((-4, 0, 1), (7, 2)), 77, 4, 15),
        (((1, -2, 1), (1, 5)), 35, 1, 9),
        (((1, 0, 3), (-5, 1)), 65, 2, 21),
    )
    counts = Counter()
    for fields, n, m, cofactor in cases:
        expected = list(exhaustive(fields, primes, menu, n, m, cofactor))
        for size in (1, 3, 8, 19, 64):
            actual = list(segmented(fields, primes, menu, n, m, cofactor, size))
            assert actual == expected
            counts["comparisons"] += len(actual)
        for (_, b), (g, h, supports, keep) in expected:
            counts["proper gcd"] += 1 < g < n
            counts["full gcd"] += g == n
            counts["cofactor exclusions"] += g == 1 and h > 1
            counts["joint retained"] += keep
            counts["local poles with smooth norm"] += any(p in (s or ()) and b % p == 0
                                                           for p in primes for s in supports)
            counts["joint smooth but excluded"] += None not in supports and not keep
    assert all(counts[key] for key in ("proper gcd", "full gcd", "cofactor exclusions",
                                       "joint retained", "local poles with smooth norm",
                                       "joint smooth but excluded"))
    for key, value in counts.items():
        print(f"{key}: {value}")


if __name__ == "__main__":
    replay()
