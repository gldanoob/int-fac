"""Search for exact six-mark order certificates on fixed semiprime cohorts."""

from collections import Counter
from fractions import Fraction
from math import gcd, isqrt, lcm, prod


STEP_CAP = 160
MARK_CAP = 600
LABEL_CAP = 512
TARGET_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19)
SMALL = (143, 221, 323, 437, 667, 899, 1147, 1517, 1763, 2021, 2491, 3127)
LARGE = (272483, 282943, 295927, 304679, 313591, 320347)


def factor_table(bound):
    factors = [{} for _ in range(bound + 1)]
    for prime in range(2, bound + 1):
        if factors[prime]:
            continue
        power = prime
        while power <= bound:
            for value in range(power, bound + 1, power):
                factors[value][prime] = factors[value].get(prime, 0) + 1
            power *= prime
    return factors


def clean_shapes(factors):
    shapes = []
    for step in range(2, STEP_CAP + 1):
        for offset in range(1, step):
            delta = 4 * step**2 - offset**2
            if (step**2 - offset**2) % 3 == 0 or isqrt(3 * delta)**2 == 3 * delta:
                continue
            pairs = [
                (step + offset, 2 * step + offset),
                (step - offset, step + offset),
                (step - offset, 2 * step - offset),
            ]
            if all(
                gcd(a, b) == 1
                and all(e == 1 for t in (a, b) for e in factors[t].values())
                for a, b in pairs
            ):
                shapes.append((step, offset, delta, prod(a * b for a, b in pairs)))
    return shapes


def centered_label(mark, modulus, height):
    residue = min(mark % modulus, -mark % modulus)
    numerator, denominator = residue, 1
    previous, previous_denominator = modulus, 0
    while numerator > height:
        quotient = previous // numerator
        previous, numerator = numerator, previous - quotient * numerator
        previous_denominator, denominator = denominator, previous_denominator - quotient * denominator
    assert (numerator - residue * denominator) % modulus == 0
    return numerator, abs(denominator)


def add_scaled(row, source, scale):
    for key, amount in source.items():
        updated = row.get(key, 0) + scale * amount
        if updated:
            row[key] = updated
        else:
            row.pop(key, None)


def reduce_row(row, coefficients, basis):
    while row and (pivot := min(row)) in basis:
        old_row, old_coefficients = basis[pivot]
        scale = -row[pivot]
        add_scaled(row, old_row, scale)
        add_scaled(coefficients, old_coefficients, scale)


def split_from_order(base, exponent, modulus):
    assert pow(base, exponent, modulus) == 1
    for prime in TARGET_PRIMES:
        while exponent % prime == 0:
            residue = pow(base, exponent // prime, modulus)
            factor = gcd(residue - 1, modulus)
            if 1 < factor < modulus:
                return factor
            if residue != 1:
                break
            exponent //= prime
    return None


def sweep(modulus, shapes, factors, mark_cap, label_cap, one_root_class=False):
    counts = Counter()
    centers = {delta % modulus: [] for _, _, delta, _ in shapes}
    for z in range(1, 2 * mark_cap + 1):
        key = 3 * z * z % modulus
        if key in centers:
            centers[key].append(z)

    basis, chart_rows, root_classes = {}, {}, {}
    for step, offset, delta, norm_product in shapes:
        matches = centers[delta % modulus]
        counts["root_matches"] += len(matches)
        for z in matches:
            if (z - offset) % 2:
                continue
            a = (z - offset) // 2 - step
            if not 1 <= a <= mark_cap - 2 * step - offset:
                continue
            counts["charts"] += 1
            assert (3 * z * z - delta) % (4 * modulus) == 0
            if gcd(norm_product, modulus) != 1:
                counts["norm_nonunit"] += 1
                continue
            marks = [a + j * step + shift for shift in (0, offset) for j in range(3)]
            if any(gcd(mark, modulus) != 1 for mark in marks):
                counts["mark_nonunit"] += 1
                continue
            labels = [centered_label(mark, modulus, label_cap) for mark in marks]
            if any(denominator > label_cap for _, denominator in labels):
                counts["label_height"] += 1
                continue
            if any(gcd(denominator, modulus) != 1 for _, denominator in labels):
                counts["label_nonunit"] += 1
                continue
            if one_root_class:
                center_class = min(z % modulus, -z % modulus)
                if root_classes.setdefault(delta % modulus, center_class) != center_class:
                    counts["second_root_class"] += 1
                    continue
            counts["admitted"] += 1

            row = {}
            ratio = Fraction(1)
            for index, (num, den) in enumerate(labels):
                sign = 1 if index < 3 else -1
                add_scaled(row, factors[num], sign)
                add_scaled(row, factors[den], -sign)
                ratio *= Fraction(num, den) ** sign
            assert ratio.numerator * pow(ratio.denominator, -1, modulus) % modulus in (1, modulus - 1)
            chart = (a, step, offset)
            original_row = row.copy()
            coefficients = {chart: 1}
            reduce_row(row, coefficients, basis)
            if row:
                pivot = min(row)
                scale = Fraction(1, row[pivot])
                basis[pivot] = (
                    {p: value * scale for p, value in row.items()},
                    {c: value * scale for c, value in coefficients.items()},
                )
                chart_rows[chart] = original_row

    counts["rank"] = len(basis)
    first_hit = None
    for base in TARGET_PRIMES:
        if gcd(base, modulus) != 1:
            counts["target_nonunit"] += 1
            continue
        target, coefficients = {base: 1}, {}
        reduce_row(target, coefficients, basis)
        if target:
            continue
        counts["relations"] += 1
        exponent = lcm(*(value.denominator for value in coefficients.values()))
        certificate = {}
        for chart, value in coefficients.items():
            add_scaled(certificate, chart_rows[chart], int(-value * exponent))
        assert certificate == {base: exponent}
        factor = split_from_order(base, 2 * exponent, modulus)
        if factor is not None:
            counts["splits"] += 1
            if first_hit is None:
                first_hit = (base, exponent, factor, len(coefficients))
    return counts, first_hit


def main():
    factors = factor_table(MARK_CAP)
    shapes = clean_shapes(factors)
    assert len(shapes) == 1408
    print(f"Retained {len(shapes)} of {STEP_CAP * (STEP_CAP - 1) // 2} shapes.", flush=True)
    screenings = ("norm_nonunit", "mark_nonunit", "label_nonunit", "target_nonunit")
    for mode, cohort in (("short", SMALL), ("short", LARGE), ("wide", LARGE)):
        for modulus in cohort:
            mark_cap = MARK_CAP if mode == "short" else 128 * (1 + isqrt(modulus))
            label_cap = MARK_CAP if mode == "short" else LABEL_CAP
            counts, hit = sweep(modulus, shapes, factors, mark_cap, label_cap)
            if modulus in LARGE:
                assert all(counts[screen] == 0 for screen in screenings)
            assert (hit is not None) == (mode == "wide" or cohort == SMALL)
            print(mode, modulus, mark_cap, dict(counts), hit, flush=True)
            if (mode, modulus) == ("wide", LARGE[0]):
                assert hit == (2, 86645694232138633020, 523, 86)

    modulus = LARGE[0]
    mark_cap = 128 * (1 + isqrt(modulus))
    counts, hit = sweep(modulus, shapes, factors, mark_cap, LABEL_CAP, one_root_class=True)
    assert all(counts[screen] == 0 for screen in screenings)
    assert counts["second_root_class"] == 81 and counts["admitted"] == 256
    assert hit == (2, 1142603024707663005240, 523, 89)
    print("one-root-class", modulus, mark_cap, dict(counts), hit, flush=True)


if __name__ == "__main__":
    main()
