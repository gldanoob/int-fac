"""Replay the two-layer threshold test for signed affine squarefree norms."""

from itertools import product
from math import prod


def affine_gate(offset, weights, threshold):
    return lambda bits: offset + sum(a * b for a, b in zip(weights, bits)) >= threshold


def add_equality(terms, multiplier, offset, weights, target):
    terms.append((multiplier, affine_gate(offset, weights, target)))
    terms.append((-multiplier, affine_gate(offset, weights, target + 1)))


def add_divisible(terms, multiplier, offset, weights, modulus):
    reduced = tuple(a % modulus for a in weights)
    offset %= modulus
    for target in range(0, offset + sum(reduced) + 1, modulus):
        add_equality(terms, multiplier, offset, reduced, target)


def add_defect(terms, form, primes, width, scale):
    offset, weights = form
    digit_weight = {p: (p**scale).bit_length() - 1 for p in primes}
    add_equality(terms, scale + sum(digit_weight.values()), offset, weights, 0)
    for p in primes:
        add_divisible(terms, -digit_weight[p], offset, weights, p)
    # Several log bins can round to the same integer cut.
    for exponent in range(width * scale):
        lo, hi = 0, 1 << width
        while hi - lo > 1:
            mid = (hi + lo) // 2
            if mid**scale <= 1 << exponent:
                lo = mid
            else:
                hi = mid
        terms.append((1, affine_gate(offset, weights, hi)))
        terms.append((1, affine_gate(-offset, tuple(-a for a in weights), hi)))


def threshold_test(forms, primes, row):
    bound = max(abs(offset) + sum(map(abs, weights)) for offset, weights in forms)
    width = max(1, bound.bit_length())
    scale = 1 + len(forms) * (width + 1)
    terms = []
    for form, prime_list in zip(forms, primes):
        add_defect(terms, form, prime_list, width, scale)
    row_offset, row_weights, modulus = row
    add_divisible(terms, -scale, row_offset, row_weights, modulus)

    def evaluate(bits):
        defect = scale + sum(weight for weight, gate in terms if gate(bits))
        return defect < scale

    return evaluate


def main():
    forms = ((-25, (1, 2, 4, 8, 16, 32)), (23, (3, -2, 5, -7, 2, -15)),
             (1, (0, 0, 0, 0, 0, 0)), (-1, (0, 0, 0, 0, 0, 0)))
    row = (-2, (1, 2, 0, 1, 2, 0), 3)
    checks = hits = 0
    for selected in ((forms[0],), forms[:2], forms):
        for band in ((), (2,), (2, 3, 5, 7), (3, 5, 7, 11, 13)):
            primes = tuple(band if i % 2 == 0 else band[1:] for i in range(len(selected)))
            test = threshold_test(selected, primes, row)
            for bits in product((0, 1), repeat=6):
                def value(form):
                    return form[0] + sum(a * b for a, b in zip(form[1], bits))

                accepted = value(row) % row[2] == 0 and all(
                    value(f) and prod(ps) % abs(value(f)) == 0
                    for f, ps in zip(selected, primes))
                assert test(bits) == bool(accepted)
                hits += bool(accepted)
                checks += 1
    assert 0 < hits < checks
    print(f"{checks} exact threshold tests, {hits} accepted")


if __name__ == "__main__":
    main()
