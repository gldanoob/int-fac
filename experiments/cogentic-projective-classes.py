"""Check the divided one- and two-mark laws of a homogeneous perturbation."""

from collections import Counter, defaultdict
from itertools import product
from math import gcd


def projective_pairs(p):
    # Every pair has different prime-to-p denominators and affine slopes other than m=1.
    marks = [(a, b) for b in (p + 1, 2 * p + 1, 3 * p + 1)
             for a in range(1, 2 * p * p + 2) if gcd(a, b) == 1 and (a - b) % p]
    examples = {}
    for a, b in marks:
        for c, d in marks:
            det = abs(a * d - b * c)
            if not det or b == d:
                continue
            valuation = 0 if det % p else (1 if det % (p * p) else 2)
            examples.setdefault((valuation, a % p == 0, c % p == 0), ((a, b), (c, d)))
    return list(examples.values())


def check_case(p, first, second, special, prescribed):
    # F = X^4+XY^3 + K Y(X-Y)G with deg G=2. At the regular prescribed
    # row 0 the residue condition is u0=0. At a special prime F mod p is fixed.
    modulus = p * p
    kappa = p if special else 1

    def mark_data(mark):
        a, b = mark
        base = a**4 + a * b**3
        forced = (base % p == 0) if special else (prescribed and a % p == 0)
        return base, kappa * b * (a - b), p if forced else 1

    a, b = first
    c, d = second
    f1, multiplier1, pre1 = mark_data(first)
    f2, multiplier2, pre2 = mark_data(second)
    output_mod1 = kappa * modulus // pre1
    output_mod2 = kappa * modulus // pre2
    determinant_part = gcd(abs(a * d - b * c), modulus)
    step1 = kappa if not special else kappa // pre1
    # A prescribed ordinary root hit only at the second mark adds p before division.
    extra = p if prescribed and pre2 == p and pre1 == 1 else 1
    step2 = kappa * determinant_part * extra // pre2
    first_output = Counter()
    conditional = defaultdict(Counter)
    smooth_at_first = unit_at_both = 0
    for u0, u1, u2 in product(range(0, modulus, p if prescribed else 1), range(modulus), range(modulus)):
        x = (b*b*u0 + a*b*u1 + a*a*u2) % modulus
        y = (d*d*u0 + c*d*u1 + c*c*u2) % modulus
        val1, val2 = f1 + multiplier1 * x, f2 + multiplier2 * y
        assert val1 % pre1 == val2 % pre2 == 0
        first_output[val1 // pre1 % output_mod1] += 1
        conditional[x][val2 // pre2 % output_mod2] += 1
        if val1 % p:
            smooth_at_first += 1
            unit_at_both += int(bool(val2 % p))

    def exact_class(counts, output_modulus, step):
        residue = next(iter(counts)) % step
        assert set(counts) == set(range(residue, output_modulus, step))
        assert len(set(counts.values())) == 1

    exact_class(first_output, output_mod1, step1)
    for counts in conditional.values():
        exact_class(counts, output_mod2, step2)
    if not special and not prescribed and determinant_part > 1:
        # This p is absent from the smooth band. Conditioning on a unit first
        # value boosts the unit probability at the second by p/(p-1).
        assert smooth_at_first * p == modulus**3 * (p - 1)
        assert unit_at_both == smooth_at_first
    return len(conditional), sum(len(counts) for counts in conditional.values())


if __name__ == '__main__':
    systems = first_fibers = second_values = 0
    for p in (3, 5):
        for first, second in projective_pairs(p):
            for special, prescribed in ((False, False), (False, True), (True, False)):
                fibers, values = check_case(p, first, second, special, prescribed)
                systems += 1
                first_fibers += fibers
                second_values += values
    print('local systems, first fibers, distinct conditional values:', systems, first_fibers, second_values)
