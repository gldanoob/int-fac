"""Construct short adaptive intercept lists for prescribed marked values."""

from fractions import Fraction
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


PRIMES_THROUGH = run_path(str(Path(__file__).with_name("cogentic-coefficient-selection.py")))["primes_through"]
BOUND = 1009
WIDTH = 1 << 40
INPUTS = (77, 143, 221, 187, 299, 437)


def reserve(length, forbidden):
    return 4 * (len(forbidden) + length.bit_length() + 1)


def anchored_candidates(start, step, length, band, forbidden):
    """Return the tested list size, forced primes, and accepted indices."""
    assert gcd(start, step) == 1
    attempts = reserve(length, forbidden)
    anchor, index = 1, 0
    chosen = []
    for p in reversed(band):
        if step % p == 0:
            continue
        if anchor * p > length // attempts:
            break
        residue = -start * pow(step, -1, p) % p
        index += anchor * ((residue - index) * pow(anchor, -1, p) % p)
        anchor *= p
        chosen.append(p)
    else:
        raise ValueError("eligible prime list exhausted before reaching the anchor budget")
    assert length // (attempts * max(band)) <= anchor <= length // attempts
    assert (start + step * index) % anchor == 0
    residual = (start + step * index) // anchor
    screened = (*chosen, *forbidden)
    assert sum(Fraction(1, p) for p in screened) + Fraction(len(screened), attempts) <= Fraction(1, 2)
    check = prod(screened)
    accepted = []
    for j in range(attempts):
        t = index + anchor * j
        value = residual + step * j
        assert 0 <= t < length and anchor * value == start + step * t
        if gcd(value, check) == 1:
            accepted.append((t, value))
    assert len(accepted) * 2 >= attempts
    return attempts, tuple(chosen), accepted


def squarefree_smooth(value, eligible):
    value = abs(value)
    for p in eligible:
        if value == 1:
            break
        if value % p == 0:
            value //= p
    return value == 1


def two_mark_shift(a, b, z, w, modulus=1):
    return modulus * (b*z-a*w), modulus * (w-z)


def main():
    primes = tuple(PRIMES_THROUGH(BOUND))
    band = tuple(p for p in primes if p > isqrt(BOUND))
    top = tuple(p for p in band if 2*p > BOUND)
    forbidden = tuple(p for p in primes if 11 <= p < isqrt(BOUND))
    z, w = -17, 43
    for a, b in ((1, 2), (29, 37), (42, 48)):
        u, v = two_mark_shift(a, b, z, w, modulus=35)
        assert u % 35 == v % 35 == 0
        assert u+a*v == 35*(b-a)*z and u+b*v == 35*(b-a)*w

    def exact_hits(start, step):
        attempts, chosen, candidates = anchored_candidates(start, step, WIDTH, top, forbidden)
        full_anchor = prod(chosen)
        eligible = tuple(p for p in band if p not in chosen)
        hits = [j for j, residue in candidates if squarefree_smooth(residue, eligible)]
        assert all(squarefree_smooth(start + step*j, band) and (start + step*j) % full_anchor == 0
                   for j in hits)
        return attempts, hits

    total_adaptive = total_fixed = total_stratified = total_marks = 0
    total_chart = total_pairs = 0
    print("N, marks, adaptive, fixed prefix, fixed strata, adaptive trials, pairs, joint pairs")
    for n in INPUTS:
        m = isqrt(n)
        residual = n - m*m
        polynomials = ((0, residual), (-1, residual+m))
        adaptive = fixed = stratified = marks = attempts_total = pairs = chart = 0
        admissible = set()
        for a in range(m+1, m+17):
            step = n * (a-m)
            starts = [a*a+slope*a+constant+step*WIDTH for slope, constant in polynomials]
            if any(gcd(start, step) != 1 for start in starts):
                continue
            admissible.add(a)
            marks += 1
            field_hits = []
            fixed_hits = []
            strata_hits = []
            for start in starts:
                attempts, hits = exact_hits(start, step)
                field_hits.append(bool(hits))
                fixed_hits.append(any(squarefree_smooth(start + step*j, band) for j in range(attempts)))
                strata_hits.append(any(squarefree_smooth(start + step*(j*WIDTH//attempts), band)
                                       for j in range(attempts)))
                attempts_total += attempts
            adaptive += all(field_hits)
            fixed += all(fixed_hits)
            stratified += all(strata_hits)
        for a in sorted(admissible):
            b = a + 1
            if b not in admissible:
                continue
            pairs += 1
            hits = []
            for slope, constant in polynomials:
                u0 = (m+16)*WIDTH
                a_data = exact_hits(a*a+slope*a+constant+n*(a-m)*u0, n*(a-m))[1]
                b_data = exact_hits(b*b+slope*b+constant+n*(b-m)*u0, n*(b-m))[1]
                hits.append(bool(a_data and b_data))
                if a_data and b_data:
                    u, v = two_mark_shift(a, b, a_data[0], b_data[0])
                    assert all(squarefree_smooth(x*x+slope*x+constant+n*(x-m)*(u0+u+v*x), band)
                               for x in (a, b))
            chart += all(hits)
        total_adaptive += adaptive
        total_fixed += fixed
        total_stratified += stratified
        total_marks += marks
        total_chart += chart
        total_pairs += pairs
        print(n, marks, adaptive, fixed, stratified, attempts_total, pairs, chart)
    assert (total_marks, total_adaptive, total_fixed) == (68, 65, 0)
    assert total_chart > 0
    print(f"Joint smooth witnesses on {total_marks} marks: adaptive {total_adaptive}, "
          f"fixed prefix {total_fixed}, fixed strata {total_stratified}")
    print(f"Joint smooth witnesses on {total_chart}/{total_pairs} pairs via a common shift in each field")


if __name__ == "__main__":
    main()
