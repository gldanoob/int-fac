#!/usr/bin/env python3
"""Finite four-coefficient selection followed by an independent GP certificate."""

import json
import os
import runpy
import subprocess
from math import gcd, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parent
selection = runpy.run_path(str(ROOT / "cogentic-coefficient-selection.py"))
Factor, Smooth, select = (selection[name] for name in ("Factor", "Smooth", "select"))

# Fixed before running selection: small public composites, one box, mark range,
# smoothness bound, and relation-search limits. No factorization enters selection.
INPUTS = (77, 143, 221, 10001, 10203, 10403)
BAND_BOUND = 300
MARKS = range(1, 101)
BOX = ((0, 0, 4, 2), (0, 0, 4, 2))  # both u and v vary in each field
RELATION_HEIGHT = 250
RELATION_BOUND = 300


def base_polynomials(n):
    """Fixed rule: slopes near -n/2; least congruent constants above a slack floor."""
    m = isqrt(n)
    slopes = (-n // 2, -n // 2 + 3)
    constants = []
    for slope in slopes:
        max_square_floor = max((slope + n*v)**2 // 4 for v in (0, 1))
        floor = max_square_floor + BAND_BOUND
        residue = (-m*m - slope*m) % n
        constants.append(floor + (residue - floor) % n)
    return m, slopes, tuple(constants)


def selected_terms(n, m, slopes, constants):
    terms = []
    for a in MARKS:
        # The modular unit check is computable from n without factoring it.
        if gcd(a-m, n) != 1:
            continue
        first_offset = a*a + slopes[0]*a + constants[0]
        second_offset = a*a + slopes[1]*a + constants[1]
        terms.append((-1,
                      Factor((Smooth(a, first_offset, n),)),
                      Factor((Smooth(a, second_offset, n),))))
    return tuple(terms)


def gp_certificate(n, slopes, constants):
    call = (f"quadratic_certificate_coeffs({n},{list(slopes)},{list(constants)},"
            f"{RELATION_HEIGHT},{RELATION_BOUND})")
    code = ('cogentic_as_library=1;\n'
            'iferr(read("cogentic-quadratic-order.gp"),err,print(err);quit(1));\n'
            f'iferr(print({call}),err,print(err);quit(1));\n')
    result = subprocess.run([os.environ.get("GP", "gp"), "-fq", "-s", "64M"], input=code, cwd=ROOT,
                            capture_output=True, text=True, timeout=120)
    if result.returncode:
        raise RuntimeError(f"PARI failed: {result.stdout}{result.stderr}")
    certificate = json.loads(result.stdout)
    if certificate == []:
        return None
    if (not isinstance(certificate, list) or len(certificate) != 5
            or any(type(value) != int for value in certificate)):
        raise ValueError(f"Invalid certificate vector {certificate!r}")
    return tuple(certificate)


def band_squarefree(value, primes):
    """Each allowed prime can be removed once from the positive norm."""
    for p in primes:
        if value % p == 0:
            value //= p
    return value == 1


def split_chain(n, base, exponent):
    assert exponent > 0 and pow(base, exponent, n) == 1
    two_adic = (exponent & -exponent).bit_length() - 1
    residue = pow(base, exponent >> two_adic, n)
    chain = []
    for _ in range(two_adic + 1):
        divisor = gcd(residue - 1, n)
        chain.append(divisor)
        residue = residue * residue % n
    return chain


def check_certificate(n, certificate):
    if certificate is not None:
        base, exponent, divisor, _, _ = certificate
        assert 1 < divisor < n and n % divisor == 0
        assert divisor in split_chain(n, base, exponent)


def run():
    records = []
    band_primes = [p for p in selection["primes_through"](BAND_BOUND) if p > isqrt(BAND_BOUND)]
    assert all(width > 1 for field in BOX for width in field[2:])
    for n in INPUTS:
        m, base_slopes, base_constants = base_polynomials(n)
        terms = selected_terms(n, m, base_slopes, base_constants)
        point, score, trace = select(BAND_BOUND, BOX, terms)
        u1, v1, u2, v2 = point
        perturbations = ((u1, v1), (u2, v2))
        slopes = tuple(base_slopes[i] + n*perturbations[i][1] for i in range(2))
        constants = tuple(base_constants[i] + n*perturbations[i][0] for i in range(2))
        discs = tuple(slopes[i]**2 - 4*constants[i] for i in range(2))
        assert all(disc < 0 for disc in discs)
        assert all((m*m + slopes[i]*m + constants[i]) % n == 0 for i in range(2))

        retained = -score
        direct_marks = []
        for a in MARKS:
            if gcd(a-m, n) != 1:
                continue
            values = tuple(a*a + slopes[i]*a + constants[i] for i in range(2))
            if all(band_squarefree(value, band_primes) for value in values):
                direct_marks.append((a, values))
        assert len(direct_marks) == retained

        certificate = gp_certificate(n, slopes, constants)
        baseline = gp_certificate(n, base_slopes, base_constants) if any(point) else certificate
        check_certificate(n, certificate)
        check_certificate(n, baseline)
        records.append((n, point, retained, tuple(direct_marks), certificate, baseline, len(trace), discs))

    for n, point, retained, marks, certificate, baseline, decisions, discs in records:
        print({"n": n, "selected_(u1,v1,u2,v2)": point, "joint_marks": retained,
               "marks": marks, "discriminants": discs, "selector_decisions": decisions,
               "certificate": certificate, "unperturbed_certificate": baseline})
    successes = sum(record[4] is not None for record in records)
    unperturbed = sum(record[5] is not None for record in records)
    assert any(record[4] is not None and any(record[1]) for record in records)
    print(f"Verified splits on {len(records)} inputs: selected {successes}, unperturbed {unperturbed}")


if __name__ == "__main__":
    run()
