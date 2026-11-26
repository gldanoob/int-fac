#!/usr/bin/env python3
"""Compare finite rank scoring, smooth-mark selection and unperturbed controls."""

import json
import os
import runpy
import subprocess
from itertools import product
from math import gcd, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parent
selection = runpy.run_path(str(ROOT / "cogentic-coefficient-selection.py"))
Factor, Smooth, select = (selection[name] for name in ("Factor", "Smooth", "select"))

# Fixed before running selection: small public composites, one box, mark range,
# smoothness bound, and relation-search limits. No factorization enters selection.
INPUTS = (77, 143, 221, 10001, 10203, 10403)
HOLDOUT = (187, 299, 437, 11021, 11663, 12317)
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


def gp_call(call, *, rank=False):
    code = ('cogentic_as_library=1;\n'
            'iferr(read("cogentic-quadratic-order.gp"),err,print(err);quit(1));\n')
    if rank:
        code += 'iferr(read("cogentic-selected-polynomial-rank.gp"),err,print(err);quit(1));\n'
    code += f'iferr(print({call}),err,print(err);quit(1));\n'
    result = subprocess.run([os.environ.get("GP", "gp"), "-fq", "-s", "64M"], input=code, cwd=ROOT,
                            capture_output=True, text=True, timeout=120)
    if result.returncode or result.stderr:
        raise RuntimeError(f"PARI failed: {result.stdout}{result.stderr}")
    return json.loads(result.stdout)


def gp_certificate(n, slopes, constants):
    call = (f"quadratic_certificate_coeffs({n},{list(slopes)},{list(constants)},"
            f"{RELATION_HEIGHT},{RELATION_BOUND})")
    certificate = gp_call(call)
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


def rank_scores(n, slopes, constants):
    fields = [list(product(range(u, u+width), range(v, v+height)))
              for u, v, width, height in BOX]
    call = (f"rank_box_scores({n},{list(slopes)},{list(constants)},{json.dumps(fields)},"
            f"{RELATION_HEIGHT},{RELATION_BOUND})")
    scores = gp_call(call, rank=True)
    return {left+right: tuple(score) for left, row in zip(fields[0], scores, strict=True)
            for right, score in zip(fields[1], row, strict=True)}


def run(label, inputs):
    totals = [0, 0, 0]
    band_primes = [p for p in selection["primes_through"](BAND_BOUND) if p > isqrt(BAND_BOUND)]
    assert all(width > 1 for field in BOX for width in field[2:])
    for n in inputs:
        m, base_slopes, base_constants = base_polynomials(n)
        terms = selected_terms(n, m, base_slopes, base_constants)
        smooth_point, score, trace = select(BAND_BOUND, BOX, terms)
        scores = rank_scores(n, base_slopes, base_constants)
        # Maximize reachable rational-prime targets, then nullity, then rank.
        # The score is exact on this finite grid. Ties keep the first tuple.
        rank_point = max(scores, key=scores.__getitem__)
        variants = (("rank", rank_point), ("smooth", smooth_point), ("unperturbed", (0, 0, 0, 0)))
        certificates = {}
        for i, (method, point) in enumerate(variants):
            u1, v1, u2, v2 = point
            slopes = (base_slopes[0]+n*v1, base_slopes[1]+n*v2)
            constants = (base_constants[0]+n*u1, base_constants[1]+n*u2)
            discs = tuple(s*s-4*c for s, c in zip(slopes, constants))
            assert all(disc < 0 for disc in discs)
            assert all((m*m+s*m+c) % n == 0 for s, c in zip(slopes, constants))

            marks = []
            for a in MARKS:
                if gcd(a-m, n) != 1:
                    continue
                values = tuple(a*a+s*a+c for s, c in zip(slopes, constants))
                if all(band_squarefree(value, band_primes) for value in values):
                    marks.append((a, values))
            if method == "smooth":
                assert len(marks) == -score

            if point not in certificates:
                certificate = gp_certificate(n, slopes, constants)
                check_certificate(n, certificate)
                if certificate is not None:
                    assert certificate[3:] == (scores[point][3], scores[point][2])
                    assert scores[point][0] > 0
                certificates[point] = certificate
            certificate = certificates[point]
            totals[i] += certificate is not None
            print({"batch": label, "n": n, "method": method, "(u1,v1,u2,v2)": point,
                   "joint_marks": len(marks), "marks": marks, "discriminants": discs,
                   "selector_decisions": len(trace) if method == "smooth" else None,
                   "targets": scores[point][0], "nullity": scores[point][1],
                   "rank": scores[point][2], "columns": scores[point][3],
                   "certificate": certificate}, flush=True)
    print(f"Verified splits on {label} batch of {len(inputs)}: "
          f"rank {totals[0]}, smooth {totals[1]}, unperturbed {totals[2]}", flush=True)


if __name__ == "__main__":
    assert gp_call("check_rank_score()", rank=True) == 1
    run("original", INPUTS)
    run("holdout", HOLDOUT)
