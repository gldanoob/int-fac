#!/usr/bin/env python3
"""Check one fixed small-discriminant pair on two finite batches."""

from math import isqrt
from pathlib import Path
from runpy import run_path

split = run_path(str(Path(__file__).with_name("cogentic-selected-polynomial-split.py")))
gp_call = split["gp_call"]
gp_certificate = split["gp_certificate"]
check_certificate = split["check_certificate"]

# The larger half of each original batch, fixed before the replay.
MISSES = split["INPUTS"][3:] + split["HOLDOUT"][3:]
# Three close-factor fixtures and three with wider separation.
FRESH = (16637, 24511, 19043, 34387, 23707, 49981)
SLOPES = (0, -1)


def centered_pair(n):
    m = isqrt(n)
    constants = tuple(n-m*m-slope*m for slope in SLOPES)
    discs = tuple(slope*slope-4*constant for slope, constant in zip(SLOPES, constants))
    if not all(disc < 0 for disc in discs):
        return None
    product = discs[0]*discs[1]
    if isqrt(product)**2 == product:
        return None
    assert all(m*m+slope*m+constant == n for slope, constant in zip(SLOPES, constants))
    return constants, discs


def run(label, inputs):
    hits = 0
    for n in inputs:
        pair = centered_pair(n)
        if pair is None:
            print({"batch": label, "n": n, "admissible": False}, flush=True)
            continue
        constants, discs = pair
        slopes, offsets = list(SLOPES), list(constants)
        height, bound = split["RELATION_HEIGHT"], split["RELATION_BOUND"]
        scores = gp_call(f"rank_box_scores({n},{slopes},{offsets},[[[0,0]],[[0,0]]],{height},{bound})",
                         rank=True)
        targets, nullity, rank, columns = scores[0][0]
        certificate = gp_certificate(n, SLOPES, constants)
        check_certificate(n, certificate)
        assert nullity == columns-rank
        if certificate is not None:
            assert targets > 0 and certificate[3:] == (columns, rank)
            hits += 1
        print({"batch": label, "n": n, "discriminants": discs, "targets": targets, "rank": rank,
               "columns": columns, "certificate": certificate}, flush=True)
    print(f"Verified splits on {label}: {hits}/{len(inputs)}", flush=True)
    return hits


if __name__ == "__main__":
    assert centered_pair(9) is None  # square input
    assert centered_pair(88) is None  # equal quadratic fields
    recovered = run("previous misses", MISSES)
    assert recovered == len(MISSES)
    run("fresh batch", FRESH)
