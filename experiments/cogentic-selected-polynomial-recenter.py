#!/usr/bin/env python3
"""Check deterministic small-discriminant pairs on two finite batches."""

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


def centered_pair(n):
    m = isqrt(n)
    r = n-m*m
    if r == 0:
        return None
    first_disc = -4*r
    for slope in (-1, -2):
        constant = r-slope*m
        second_disc = slope*slope-4*constant
        product = first_disc*second_disc
        if isqrt(product)**2 != product:
            return (0, slope), (r, constant), (first_disc, second_disc)
    raise AssertionError("the three slopes produced the same field")


def run(label, inputs):
    hits = 0
    for n in inputs:
        pair = centered_pair(n)
        if pair is None:
            print({"batch": label, "n": n, "admissible": False}, flush=True)
            continue
        slopes, constants, discs = pair
        slopes, offsets = list(slopes), list(constants)
        height, bound = split["RELATION_HEIGHT"], split["RELATION_BOUND"]
        scores = gp_call(f"rank_box_scores({n},{slopes},{offsets},[[[0,0]],[[0,0]]],{height},{bound})",
                         rank=True)
        targets, nullity, rank, columns = scores[0][0]
        certificate = gp_certificate(n, slopes, constants)
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
    assert centered_pair(2) == ((0, -1), (1, 2), (-4, -7))
    assert centered_pair(3) == ((0, -1), (2, 3), (-8, -11))
    assert centered_pair(9) is None  # square input
    assert centered_pair(88) == ((0, -2), (7, 25), (-28, -96))
    for n in range(2, 1024):
        m = isqrt(n)
        if n == m*m:
            continue
        slopes, constants, discs = centered_pair(n)
        assert all(0 < c <= 4*m and m*m+s*m+c == n for s, c in zip(slopes, constants))
        assert all(disc < 0 for disc in discs)
        product = discs[0]*discs[1]
        assert isqrt(product)**2 != product
    recovered = run("previous misses", MISSES)
    assert recovered == len(MISSES)
    run("fresh batch", FRESH)
