#!/usr/bin/env python3
"""Check one fixed small-discriminant pair on the six previous misses."""

from math import isqrt
from pathlib import Path
from runpy import run_path

split = run_path(str(Path(__file__).with_name("cogentic-selected-polynomial-split.py")))
gp_call = split["gp_call"]
gp_certificate = split["gp_certificate"]
check_certificate = split["check_certificate"]

# The larger half of each original batch, fixed before the replay.
INPUTS = split["INPUTS"][3:] + split["HOLDOUT"][3:]
SLOPES = (0, -1)


def run():
    hits = 0
    for n in INPUTS:
        m = isqrt(n)
        constants = tuple(n-m*m-slope*m for slope in SLOPES)
        discs = tuple(slope*slope-4*constant for slope, constant in zip(SLOPES, constants))
        assert all(disc < 0 for disc in discs)
        assert all(m*m+slope*m+constant == n for slope, constant in zip(SLOPES, constants))
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
        print({"n": n, "discriminants": discs, "targets": targets, "rank": rank,
               "columns": columns, "certificate": certificate}, flush=True)
    print(f"Verified splits with near-square polynomials: {hits}/{len(INPUTS)}")


if __name__ == "__main__":
    run()
