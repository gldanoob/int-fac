#!/usr/bin/env python3
"""Replay the single-input schedule using a sparse verified dependency."""

from pathlib import Path
from runpy import run_path


if __name__ == "__main__":
    check = run_path(str(Path(__file__).with_name("keybreak-private-elliptic-schedule.py")))["check_schedule"]
    check(
        field="1.36245 .79414 .667731 .500005 .684287",
        descent=".78 1.97 2.149294 .644358",
        recognition=".785005 .785005 .000005 2.155",
        period_bounds=".64435 .39541",
        algebraic_exponent="1.4143",
        stages=1024, first_knot=".026", first_floor=".00067",
        minimum_mean=".00002", matrix_exponent="2",
    )
    check(
        field="1.36252275 .79425931 .667753188 .5000001 .68410920",
        descent=".78 1.97 2.1488529 .64421050",
        recognition=".78487843 .78487843 .0000002 2.15468",
        period_bounds=".64421039 .39533814",
        algebraic_exponent="1.414217", private_exponent="1.414217",
        stages=3072, first_knot=".022", first_floor=".000479",
        minimum_mean=".0000003", matrix_exponent="2",
    )
    # The final grid checks every asymptotic band. Integer replay sizes for the
    # coarser grids precede the separation threshold for these narrower bands.
    check(
        field="1.36252214 .79430825 .66779525506 .500000001 .68401159399",
        descent=".78 1.97 2.14867235968 .6441958804",
        recognition=".7848525113 .7848525113 .000000002 2.154631",
        period_bounds=".6441958793 .3953386693",
        algebraic_exponent="1.41421357", private_exponent="1.41421357",
        stages=262144, first_knot=".002", first_floor=".00000399",
        minimum_mean=".000000003", matrix_exponent="2", rounded_exponents=(),
    )
