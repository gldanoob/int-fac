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
