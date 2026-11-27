#!/usr/bin/env python3
"""Cost target assuming a cheap public pool with the specified residual rank."""

from pathlib import Path
from runpy import run_path


if __name__ == "__main__":
    check = run_path(str(Path(__file__).with_name("keybreak-private-elliptic-schedule.py")))["check_schedule"]
    check(
        field="1.36096005 .71163161 .70597223 .500005 .62385228",
        descent=".63 1.88 2.08060323 .67543306",
        recognition=".82966951 .82966951 .0000004 1.922",
        period_bounds=".675430 .396702",
        algebraic_exponent="1.414217", private_exponent="1.414217",
        stages=1024, first_knot=".026", first_floor=".00067",
        minimum_mean=".000004", matrix_exponent="2", row_exponent=".720",
    )
