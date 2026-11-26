#!/usr/bin/env python3
"""Check the 2.157 arithmetic conditional on public and private elliptic recognition."""

from pathlib import Path
from runpy import run_path


if __name__ == "__main__":
    check = run_path(str(Path(__file__).with_name("keybreak-private-elliptic-schedule.py")))["check_schedule"]
    check(
        field="1.3609 .8127 .66025 .5001 .7007",
        descent=".78 2.03 2.1718 .64094",
        recognition=".77644 .77644 .0001 2.157",
        period_bounds=".6408 .397",
        algebraic_exponent="1.4143",
    )
