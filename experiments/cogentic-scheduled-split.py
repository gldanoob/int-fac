"""Replay exact splitting on one fixed automatic-schedule holdout."""

import os
import runpy
import subprocess
from pathlib import Path


def run():
    directory = Path(__file__).resolve().parent
    constructor = runpy.run_path(str(directory / "cogentic-monic-pair.py"))
    repair = runpy.run_path(str(directory / "cogentic-monic-index.py"))["repair"]
    cases = [
        'cogentic_as_library=1;',
        'read("cogentic-quadratic-order.gp");',
        'read("cogentic-monic-pair-relations.gp");',
        'read("cogentic-monic-unit-corrections.gp");',
        'read("cogentic-scheduled-split.gp");',
    ]
    for n in (187, 209, 247, 299, 391, 437, 10403):
        degree = constructor["scheduled_degree"](n)
        m, f, g = constructor["check_pair"](n, degree)
        fixed = repair(n, m, f, g)
        if isinstance(fixed, int):
            assert 1 < fixed < n and n % fixed == 0
            cases.append(f'print([{n},{degree},{m},"derivative",{fixed}]);')
            continue
        t, pair = fixed
        cases.append(f"iferr(print(scheduled_split({n},{degree},{m},{t},"
                     f"{[list(p) for p in pair]})),err,print(err);quit(1));")
    result = subprocess.run([os.environ.get("GP", "gp"), "-fq"], input="\n".join(cases) + "\n",
                            cwd=directory, capture_output=True, text=True, timeout=15, check=True)
    if result.stderr:
        raise RuntimeError(result.stderr)
    print(result.stdout, end="")


if __name__ == "__main__":
    run()
