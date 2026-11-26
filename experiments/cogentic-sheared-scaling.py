"""Run the preregistered matcher scaling cases with fixed wall and query limits."""

import argparse
import json
from math import isfinite
from os import killpg
from pathlib import Path
from runpy import run_path
from signal import SIGKILL
from subprocess import PIPE, Popen, TimeoutExpired
import sys
from time import monotonic

HERE = Path(__file__).resolve().parent
SOLVER = HERE / "cogentic-sheared-local-squares.py"
INPUTS = tuple(json.loads((HERE / "cogentic-sheared-scaling-inputs.json").read_text()))
HEIGHT, CANDIDATES, SECONDS = 64, 32, 15


def attempt(n):
    start = monotonic()
    command = [sys.executable, "-B", str(SOLVER), str(n)]
    with Popen(command, stdout=PIPE, stderr=PIPE, text=True, start_new_session=True) as process:
        try:
            stdout, stderr = process.communicate(timeout=SECONDS)
            capped = False
        except TimeoutExpired:
            try:
                killpg(process.pid, SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = process.communicate()
            capped = True
    lines = stdout.split("\n")[:-1]
    record = json.loads(lines[-1]) if lines else dict(n=n, height=HEIGHT)
    if capped:
        record["status"] = "time-cap"
    elif process.returncode:
        record.update(status="process-error", error=stderr or str(process.returncode))
    assert record["n"] == n and record["height"] == HEIGHT
    assert record.get("attempts", 0) <= CANDIDATES
    return dict(record, bits=n.bit_length(), seconds=round(monotonic()-start, 3))


def run():
    implementation = run_path(str(SOLVER))
    assert (implementation["HEIGHT"], implementation["ATTEMPTS"], implementation["SECONDS"]) == (
        HEIGHT, CANDIDATES, SECONDS)
    for n in INPUTS:
        print(json.dumps(attempt(n)), flush=True)


def verify(path):
    labels = run_path(str(HERE / "cogentic-sheared-scaling-cohort.py"))["generate"]()
    implementation = run_path(str(SOLVER))
    require = implementation["require"]
    records = [json.loads(line) for line in path.read_text().splitlines()]
    require(tuple(record["n"] for record in records) == INPUTS == tuple(labels), "cohort changed")
    checked = 0
    for record in records:
        n, height, status = (record[key] for key in ("n", "height", "status"))
        require(height == HEIGHT and record["bits"] == n.bit_length(), f"{n}: incorrect case")
        require(isfinite(record["seconds"]) and 0 <= record["seconds"], f"{n}: invalid runtime")
        require(0 <= record.get("attempts", 0) <= CANDIDATES, f"{n}: invalid query count")
        require(status in ("complete-no-split", "square-split", "derivative-gcd", "query-cap",
                           "time-cap", "process-error"), f"{n}: unexpected status {status!r}")
        # Recompute the exact algebraic stages without the timed subprocess wrapper.
        repeated = json.loads(json.dumps(implementation["measure"](n, height)))
        keys = ("status", "fields", "local_dimensions", "rational_nullity", "identical_nullity", "attempts", "order")
        require(all(record.get(key) == repeated.get(key) for key in keys), f"{n}: exact repeat disagrees")
        if status == "derivative-gcd":
            require(record["divisor"] in labels[n], f"{n}: invalid derivative gcd")
        elif status == "square-split":
            admitted = set(implementation["field_candidates"](n))
            implementation["verify_certificate"](n, height, record["certificate"], admitted=admitted,
                                                  expected_factors=labels[n])
            checked += 1
        else:
            require("certificate" not in record, f"{n}: unexpected certificate")
        if status == "complete-no-split":
            require(record["attempts"] == record["rational_nullity"], f"{n}: basis not exhausted")
    print(f"Exactly replayed {len(labels)} public inputs and verified {checked} independent square certificates.")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", type=Path, help="independently verify saved results")
    args = parser.parse_args()
    if args.verify is None:
        run()
    else:
        verify(args.verify)
