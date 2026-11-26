"""Run the frozen fresh validation portfolio using public integers only."""

import argparse
import json
from math import gcd
from pathlib import Path
from runpy import run_path
from subprocess import CalledProcessError, TimeoutExpired
from time import monotonic

HERE = Path(__file__).resolve().parent
INPUTS = tuple(json.loads((HERE / "cogentic-monic-fresh-inputs.json").read_text()))
NEARBY = run_path(str(HERE / "cogentic-monic-nearby-bases.py"))
DRIVER, GRID = NEARBY["DRIVER"], NEARBY["GRID"]
SCHEDULED = run_path(str(HERE / "cogentic-monic-pair.py"))["scheduled_degree"]
MIXED = run_path(str(HERE / "cogentic-monic-mixed-grid.py"))["search"]
HEIGHT, CUTOFF, PROBES, PAIR_CAP, MIXED_CAP, EXACT_SECONDS = 256, 131072, 257, 3, 4, 5


def pair_trial(n, m, fields):
    repaired = DRIVER["REPAIR"](n, m, *fields)
    if isinstance(repaired, int):
        assert 1 < repaired < n and n % repaired == 0
    return repaired


def plan_shifts(n):
    m, _, _ = GRID["CHECK_PAIR"](n, 2)
    trials = []
    for j in (1, 2):
        base = m-2*j
        fields = NEARBY["shifted_pair"](n, base)
        fixed = pair_trial(n, base, fields)
        score = NEARBY["local_score"](n, base, fields if isinstance(fixed, int) else fixed[1])
        trials.append((j, base, fixed, score))
    return sorted(trials, key=lambda trial: (-trial[3], trial[0]))


def raw(n):
    degree = SCHEDULED(n)
    assert degree == 2
    m, f, g = GRID["CHECK_PAIR"](n, degree)
    fixed = pair_trial(n, m, (f, g))
    if isinstance(fixed, int):
        return dict(n=n, m=m, status="derivative-gcd", divisor=fixed, tests=0, factors=[])
    shift, fields = fixed
    result = DRIVER["replay"](n, m, shift, fields, None, CUTOFF, height=HEIGHT,
                              query_cap=PAIR_CAP, time_cap=EXACT_SECONDS, ramified_two=True,
                              mark_local=True, probe_cutoff=PROBES, stop_at_factor=True)
    return dict(result, fields=fields)


def mixed(n):
    result = MIXED(n, HEIGHT, query_cap=MIXED_CAP, time_cap=EXACT_SECONDS)
    certificate = result.pop("certificate", None)
    if certificate:
        ratio, divisor = certificate["ratio"], certificate["divisor"]
        assert ratio*ratio % n == 1 and divisor == gcd(ratio-1, n) and 1 < divisor < n
    return dict(result, factors=[certificate] if certificate else [])


def measure(n, stage, run, *args):
    start = monotonic()
    try:
        result = run(n, *args)
    except (CalledProcessError, RuntimeError, TimeoutExpired, DRIVER["GPStackLimit"]) as error:
        result = dict(n=n, status="error", error=type(error).__name__, factors=[])
    return dict(result, stage=stage, elapsed=round(monotonic()-start, 4))


def log(record):
    print(json.dumps(record), flush=True)


def run():
    plans = {n: plan_shifts(n) for n in INPUTS}
    unresolved = set(INPUTS)
    for n in INPUTS:
        result = measure(n, "raw", raw)
        log(result)
        if result["factors"]:
            unresolved.remove(n)
    for n in INPUTS:
        if n not in unresolved:
            log(dict(n=n, stage="nearby", status="skipped-after-square", factors=[]))
            continue
        budget = PAIR_CAP
        for trial in plans[n]:
            if n not in unresolved or not budget:
                log(dict(n=n, j=trial[0], stage="nearby", status="skipped-after-square" if n not in unresolved
                         else "skipped-after-budget", factors=[]))
                continue
            result = measure(n, "nearby", NEARBY["measure"], trial, budget)
            charged = (budget if result["status"] == "error" else
                       result.get("tests", 0) + (result["status"] in ("time-cap", "stack-cap")))
            assert charged <= budget
            budget -= charged
            log(dict(result, charged_queries=charged))
            if result["factors"]:
                unresolved.remove(n)
    for n in INPUTS:
        if n not in unresolved:
            log(dict(n=n, stage="mixed", status="skipped-after-square", factors=[]))
            continue
        log(measure(n, "mixed", mixed))


def verify_saved(path):
    results = [json.loads(line) for line in path.read_text().splitlines()]
    pair_rows = [row for row in results if row["stage"] in ("raw", "nearby") and row["factors"]]
    pair_count = NEARBY["confirm_certificates"](pair_rows)
    mixed_checker = run_path(str(HERE / "cogentic-monic-mixed-certificate-check.py"))["verify"]
    gp_check = run_path(str(HERE / "cogentic-monic-degree-certificate-check.py"))["GP_CHECK"]
    pair = run_path(str(HERE / "cogentic-monic-pair.py"))
    mixed_count = 0
    for row in results:
        if row["stage"] == "mixed":
            for certificate in row["factors"]:
                mixed_checker(certificate, pair, GRID["gp"], gp_check)
                mixed_count += 1
    print(json.dumps(dict(independent_pair_certificates=pair_count, independent_mixed_certificates=mixed_count)))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", type=Path, help="independently verify saved certificates")
    args = parser.parse_args()
    if args.verify:
        verify_saved(args.verify)
    else:
        run()
