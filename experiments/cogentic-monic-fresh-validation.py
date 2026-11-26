"""Run the fixed monic portfolio on one integer or replay its frozen validation."""

import argparse
import json
from math import gcd
from pathlib import Path
from runpy import run_path
from subprocess import CalledProcessError, TimeoutExpired
from time import monotonic

HERE = Path(__file__).resolve().parent
NEARBY = run_path(str(HERE / "cogentic-monic-nearby-bases.py"))
DRIVER, GRID = NEARBY["DRIVER"], NEARBY["GRID"]
PAIR = run_path(str(HERE / "cogentic-monic-pair.py"))
SCHEDULED = PAIR["scheduled_degree"]
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
        if base < 3:
            continue
        fields = NEARBY["shifted_pair"](n, base)
        fixed = pair_trial(n, base, fields)
        score = NEARBY["local_score"](n, base, fields if isinstance(fixed, int) else fixed[1])
        trials.append((j, base, fixed, score))
    return sorted(trials, key=lambda trial: (-trial[3], trial[0]))


def raw(n):
    degree = SCHEDULED(n)
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


def nearby_attempt(n, trial, budget):
    result = measure(n, "nearby", NEARBY["measure"], trial, budget)
    charged = (budget if result["status"] == "error" else
               result.get("tests", 0) + (result["status"] in ("time-cap", "stack-cap")))
    assert charged <= budget
    return dict(result, charged_queries=charged)


def ordinary_result(result):
    n = result["n"]
    candidates = [result["divisor"]] if "divisor" in result else []
    candidates.extend(g for g in result.get("derivative_gcds", ()) if 1 < g < n)
    if candidates:
        assert all(1 < g < n and n % g == 0 for g in candidates)
        result = dict(result, divisor=candidates[0], cofactor=n//candidates[0])
    assert all(1 < cert["divisor"] < n and n % cert["divisor"] == 0 for cert in result["factors"])
    log(result)
    return bool(candidates or result["factors"])


def run_single(n):
    if n in (2, 3, 5, 7):
        log(dict(n=n, stage="precheck", status="prime", factors=[]))
        return
    if n % 2 == 0:
        ordinary_result(dict(n=n, stage="precheck", status="even", divisor=2, factors=[]))
        return
    divisor = PAIR["perfect_power_divisor"](n)
    if divisor is not None:
        ordinary_result(dict(n=n, stage="precheck", status="perfect-power", divisor=divisor, factors=[]))
        return
    degree = SCHEDULED(n)
    if ordinary_result(dict(measure(n, "raw", raw), degree=degree)):
        return
    plans = plan_shifts(n) if degree == 2 else []
    if not plans:
        reason = "scheduled-degree" if degree != 2 else "no-odd-base-at-least-three"
        log(dict(n=n, stage="nearby", status="skipped", reason=reason, factors=[]))
    budget = PAIR_CAP
    for trial in plans:
        result = nearby_attempt(n, trial, budget)
        budget -= result["charged_queries"]
        if ordinary_result(result):
            return
        if not budget:
            break
    if not ordinary_result(measure(n, "mixed", mixed)):
        log(dict(n=n, stage="portfolio", status="exhausted", factors=[]))


def run():
    inputs = tuple(json.loads((HERE / "cogentic-monic-fresh-inputs.json").read_text()))
    plans = {n: plan_shifts(n) for n in inputs}
    unresolved = set(inputs)
    for n in inputs:
        result = measure(n, "raw", raw)
        log(result)
        if result["factors"]:
            unresolved.remove(n)
    for n in inputs:
        if n not in unresolved:
            log(dict(n=n, stage="nearby", status="skipped-after-square", factors=[]))
            continue
        budget = PAIR_CAP
        for trial in plans[n]:
            if n not in unresolved or not budget:
                log(dict(n=n, j=trial[0], stage="nearby", status="skipped-after-square" if n not in unresolved
                         else "skipped-after-budget", factors=[]))
                continue
            result = nearby_attempt(n, trial, budget)
            budget -= result["charged_queries"]
            log(result)
            if result["factors"]:
                unresolved.remove(n)
    for n in inputs:
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
    parser.add_argument("n", nargs="?", type=int, help="public integer for a single search")
    parser.add_argument("--verify", type=Path, help="independently verify saved certificates")
    args = parser.parse_args()
    if args.n is not None:
        if args.n < 2 or args.verify:
            parser.error("provide N >= 2 without --verify")
        run_single(args.n)
    elif args.verify:
        verify_saved(args.verify)
    else:
        run()
