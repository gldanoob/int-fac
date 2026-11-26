"""Compare conservative and all-ideal parity on the frozen monic inputs."""

import json
import subprocess
import sys
from math import gcd
from pathlib import Path
from runpy import run_path
from time import monotonic


HERE = Path(__file__).resolve().parent
BLIND = run_path(str(HERE / "cogentic-monic-blind-grid.py"))
DRIVER = BLIND["DRIVER"]
GRID = BLIND["GRID"]
SCHEDULED = run_path(str(HERE / "cogentic-monic-pair.py"))["scheduled_degree"]
HEIGHT, CASE_SECONDS, QUERIES = 32, 6, 3
CUTOFF = 2*HEIGHT**2


def parity(n, m, fields, marks, started, deadline):
    core, basis = GRID["parity_basis"]([rows for _, rows in marks])
    result = dict(columns=len(marks), rank=len(marks)-len(basis), nullity=len(basis),
                  collection_seconds=round(monotonic()-started, 3), queries=0, factors=[])
    if not basis:
        return dict(result, status="zero-parity")
    core_marks = [marks[j] for j in core]
    sign_bit, _, query = DRIVER["exact_oracle"](n, m, fields, core_marks,
                                               max(0, deadline-monotonic()), dyadic=True)
    support = [point for point, _ in core_marks]
    signed, _ = BLIND["PREFILTER"](fields, support, [sign_bit, *basis], prime_cutoff=BLIND["PROBE_CAP"])
    status, queries, _, squares = DRIVER["adaptive"](signed, query, QUERIES, n)
    factors = {gcd(left-right, n) for _, (left, right) in squares} - {1, n}
    assert all(n % divisor == 0 for divisor in factors)
    return dict(result, status=status, queries=queries, factors=sorted(factors))


def coverage(exact_module, conservative, complete, fields, primes):
    old, new = dict(conservative), dict(complete)
    shared = sorted(old.keys() & new.keys())
    added = sorted(new.keys()-old.keys())
    labels = exact_module["row_supports"]
    old_supports = labels([old[point] for point in shared])
    new_supports = labels([new[point] for point in shared])
    derivatives = [tuple(j*c for j, c in enumerate(field) if j) for field in fields]
    reasons = []
    for a, b in added:
        named, private = [], False
        for i, (field, derivative) in enumerate(zip(fields, derivatives, strict=True), 1):
            value = abs(GRID["homogeneous"](field, a, b))
            dvalue = GRID["homogeneous"](derivative, a, b)
            factors, tail = exact_module["bounded_parts"](value, primes)
            named.extend((i, p) for p, exponent in factors if p > 2 and exponent > 1 and dvalue % p == 0)
            private |= gcd(tail, dvalue) > 1
        reasons.append(dict(mark=[a, b], named_singular=named, private_singular=private,
                            odd_rows=len(new[a, b])))
    return dict(shared=len(shared), conservative_only=sorted(old.keys()-new.keys()),
                complete_only=reasons, shared_supports_removed=sum((old_supports-new_supports).values()),
                shared_supports_added=sum((new_supports-old_supports).values()))


def measure(n):
    deadline = monotonic() + CASE_SECONDS
    degree = SCHEDULED(n)
    m, f, g = GRID["CHECK_PAIR"](n, degree)
    repaired = DRIVER["REPAIR"](n, m, f, g)
    if isinstance(repaired, int):
        assert 1 < repaired < n and n % repaired == 0
        print(json.dumps(dict(n=n, status="derivative-gcd", divisor=repaired)), flush=True)
        return
    shift, fields = repaired
    started = monotonic()
    disc = int(DRIVER["gp_value"](f"poldisc(Polrev({list(fields[0])}))*poldisc(Polrev({list(fields[1])}))",
                                 max(0, deadline-monotonic())))
    primes = tuple(GRID["primes_through"](CUTOFF))
    conservative = [(point, small + large)
                    for point, small, large, _ in GRID["relations"](
                        n, m, fields, disc, primes, CUTOFF, True, height=HEIGHT,
                        include_ramified_two=True, mark_local=True)]
    result = dict(n=n, degree=degree, height=HEIGHT, cutoff=CUTOFF, m=m, shift=shift,
                  conservative=parity(n, m, fields, conservative, started, deadline))
    print(json.dumps(result), flush=True)

    exact_module = run_path(str(HERE / "cogentic-monic-exact-grid.py"))
    started = monotonic()
    complete = list(exact_module["collect"](n, m, fields, CUTOFF, height=HEIGHT))
    result["complete"] = parity(n, m, fields, complete, started, deadline)
    result["coverage"] = coverage(exact_module, conservative, complete, fields, primes)
    print(json.dumps(dict(result, status="measured")), flush=True)


def run():
    for n in BLIND["INPUTS"]:
        started = monotonic()
        command = [sys.executable, __file__, str(n)]
        try:
            process = subprocess.run(command, capture_output=True, text=True, timeout=CASE_SECONDS)
            lines = process.stdout.splitlines()
            status = "process-error" if process.returncode else "measured"
        except subprocess.TimeoutExpired as error:
            output = error.stdout or b""
            lines = output[:output.rfind(b"\n")+1].decode().splitlines()
            status = "time-cap"
        result = dict(n=n, degree=SCHEDULED(n), height=HEIGHT, cutoff=CUTOFF)
        if lines:
            result.update(json.loads(lines[-1]))
        if status == "measured":
            result.setdefault("status", "incomplete-output")
        else:
            result["status"] = status
        if status == "process-error":
            result["error"] = process.stderr.splitlines()[-1:] or [str(process.returncode)]
        result["wall_seconds"] = round(monotonic()-started, 3)
        print(json.dumps(result), flush=True)


if __name__ == "__main__":
    if len(sys.argv) > 1:
        measure(int(sys.argv[1]))
    else:
        run()
