"""Compare a frozen degree and height schedule on the ten blind monic inputs."""

import json
from math import gcd, prod
from pathlib import Path
from runpy import run_path
from subprocess import CalledProcessError, TimeoutExpired
from time import monotonic


HERE = Path(__file__).resolve().parent
BLIND = run_path(str(HERE / "cogentic-monic-blind-grid.py"))
DRIVER = BLIND["DRIVER"]
GRID = BLIND["GRID"]
COLLECT = run_path(str(HERE / "cogentic-monic-lattice-sieve.py"))["collect"]
SCHEDULED = run_path(str(HERE / "cogentic-monic-pair.py"))["scheduled_degree"]
PARITY_BASIS = GRID["parity_basis"]
PLAN = ((64, None), (64, 3), (64, 4), (128, None), (128, 3), (128, 4), (256, None))


def run_case(n, height, manual_degree):
    degree = SCHEDULED(n) if manual_degree is None else manual_degree
    cutoff = 2*height**2
    result = dict(n=n, height=height, cutoff=cutoff, degree=degree, automatic=manual_degree is None,
                  columns=None, parity_rank=None, parity_nullity=None, tests=0, factors=[])
    m, f, g = GRID["CHECK_PAIR"](n, degree)
    repaired = DRIVER["REPAIR"](n, m, f, g)
    if isinstance(repaired, int):
        assert 1 < repaired < n and n % repaired == 0
        return dict(result, status="derivative-gcd", divisor=repaired)
    shift, fields = repaired
    left, right = map(list, fields)
    try:
        disc = int(DRIVER["gp_value"](f"poldisc(Polrev({left}))*poldisc(Polrev({right}))",
                                     BLIND["CASE_SECONDS"]))
    except (TimeoutExpired, DRIVER["GPStackLimit"]) as error:
        return dict(result, status="discriminant-error", error=type(error).__name__)
    try:
        marks = COLLECT(n, m, fields, disc, cutoff, height=height,
                        include_ramified_two=True, mark_local=True)
    except (CalledProcessError, RuntimeError) as error:
        return dict(result, status="collection-error", error=type(error).__name__)
    columns = [small + large for _, small, large, _ in marks]
    core, basis = PARITY_BASIS(columns)
    result.update(m=m, shift=shift, columns=len(marks), parity_rank=len(marks)-len(basis),
                  parity_nullity=len(basis), core=len(core), smooth=sum(mark[3] for mark in marks))
    if height == PLAN[0][0]:
        full = GRID["parity_words"](columns)
        assert len(basis) == len(GRID["eliminate"](full, (1 << j for j in range(len(full)))))
    if not basis:
        return dict(result, status="zero-parity")
    core_marks = [marks[j] for j in core]
    sign_bit, decode, query = DRIVER["exact_oracle"](n, m, fields, core_marks, BLIND["CASE_SECONDS"])
    signed, probes = BLIND["PREFILTER"](fields, [mark[0] for mark in core_marks], [sign_bit, *basis], disc,
                                       prime_cutoff=BLIND["PROBE_CAP"])
    status, tests, rank, squares = DRIVER["adaptive"](signed, query, BLIND["QUERY_CAP"])
    if status == "complete":
        assert rank + len(squares) == len(signed)
    for word, (left, right) in squares:
        sign, points = decode(word)
        common = sign * prod(a-b*m for a, b in points) % n
        assert gcd(common, n) == 1 and left**2 % n == right**2 % n == common
        divisor = gcd(left-right, n)
        if 1 < divisor < n:
            assert n % divisor == 0
            result["factors"].append(dict(divisor=divisor, sign=sign, points=points, residues=[left, right]))
    return dict(result, status=status, probes=probes["probes"], surviving=len(signed),
                tests=tests, square_basis=len(squares))


if __name__ == "__main__":
    assert PARITY_BASIS([[1, 2], [1], [2], [3], []]) == ([0, 1, 2, 4], [7, 8])
    batches = []
    for height, degree in PLAN:
        cases = []
        for n in BLIND["INPUTS"]:
            start = monotonic()
            outcome = run_case(n, height, degree)
            outcome["seconds"] = round(monotonic()-start, 4)
            print(json.dumps(outcome), flush=True)
            cases.append(outcome)
        batches.append((height, cases))
    BLIND["validate"](batches)
