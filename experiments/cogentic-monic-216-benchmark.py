"""Measure the frozen degree-three boundary cohort using only public integers."""

import argparse
import json
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path
from time import monotonic

HERE = Path(__file__).resolve().parent
INPUTS = tuple(json.loads((HERE / "cogentic-monic-216-inputs.json").read_text()))
GRID = run_path(str(HERE / "cogentic-monic-large-primes.py"))
PAIR = run_path(str(HERE / "cogentic-monic-pair.py"))
COLLECT = run_path(str(HERE / "cogentic-monic-lattice-sieve.py"))["collect"]
SPARSE = run_path(str(HERE / "cogentic-short-field-list.py"))
HEIGHTS = (64, 128)


def factor_count_floor(value, cutoff):
    count, power = 0, 1
    while power < value:
        power *= cutoff
        count += 1
    return count


def residual(value, primes):
    value = abs(value)
    for p in primes:
        while value % p == 0:
            value //= p
    return value


def raw(n, height):
    assert n.bit_length() == 216 and PAIR["scheduled_degree"](n) == 3
    m, f, g = PAIR["check_pair"](n, 3)
    fields = [list(f), list(g)]
    line, = GRID["gp"](f"print(apply(poldisc,apply(Polrev,{fields})));\n")
    discs = json.loads(line)
    cutoff = 2*height**2
    marks = [COLLECT(n, m, (field,), disc, cutoff, height=height,
                     include_ramified_two=True, mark_local=True)
             for field, disc in zip(fields, discs, strict=True)]
    tables = [{point: (small+large, smooth) for point, small, large, smooth in side} for side in marks]
    common = sorted(tables[0].keys() & tables[1].keys())
    rows = [[(i, p, r) for i, table in enumerate(tables) for _, p, r in table[point][0]]
            for point in common]
    core, basis = GRID["parity_basis"](rows)
    count = sum(gcd(a, b) == gcd(a-b*m, n) == 1
                for a in range(-height, height+1) for b in range(1, height+1))
    floor = (m-height+1)//2
    primes = tuple(GRID["primes_through"](cutoff))
    witnesses = []
    for i, side in enumerate(tables):
        for point, (odd_rows, _) in side.items():
            norms = [GRID["homogeneous"](field, *point) for field in fields]
            tails = [residual(value, primes) for value in norms]
            assert isqrt(tails[i])**2 == tails[i]
            witnesses.append(dict(point=point, field=i, norms=norms, tails=tails, odd_rows=odd_rows))
    return dict(n=n, mode="raw", height=height, degree=[3, 4], m=m, cutoff=cutoff,
                fields=fields, discriminants=discs, primitive_unit=count,
                accepted=list(map(len, marks)), smooth=[sum(row[3] for row in side) for side in marks],
                joint=len(common), joint_smooth=sum(all(side[point][1] for side in tables) for point in common),
                core=len(core), rank=len(common)-len(basis), nullity=len(basis), witnesses=witnesses,
                nonzero_numerator_factor_floor=[factor_count_floor(floor, bound) for bound in (151, cutoff)])


def planted(n):
    fixture = SPARSE["build"](n, 3, 1)
    if isinstance(fixture, int):
        assert 1 < fixture < n and n % fixture == 0
        return dict(n=n, mode="planted", status="construction-gcd", divisor=fixture)
    m, fields, cuts, primes, norms, bound = fixture
    assert cuts == (0,) and len(primes) == 1 and gcd(m, n) == 1
    p, = primes
    fs = [SPARSE["squarefree_factors"](side[0]) for side in norms]
    assert all(factors and prod(factors) == norms[i][0] <= bound for i, factors in enumerate(fs))
    assert p in fs[0] and p not in fs[1]
    assert fields[0][0] % p == 0 and fields[0][1] % p != 0
    assert all(SPARSE["evaluate"](field, m) % n == 0 for field in fields)
    return dict(n=n, mode="planted", degree=[len(f)-1 for f in fields], m=m, status="private-row",
                field_row=[0, p, 0], norms=[side[0] for side in norms], factors=fs, rank_at_least=1)


def records():
    assert PAIR["scheduled_degree"]((1 << 215)-1) == 2
    assert PAIR["scheduled_degree"](1 << 215) == 3
    for height in HEIGHTS:
        for n in INPUTS:
            start = monotonic()
            result = raw(n, height)
            yield dict(result, seconds=round(monotonic()-start, 4))
    for n in INPUTS:
        yield planted(n)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", type=Path, help="recompute every saved row except elapsed time")
    args = parser.parse_args()
    if args.verify:
        saved = [json.loads(line) for line in args.verify.read_text().splitlines()]
        for expected, observed in zip(saved, records(), strict=True):
            expected.pop("seconds", None)
            observed.pop("seconds", None)
            if expected != json.loads(json.dumps(observed)):
                raise ValueError(f"frozen result differs for {observed['n']} in {observed['mode']} mode")
        print(f"Verified {len(saved)} frozen 216-bit grid and planting records")
    else:
        for row in records():
            print(json.dumps(row), flush=True)
