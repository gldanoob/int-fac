"""Test the frozen integer-lift rule on the three 40-bit scaling inputs."""

import argparse
from collections import Counter
import json
from math import gcd, isfinite, isqrt, prod
from os import killpg
from pathlib import Path
from runpy import run_path
from signal import SIGKILL
from subprocess import PIPE, Popen, TimeoutExpired
import sys
from time import monotonic

HERE = Path(__file__).resolve().parent
SHEARED = run_path(str(HERE / "cogentic-sheared-local-squares.py"))
GRID, SQUARES = SHEARED["GRID"], SHEARED["SQUARES"]
INPUTS = tuple(json.loads((HERE / "cogentic-sheared-scaling-inputs.json").read_text())[:3])
HEIGHT, ATTEMPTS, SECONDS = 64, 32, 15
PRIMES = tuple(GRID["primes_through"](251))
OFFSETS = (0, *(sign*k for k in range(1, 129) for sign in (1, -1)))


def smooth_row(value):
    row, value = int(value < 0), abs(value)
    if not value:
        return None
    for i, p in enumerate(PRIMES, 1):
        while value % p == 0:
            row ^= 1 << i
            value //= p
        if value == 1:
            return row
    return None


def prepare(n):
    local, generators = [], []
    for m, field in SHEARED["field_candidates"](n):
        assert gcd(2*m+field[1], n) == 1
        points = [(a, b) for a in range(-HEIGHT, HEIGHT+1) for b in range(1, HEIGHT+1)
                  if gcd(a, b) == gcd(a-b*m, n) == 1]
        basis = SHEARED["SUPPORTED"]["grid_square_masks"](field, points, HEIGHT, packed_roots=True)
        values = [a-b*m for a, b in points]+[-1]
        generators.extend((len(local), word) for word in basis)
        local.append(dict(m=m, field=field, points=points, values=values, basis=basis))
    return local, generators


def lift_generators(n, local, generators):
    admitted, rows = [], []
    for j, (i, word) in enumerate(generators):
        residue = prod(local[i]["values"][k] % n for k in GRID["support"](word)) % n
        centered = residue if residue <= n//2 else residue-n
        assert gcd(centered, n) == 1
        for k in OFFSETS:
            label = centered+k*n
            row = smooth_row(label)
            if row is not None:
                admitted.append((j, label))
                rows.append(row)
                break
    return admitted, rows


def field_parts(n, local, generators, selected):
    multiplicities = [Counter() for _ in local]
    for j in selected:
        i, word = generators[j]
        multiplicities[i].update(GRID["support"](word))
    for entry, counts in zip(local, multiplicities, strict=True):
        if not counts:
            continue
        m, field, marks = entry["m"], entry["field"], entry["points"]
        sign = -1 if counts[len(marks)] % 2 else 1
        points = [marks[j] for j, count in sorted(counts.items()) if j < len(marks) and count % 2]
        correction = prod(pow(entry["values"][j], count//2, n) for j, count in counts.items()) % n
        yield m, field, sign, points, correction


def certified_root(n, m, field, sign, points):
    value = [sign, 0]
    for a, b in points:
        value = SQUARES["multiply_mark"](field, value, a, b)
    root = SHEARED["MIXED"]["quadratic_numerator"](field, value)
    assert root is not None
    residue = SQUARES["evaluate"](root, m)*pow(2*m+field[1], -1, n) % n
    assert residue**2 % n == sign*prod((a-b*m) % n for a, b in points) % n
    return residue


def candidate(n, local, generators, lifts, witnesses, word):
    chosen = list(GRID["support"](word))
    selected = [lifts[k] for k in chosen if k < len(lifts)]
    public = [witnesses[k-len(lifts)] for k in chosen if k >= len(lifts)]
    label_product = prod(label for _, label in selected)*prod(label for label, _ in public)
    scale = isqrt(label_product)
    assert scale**2 == label_product and gcd(scale, n) == 1
    roots = []
    for m, field, sign, points, correction in field_parts(n, local, generators, [j for j, _ in selected]):
        root = certified_root(n, m, field, sign, points)
        roots.append(dict(m=m, field=field, sign=sign, points=points, correction=correction, residue=root))
    product = prod(part["correction"]*part["residue"] % n for part in roots)*prod(root for _, root in public) % n
    ratio = product*pow(scale, -1, n) % n
    assert ratio*ratio % n == 1
    divisor = gcd(ratio-1, n)
    if 1 < divisor < n:
        source = [dict(field=generators[j][0], mask=hex(generators[j][1]), label=label)
                  for j, label in selected]
        return dict(divisor=divisor, cofactor=n//divisor, ratio=ratio, normalization=scale % n,
                    selected=source, fields=roots, public=public)
    return None


def basis(rows):
    return GRID["eliminate"](rows, (1 << j for j in range(len(rows))))


def measure(n):
    local, generators = prepare(n)
    exact, identical = SHEARED["evaluation_rows"](local, HEIGHT, 2)
    lifts, rows = lift_generators(n, local, generators)
    lift_basis = basis(rows)
    result = dict(n=n, dimensions=[len(field["basis"]) for field in local],
                  original_nullity=len(basis(exact)), identical_nullity=len(basis(identical)), retained=len(lifts),
                  original_retained_nullity=len(basis([exact[j] for j, _ in lifts])), lift_nullity=len(lift_basis),
                  attempts=0)
    print(json.dumps(dict(result, status="prepared")), flush=True)
    for word in lift_basis[:ATTEMPTS]:
        certificate = candidate(n, local, generators, lifts, (), word)
        result["attempts"] += 1
        if certificate:
            return dict(result, status="lift-split", certificate=certificate)
    if result["attempts"] == ATTEMPTS:
        return dict(result, status="lift-query-cap")

    public, public_rows = [], []
    for u in range(isqrt(n-1)+1, isqrt(n-1)+65):
        g = gcd(u, n)
        if 1 < g < n:
            return dict(result, status="public-gcd", divisor=g)
        label = u*u-n
        row = smooth_row(label)
        if g == 1 and row is not None:
            public.append((label, u))
            public_rows.append(row)
    extended = basis(rows+public_rows)
    assert extended[:len(lift_basis)] == lift_basis
    result.update(public=len(public), extended_nullity=len(extended))
    print(json.dumps(dict(result, status="public-prepared")), flush=True)
    for word in extended[len(lift_basis):ATTEMPTS]:
        certificate = candidate(n, local, generators, lifts, public, word)
        result["attempts"] += 1
        if certificate:
            return dict(result, status="public-split", certificate=certificate)
    return dict(result, status="public-query-cap" if result["attempts"] < len(extended) else "exhausted")


def check_normalization():
    local = [dict(m=1, field=(43, 21, 1), points=[(57, 1)], values=[56, -1]),
             dict(m=2, field=(15, 23, 1), points=[(85, 3)], values=[79, -1])]
    certificate = candidate(65, local, [(0, 1), (1, 1)], [(0, 56), (1, 14)], (), 3)
    assert sorted((certificate["divisor"], certificate["cofactor"])) == [5, 13]
    repeated = [(0, 1), (0, 1)]
    assert list(field_parts(65, local, repeated, [0, 1])) == [(1, (43, 21, 1), 1, [], 56)]
    assert candidate(65, local, repeated, [(0, 56), (1, 56)], (), 3) is None


def run():
    for n in INPUTS:
        start = monotonic()
        with Popen([sys.executable, "-B", __file__, str(n)], stdout=PIPE, stderr=PIPE,
                   text=True, start_new_session=True) as process:
            try:
                stdout, stderr = process.communicate(timeout=SECONDS)
                status = None if process.returncode == 0 else "process-error"
            except TimeoutExpired:
                try:
                    killpg(process.pid, SIGKILL)
                except ProcessLookupError:
                    pass
                stdout, stderr = process.communicate()
                status = "time-cap"
        lines = stdout.split("\n")[:-1]
        record = json.loads(lines[-1]) if lines else dict(n=n)
        if status:
            record.update(status=status, error=stderr)
        print(json.dumps(dict(record, seconds=round(monotonic()-start, 3))), flush=True)


def verification_record(n):
    local, generators = prepare(n)
    exact, identical = SHEARED["evaluation_rows"](local, HEIGHT, 2)
    rational_words = SHEARED["SUPPORTED"]["QUADRATIC"]["rational_words"]
    primorial = prod(PRIMES)

    def smooth(value):
        remainder = abs(value)
        while remainder > 1 and (common := gcd(remainder, primorial)) > 1:
            remainder //= common
        return remainder == 1

    labels, retained = [], []
    for j, (i, word) in enumerate(generators):
        residue = prod(local[i]["values"][k] for k in GRID["support"](word)) % n
        centered = (residue+n//2) % n-n//2
        for offset in OFFSETS:
            label = centered+offset*n
            if smooth(label):
                labels.append(label)
                retained.append(j)
                break
    public_start = isqrt(n-1)+1
    public = []
    for u in range(public_start, public_start+64):
        if gcd(u, n) != 1:
            raise ValueError(f"{n}: unexpected nonunit public witness")
        if smooth(u*u-n):
            public.append(u*u-n)
    lift_nullity = len(basis(rational_words(labels)))
    extended_nullity = len(basis(rational_words(labels+public)))
    if lift_nullity or extended_nullity:
        raise ValueError(f"{n}: frozen exhaustion now has candidate dependencies")
    return dict(n=n, dimensions=[len(field["basis"]) for field in local],
                original_nullity=len(basis(exact)), identical_nullity=len(basis(identical)),
                retained=len(retained), original_retained_nullity=len(basis([exact[j] for j in retained])),
                lift_nullity=lift_nullity, attempts=0, public=len(public), extended_nullity=extended_nullity,
                status="exhausted")


def verify(path):
    def unique_keys(pairs):
        record = dict(pairs)
        if len(record) != len(pairs):
            raise ValueError("duplicate key in result record")
        return record

    records = [json.loads(line, object_pairs_hook=unique_keys) for line in path.read_text().splitlines()]
    if len(records) != len(INPUTS) or any(not isinstance(record, dict) for record in records):
        raise ValueError("expected three JSON objects in frozen order")
    for n, record in zip(INPUTS, records, strict=True):
        seconds = record.pop("seconds", None)
        if type(seconds) not in (int, float) or not isfinite(seconds) or seconds < 0:
            raise ValueError(f"{n}: invalid recorded wall time")
        if record.get("n") != n or record.get("status") != "exhausted":
            raise ValueError(f"{n}: unexpected input or status")
        expected = verification_record(n)
        if json.dumps(record, sort_keys=True) != json.dumps(expected, sort_keys=True):
            raise ValueError(f"{n}: saved counts disagree with the independent replay")
    print(f"Verified all {len(records)} frozen integer-lift records (wall times excluded).")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("n", nargs="?", type=int, choices=INPUTS)
    mode.add_argument("--verify", type=Path, help="recompute the three frozen records")
    args = parser.parse_args()
    if args.verify is not None:
        try:
            verify(args.verify)
        except (ValueError, OSError) as error:
            parser.error(str(error))
    elif args.n is None:
        check_normalization()
        run()
    else:
        print(json.dumps(measure(args.n)), flush=True)
