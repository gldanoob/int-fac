"""Join local quadratic square bases by rational squareclasses of sheared evaluations."""

import json
import subprocess
import sys
from collections import Counter
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path
from time import monotonic


HERE = Path(__file__).resolve().parent
MIXED = run_path(str(HERE / "cogentic-monic-mixed-complete.py"))
SUPPORTED = run_path(str(HERE / "cogentic-quadratic-supported-kernel.py"))
BOUNDED = run_path(str(HERE / "cogentic-quadratic-grid-norms.py"))["bounded_words"]
GRID, SQUARES = MIXED["GRID"], MIXED["SQUARES"]
INPUTS = json.loads((HERE / "cogentic-sheared-inputs.json").read_text())
HEIGHT, ATTEMPTS, SECONDS = 64, 32, 15
SHIFTS, SLOPES = (0, 1, 2), (0, -1)


def evaluation_rows(local_fields, height, spread):
    values = sorted({value for entry in local_fields for value in entry["values"]})
    bits = dict(zip(values, BOUNDED(values, (2+spread)*height**2), strict=True))
    indices = {value: j for j, value in enumerate(values)}
    rational, identical = [], []
    for entry in local_fields:
        for word in entry["basis"]:
            selected = (entry["values"][j] for j in GRID["support"](word))
            row, exact = 0, 0
            for value in selected:
                row ^= bits[value]
                exact ^= 1 << indices[value]
            rational.append(row)
            identical.append(exact)
    return rational, identical


def roots(n, local_fields, generators, history):
    combined = Counter()
    for j in GRID["support"](history):
        i, mask = generators[j]
        combined[i] ^= mask
    certificates, evaluations = [], []
    for i, mask in sorted(combined.items()):
        if not mask:
            continue
        entry = local_fields[i]
        m, field, all_points = entry["m"], entry["field"], entry["points"]
        sign = 1-2*(mask >> len(all_points))
        points = [all_points[j] for j in GRID["support"](mask & ((1 << len(all_points))-1))]
        value = [sign, 0]
        for a, b in points:
            value = SQUARES["multiply_mark"](field, value, a, b)
        cleared = MIXED["quadratic_numerator"](field, value)
        assert cleared is not None
        residue = SQUARES["evaluate"](cleared, m)*pow(2*m+field[1], -1, n) % n
        evaluations.extend(a-b*m for a, b in points)
        if sign < 0:
            evaluations.append(-1)
        assert residue**2 % n == sign*prod((a-b*m) % n for a, b in points) % n
        certificates.append(dict(m=m, field=field, sign=sign, points=points, residue=residue))
    total = prod(evaluations)
    normalization = isqrt(total)
    assert normalization**2 == total and gcd(normalization, n) == 1
    product = prod(entry["residue"] for entry in certificates) % n
    ratio = product*pow(normalization, -1, n) % n
    assert ratio**2 % n == 1
    divisor = gcd(ratio-1, n)
    if not 1 < divisor < n:
        return None
    assert n % divisor == 0
    unpaired = sorted(value for value, count in Counter(evaluations).items() if count % 2)
    return dict(fields=certificates, normalization=normalization % n, ratio=ratio,
                divisor=divisor, cofactor=n//divisor, unpaired_evaluations=unpaired)


def measure(n, height=HEIGHT):
    local_fields, groups, generators = [], [], []
    for shift in SHIFTS:
        m = isqrt(n)-shift
        points = [(a, b) for a in range(-height, height+1) for b in range(1, height+1)
                  if gcd(a, b) == gcd(a-b*m, n) == 1]
        values = [a-b*m for a, b in points] + [-1]
        for u in SLOPES:
            common = gcd(2*m+u, n)
            if 1 < common < n:
                return dict(n=n, height=height, status="derivative-gcd", divisor=common, m=m, slope=u)
            assert common == 1
            field = (n-m*m-u*m, u, 1)
            basis = SUPPORTED["grid_square_masks"](field, points, height, packed_roots=True)
            groups.append(list(range(len(generators), len(generators)+len(basis))))
            generators.extend((len(local_fields), mask) for mask in basis)
            local_fields.append(dict(m=m, field=field, points=points, values=values, basis=basis))
    rational, identical = evaluation_rows(local_fields, height, max(SHIFTS)-min(SHIFTS))
    columns = len(generators)

    def dependencies(rows, order):
        return GRID["eliminate"]((rows[j] for j in order), (1 << j for j in order))

    output = dict(n=n, height=height, fields=[(entry["m"], entry["field"]) for entry in local_fields],
                  local_dimensions=list(map(len, groups)), rational_nullity=len(dependencies(rational, range(columns))),
                  identical_nullity=len(dependencies(identical, range(columns))), order=[], attempts=0)
    assert output["identical_nullity"] <= output["rational_nullity"]
    print(json.dumps(dict(output, status="prepared")), flush=True)

    previous, selected, unused = [], [], list(range(len(local_fields)))
    for _ in local_fields:
        candidates = [(dependencies(rational, selected + groups[i]), i) for i in unused]
        basis, i = max(candidates, key=lambda case: (len(case[0]), len(groups[case[1]]), -case[1]))
        output["order"].append(i)
        assert basis[:len(previous)] == previous
        for history in basis[len(previous):]:
            if output["attempts"] == ATTEMPTS:
                return dict(output, status="query-cap")
            output["attempts"] += 1
            certificate = roots(n, local_fields, generators, history)
            if certificate:
                return dict(output, status="square-split", certificate=certificate)
        previous = basis
        selected.extend(groups[i])
        unused.remove(i)
    return dict(output, status="complete-no-split")


def run():
    values = [a-b*(211-shift) for shift in SHIFTS for a in range(-3, 4) for b in range(1, 4)
              if gcd(a, b) == 1] + [-1]
    words = BOUNDED(values, (2+max(SHIFTS))*3**2)
    expected = SUPPORTED["QUADRATIC"]["rational_words"](values)
    assert GRID["eliminate"](words, (1 << j for j in range(len(values)))) == GRID["eliminate"](
        expected, (1 << j for j in range(len(values))))
    for n in INPUTS:
        start = monotonic()
        command = [sys.executable, __file__, str(n)]
        try:
            process = subprocess.run(command, capture_output=True, text=True, timeout=SECONDS)
            lines = process.stdout.splitlines()
            error = (process.stderr or str(process.returncode)) if process.returncode else None
        except subprocess.TimeoutExpired as limit:
            output = limit.stdout or b""
            lines = output[:output.rfind(b"\n")+1].decode().splitlines()
            error = "time-cap"
        record = json.loads(lines[-1]) if lines else dict(n=n, height=HEIGHT)
        if error:
            record.update(status="time-cap" if error == "time-cap" else "process-error", error=error)
        record["seconds"] = round(monotonic()-start, 3)
        print(json.dumps(record), flush=True)


def verify(path):
    checker = run_path(str(HERE / "cogentic-monic-degree-certificate-check.py"))["GP_CHECK"]
    labels = run_path(str(HERE / "cogentic-sheared-cohort.py"))["generate"]()
    cases = [json.loads(line) for line in path.read_text().splitlines()]
    assert [case["n"] for case in cases] == INPUTS == list(labels)
    for case in cases:
        n = case["n"]
        if case["status"] == "derivative-gcd":
            assert case["divisor"] in labels[n]
        if case["status"] != "square-split":
            assert "certificate" not in case
            continue
        certificate = case["certificate"]
        assert case["height"] == HEIGHT and 0 < case["attempts"] <= ATTEMPTS
        fields, evaluations, calls = set(), [], []
        residues = []
        for part in certificate["fields"]:
            m, field, sign, points, residue = (part[key] for key in ("m", "field", "sign", "points", "residue"))
            v, u, leading = field
            assert leading == 1 and u in SLOPES and isqrt(n)-m in SHIFTS and v == n-m*m-u*m
            assert (m, u) not in fields and sign in (-1, 1)
            fields.add((m, u))
            assert len({tuple(point) for point in points}) == len(points)
            assert all(abs(a) <= HEIGHT and 1 <= b <= HEIGHT and gcd(a, b) == gcd(a-b*m, n) == 1
                       for a, b in points)
            calls.append(f"check_square(Polrev({field}),{points},{sign},{m},{n})")
            values = [a-b*m for a, b in points]
            assert residue**2 % n == sign*prod(values) % n
            evaluations.extend(values)
            if sign == -1:
                evaluations.append(-1)
            residues.append(residue)
        line, = GRID["gp"](checker + f'iferr(print([{",".join(calls)}]),err,print(err);quit(1));\n')
        independent = json.loads(line)
        assert all(a in (b, -b % n) for a, b in zip(residues, independent, strict=True))
        total = prod(evaluations)
        scale = isqrt(total)
        assert scale**2 == total and scale % n == certificate["normalization"]
        unpaired = sorted(value for value, count in Counter(evaluations).items() if count % 2)
        assert unpaired == certificate["unpaired_evaluations"]
        ratio = prod(residues)*pow(scale, -1, n) % n
        assert ratio**2 % n == 1 and ratio == certificate["ratio"]
        divisor = gcd(ratio-1, n)
        assert divisor == certificate["divisor"] and divisor*certificate["cofactor"] == n
        assert tuple(sorted((divisor, certificate["cofactor"]))) == labels[n]
        print(f"{n} = {divisor} * {n//divisor}, {len(fields)} exact field roots")


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--verify":
        verify(Path(sys.argv[2]))
    elif len(sys.argv) == 2:
        print(json.dumps(measure(int(sys.argv[1]))), flush=True)
    else:
        run()
