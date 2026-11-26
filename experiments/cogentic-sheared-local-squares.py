"""Join local quadratic square bases by rational squareclasses of sheared evaluations."""

import argparse
import json
import subprocess
import sys
from collections import Counter
from math import gcd, isfinite, isqrt, prod
from pathlib import Path
from runpy import run_path
from time import monotonic


HERE = Path(__file__).resolve().parent
MIXED = run_path(str(HERE / "cogentic-monic-mixed-complete.py"))
SUPPORTED = run_path(str(HERE / "cogentic-quadratic-supported-kernel.py"))
BOUNDED = run_path(str(HERE / "cogentic-quadratic-grid-norms.py"))["bounded_words"]
PERFECT_POWER = run_path(str(HERE / "cogentic-monic-pair.py"))["perfect_power_divisor"]
GRID, SQUARES = MIXED["GRID"], MIXED["SQUARES"]
INPUTS = json.loads((HERE / "cogentic-sheared-inputs.json").read_text())
HEIGHT, ATTEMPTS, SECONDS = 64, 32, 15
SHIFTS, SLOPES = (0, 1, 2), (0, -1)


def field_candidates(n):
    root = isqrt(n)
    for shift in SHIFTS:
        m = root-shift
        for u in SLOPES:
            yield m, (n-m*m-u*m, u, 1)


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


def measure(n, height=HEIGHT, *, progress=None):
    if n < 2 or height < 1:
        raise ValueError("require N >= 2 and a positive height")
    case = dict(n=n, height=height)
    if n in (2, 3, 5, 7):
        return dict(case, status="prime")
    if n % 2 == 0:
        return dict(case, status="even", divisor=2, cofactor=n//2)
    divisor = PERFECT_POWER(n)
    if divisor is not None:
        return dict(case, status="perfect-power", divisor=divisor, cofactor=n//divisor)

    local_fields, groups, generators, skipped = [], [], [], []
    last_base = None
    for m, field in field_candidates(n):
        v, u, _ = field
        common = gcd(2*m+u, n)
        if 1 < common < n:
            return dict(case, status="derivative-gcd", divisor=common, cofactor=n//common, m=m, slope=u)
        if common == n:
            skipped.append(dict(m=m, field=field, reason="nonunit-derivative"))
            continue
        discriminant = u*u-4*v
        if discriminant >= 0 and isqrt(discriminant)**2 == discriminant:
            skipped.append(dict(m=m, field=field, reason="reducible"))
            continue
        if m != last_base:
            last_base = m
            points = [(a, b) for a in range(-height, height+1) for b in range(1, height+1)
                      if gcd(a, b) == gcd(a-b*m, n) == 1]
            values = [a-b*m for a, b in points] + [-1]
        basis = SUPPORTED["grid_square_masks"](field, points, height, packed_roots=True)
        groups.append(list(range(len(generators), len(generators)+len(basis))))
        generators.extend((len(local_fields), mask) for mask in basis)
        local_fields.append(dict(m=m, field=field, points=points, values=values, basis=basis))
    if skipped:
        case["skipped_fields"] = skipped
    if not local_fields:
        return dict(case, status="no-eligible-fields")
    rational, identical = evaluation_rows(local_fields, height, max(SHIFTS)-min(SHIFTS))
    columns = len(generators)

    def dependencies(rows, order):
        return GRID["eliminate"]((rows[j] for j in order), (1 << j for j in order))

    output = dict(case, fields=[(entry["m"], entry["field"]) for entry in local_fields],
                  local_dimensions=list(map(len, groups)), rational_nullity=len(dependencies(rational, range(columns))),
                  identical_nullity=len(dependencies(identical, range(columns))), order=[], attempts=0)
    assert output["identical_nullity"] <= output["rational_nullity"]
    if progress is not None:
        progress(dict(output, status="prepared"))

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
    if output["attempts"] != output["rational_nullity"]:
        raise ArithmeticError("matching basis was not exhausted")
    return dict(output, status="complete-no-split")


def run_case(n):
    start = monotonic()
    command = [sys.executable, __file__, "--worker", str(n)]
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
        record.pop("certificate", None)
        record.update(status="time-cap" if error == "time-cap" else "process-error", error=error)
    elif record.get("status") in (None, "prepared"):
        record.update(status="process-error", error="missing terminal result")
    record["seconds"] = round(monotonic()-start, 3)
    return record


def run():
    values = [a-b*(211-shift) for shift in SHIFTS for a in range(-3, 4) for b in range(1, 4)
              if gcd(a, b) == 1] + [-1]
    words = BOUNDED(values, (2+max(SHIFTS))*3**2)
    expected = SUPPORTED["QUADRATIC"]["rational_words"](values)
    assert GRID["eliminate"](words, (1 << j for j in range(len(values)))) == GRID["eliminate"](
        expected, (1 << j for j in range(len(values))))
    for n in INPUTS:
        print(json.dumps(run_case(n)), flush=True)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def checkpoint_object(pairs):
    record = dict(pairs)
    require(len(record) == len(pairs), "duplicate keys in checkpoint")
    return record


def verify_certificate(n, height, certificate, *, admitted=None, expected_factors=None):
    """Verify a saved square split independently in PARI and return its used fields."""
    checker = run_path(str(HERE / "cogentic-monic-degree-certificate-check.py"))["GP_CHECK"]
    require(type(n) is int and n > 2 and n % 2 and type(height) is int and height >= 1,
            "expected an odd modulus and a positive height")
    require(isinstance(certificate, dict) and
            set(certificate) == {"fields", "normalization", "ratio", "divisor", "cofactor",
                                 "unpaired_evaluations"},
            f"{n}: invalid square certificate")
    used, evaluations, calls, residues = set(), [], [], []
    for part in certificate["fields"]:
        m, field, sign, points, residue = (part[key] for key in ("m", "field", "sign", "points", "residue"))
        require(type(m) is int and len(field) == 3 and all(type(c) is int for c in field) and
                field[-1] == 1 and field[0]+field[1]*m+m*m == n,
                f"{n}: expected a monic exact-value quadratic field")
        key = m, tuple(field)
        require((admitted is None or key in admitted) and key not in used and
                type(sign) is int and sign in (-1, 1),
                f"{n}: invalid local field, repeated field, or sign")
        used.add(key)
        require(len({tuple(point) for point in points}) == len(points) and
                all(type(a) is int and type(b) is int and abs(a) <= height and 1 <= b <= height
                    and gcd(a, b) == gcd(a-b*m, n) == 1 for a, b in points),
                f"{n}: invalid primitive unit support")
        calls.append(f"check_square(Polrev({list(field)}),{[list(point) for point in points]},{sign},{m},{n})")
        values = [a-b*m for a, b in points]
        require(type(residue) is int and 0 <= residue < n and residue**2 % n == sign*prod(values) % n,
                f"{n}: incorrect modular square")
        evaluations.extend(values)
        if sign == -1:
            evaluations.append(-1)
        residues.append(residue)
    require(bool(used), f"{n}: missing field square witnesses")
    line, = GRID["gp"](checker + f'iferr(print([{",".join(calls)}]),err,print(err);quit(1));\n')
    independent = json.loads(line)
    require(all(a in (b, -b % n) for a, b in zip(residues, independent, strict=True)),
            f"{n}: saved residues disagree with exact field roots")
    total = prod(evaluations)
    scale = isqrt(max(total, 0))
    normalization = certificate["normalization"]
    require(scale > 0 and scale**2 == total and type(normalization) is int and scale % n == normalization,
            f"{n}: incorrect rational square normalization")
    unpaired = sorted(value for value, count in Counter(evaluations).items() if count % 2)
    support = certificate["unpaired_evaluations"]
    require(isinstance(support, list) and all(type(value) is int for value in support) and unpaired == support,
            f"{n}: incorrect evaluation support")
    ratio = prod(residues)*pow(scale, -1, n) % n
    require(ratio**2 % n == 1 and type(certificate["ratio"]) is int and ratio == certificate["ratio"],
            f"{n}: incorrect normalized root")
    divisor = gcd(ratio-1, n)
    cofactor = certificate["cofactor"]
    require(1 < divisor < n and type(certificate["divisor"]) is int and divisor == certificate["divisor"]
            and type(cofactor) is int and n//divisor == cofactor,
            f"{n}: incorrect factor certificate")
    require(expected_factors is None or tuple(sorted((divisor, cofactor))) == tuple(sorted(expected_factors)),
            f"{n}: certificate disagrees with the regenerated factors")
    return used


def verify(path):
    labels = run_path(str(HERE / "cogentic-sheared-cohort.py"))["generate"]()
    cases = [json.loads(line, object_pairs_hook=checkpoint_object) for line in path.read_text().splitlines()]
    require(all(isinstance(case, dict) for case in cases) and
            [case.get("n") for case in cases] == INPUTS == list(labels),
            "expected all eight frozen inputs exactly once in frozen order")
    # Stable metadata from the frozen run, excluding elapsed time and root sign choices.
    expected = (
        ([628, 290, 772, 164, 319, 227], 332, [2, 0], 2),
        ([384, 358, 325, 107, 726, 550], 350, [4, 5], 1),
        ([645, 667, 343, 155, 585, 183], 451, [1, 0], 1),
        ([1103, 722, 393, 285, 380, 253], 670, [0, 1], 5),
        ([386, 352, 419, 251, 277, 176], 0, [2, 0, 1, 4, 3, 5], 0),
        ([859, 652, 378, 212, 747, 187], 727, [0, 1], 2),
        ([525, 864, 677, 405, 359, 13], 706, [1, 2], 1),
        ([1110, 606, 189, 388, 298, 271], 615, [0], 1),
    )
    for case, (dimensions, nullity, order, attempts) in zip(cases, expected, strict=True):
        n = case["n"]
        fields = [[m, list(field)] for m, field in field_candidates(n)]
        status = "square-split" if nullity else "complete-no-split"
        stable = dict(n=n, height=HEIGHT, fields=fields, local_dimensions=dimensions,
                      rational_nullity=nullity, identical_nullity=0, order=order,
                      attempts=attempts, status=status)
        metadata = {key: value for key, value in case.items() if key not in ("seconds", "certificate")}
        seconds = case.get("seconds")
        require(json.dumps(metadata, sort_keys=True) == json.dumps(stable, sort_keys=True) and
                type(seconds) in (int, float) and isfinite(seconds) and seconds >= 0,
                f"{n}: incorrect frozen outcome or matching metadata")
        if not nullity:
            require("certificate" not in case, f"{n}: no-split record contains a certificate")
            result = json.loads(json.dumps(measure(n)))
            require(result == stable, f"{n}: recomputation disagrees with the zero matching nullity")
            print(f"{n}: all eligible fields recomputed, rational matching nullity zero")
            continue
        certificate = case["certificate"]
        require(0 < attempts <= ATTEMPTS, f"{n}: invalid exact root attempt count")
        admitted = {(fields[i][0], tuple(fields[i][1])) for i in order}
        used = verify_certificate(n, HEIGHT, certificate, admitted=admitted, expected_factors=labels[n])
        last_m, last_field = fields[order[-1]]
        require((last_m, tuple(last_field)) in used, f"{n}: missing newly admitted field")
        print(f"{n} = {certificate['divisor']} * {certificate['cofactor']}, {len(used)} exact field roots")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("n", nargs="?", type=int, help="odd or even integer N >= 2")
    mode.add_argument("--verify", type=Path, help="verify all eight frozen benchmark results")
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker and args.n is None:
        parser.error("worker requires N")
    if args.n is not None and args.n < 2:
        parser.error("require N >= 2")
    try:
        if args.verify is not None:
            verify(args.verify)
        elif args.worker:
            def emit(record):
                print(json.dumps(record), flush=True)
            emit(measure(args.n, progress=emit))
        elif args.n is not None:
            print(json.dumps(run_case(args.n)), flush=True)
        else:
            run()
    except (KeyError, OSError, TypeError, ValueError, subprocess.SubprocessError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
