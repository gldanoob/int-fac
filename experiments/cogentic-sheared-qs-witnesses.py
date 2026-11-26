"""Run the preregistered auxiliary square-witness menu on the scaling cohort."""

import argparse
import json
import os
from collections import Counter
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path
from signal import SIGKILL
from subprocess import PIPE, Popen, TimeoutExpired
import sys
from time import monotonic


HERE = Path(__file__).resolve().parent
SHEARED = run_path(str(HERE / "cogentic-sheared-local-squares.py"))
RANK = run_path(str(HERE / "cogentic-mixed-lifted-rank.py"))["crt_rank"]
GRID, SQUARES = SHEARED["GRID"], SHEARED["SQUARES"]
INPUTS = json.loads((HERE / "cogentic-sheared-scaling-inputs.json").read_text())
HEIGHT, CUTOFF, SECONDS, ATTEMPTS = 64, 16384, 15, 32


def prepare_fields(n):
    fields, generators, skipped = [], [], 0
    last_base = None
    for m, field in SHEARED["field_candidates"](n):
        discriminant = field[1]**2-4*field[0]
        if gcd(2*m+field[1], n) != 1 or (
            discriminant >= 0 and isqrt(discriminant)**2 == discriminant
        ):
            skipped += 1
            continue
        if m != last_base:
            last_base = m
            points = [(a, b) for a in range(-HEIGHT, HEIGHT+1) for b in range(1, HEIGHT+1)
                      if gcd(a, b) == gcd(a-b*m, n) == 1]
            values = [a-b*m for a, b in points] + [-1]
        basis = SHEARED["SUPPORTED"]["grid_square_masks"](field, points, HEIGHT, packed_roots=True)
        generators.extend((len(fields), word) for word in basis)
        fields.append(dict(m=m, field=field, points=points, values=values, basis=basis))
    return fields, generators, skipped


def public_menu(n):
    center = isqrt(n-1)+1
    return [(r*r-n, r) for r in range(center-32, center+33)
            if r > 0 and r*r != n and gcd(r, n) == 1]


def extra_primes(public):
    bound = max((isqrt(abs(value)) for value, _ in public), default=1)
    assert bound <= 2**20
    primes = tuple(GRID["primes_through"](bound))
    extra = set()
    for value, _ in public:
        remaining = abs(value)
        for p in primes:
            if p*p > remaining:
                break
            if remaining % p == 0:
                if p > CUTOFF:
                    extra.add(p)
                while remaining % p == 0:
                    remaining //= p
        if remaining > CUTOFF:
            extra.add(remaining)
    return sorted(extra)


def augmented_words(values, extra):
    reduced, high = [], []
    for value in values:
        remaining, mask = abs(value), 0
        for j, p in enumerate(extra):
            if p > remaining:
                break
            while remaining % p == 0:
                remaining //= p
                mask ^= 1 << j
        reduced.append(-remaining if value < 0 else remaining)
        high.append(mask)
    low = SHEARED["BOUNDED"](reduced, CUTOFF)
    offset = max((word.bit_length() for word in low), default=0)
    return [a | (b << offset) for a, b in zip(low, high, strict=True)]


def matching_rows(fields, public, encode):
    values = sorted({value for entry in fields for value in entry["values"]})
    words = encode(values, [value for value, _ in public])
    lookup = dict(zip(values, words[:len(values)], strict=True))
    rows = []
    for entry in fields:
        for word in entry["basis"]:
            row = 0
            for j in GRID["support"](word):
                row ^= lookup[entry["values"][j]]
            rows.append(row)
    return rows + words[len(values):]


def bases(rows, boundary):
    columns = list(range(len(rows)))
    field, public, full = [
        GRID["eliminate"]((rows[j] for j in indices), (1 << j for j in indices))
        for indices in (columns[:boundary], columns[boundary:], columns)
    ]
    pivots, extension = {}, []
    for mode, masks in (("field", field), ("public", public), ("mixed", full)):
        for original in masks:
            word = original
            while word and word.bit_length() in pivots:
                word ^= pivots[word.bit_length()]
            if word:
                pivots[word.bit_length()] = word
                extension.append((mode, original))
    assert len(extension) == len(full)
    return dict(field=len(field), public=len(public), full=len(full)), extension


def exact_ratio(n, fields, generators, public, history):
    combined, selected = Counter(), []
    for j in GRID["support"](history):
        if j < len(generators):
            i, mask = generators[j]
            combined[i] ^= mask
        else:
            selected.append(public[j-len(generators)])
    evaluations, residues, parts = [value for value, _ in selected], [r % n for _, r in selected], []
    for i, mask in sorted(combined.items()):
        if not mask:
            continue
        entry = fields[i]
        m, field, all_points = entry["m"], entry["field"], entry["points"]
        sign = 1-2*(mask >> len(all_points))
        points = [all_points[j] for j in GRID["support"](mask & ((1 << len(all_points))-1))]
        value = [sign, 0]
        for a, b in points:
            value = SQUARES["multiply_mark"](field, value, a, b)
        numerator = SHEARED["MIXED"]["quadratic_numerator"](field, value)
        assert numerator is not None
        residue = SQUARES["evaluate"](numerator, m)*pow(2*m+field[1], -1, n) % n
        marks = [a-b*m for a, b in points]
        assert residue**2 % n == sign*prod(marks) % n
        evaluations.extend([sign, *marks])
        residues.append(residue)
        parts.append(dict(m=m, field=field, sign=sign, points=points, residue=residue))
    total = prod(evaluations)
    normal = isqrt(total)
    assert normal**2 == total and gcd(normal, n) == 1
    z = prod(residues)*pow(normal, -1, n) % n
    assert z*z % n == 1
    divisor = gcd(z-1, n)
    if 1 < divisor < n:
        return z, dict(fields=parts, public=selected, normalization=normal % n,
                       ratio=z, divisor=divisor, cofactor=n//divisor)
    return z, None


def measure(n, progress):
    fields, generators, skipped = prepare_fields(n)
    public = public_menu(n)
    extra = extra_primes(public)
    rows = matching_rows(fields, public, lambda marks, auxiliary: augmented_words(marks+auxiliary, extra))
    dimensions, history = bases(rows, len(generators))
    roots = dict(field=[], public=[], mixed=[])
    certificates = []
    output = dict(n=n, height=HEIGHT, bits=n.bit_length(), public=len(public),
                  local_dimensions=[len(field["basis"]) for field in fields],
                  skipped_fields=skipped, auxiliary_large_primes=len(extra), dimensions=dimensions)

    def report(status):
        restricted = roots["field"] + roots["public"]
        full = restricted + roots["mixed"]
        groups = dict(field=roots["field"], public=roots["public"], full=full)
        images = {key: dict(tested=len(group), rank_lower=RANK(n, group),
                            complete=len(group) == dimensions[key])
                  for key, group in groups.items()}
        controls_complete = images["field"]["complete"] and images["public"]["complete"]
        gain = images["full"]["rank_lower"]-RANK(n, restricted) if controls_complete else None
        return dict(output, status=status, images=images, mixed_gain_lower=gain,
                    mixed_gain_complete=controls_complete and images["full"]["complete"],
                    certificates=certificates)

    progress(report("prepared"))
    for mode, mask in history[:ATTEMPTS]:
        z, certificate = exact_ratio(n, fields, generators, public, mask)
        roots[mode].append(z)
        if certificate:
            certificates.append(dict(certificate, mode=mode))
        progress(report("running"))
    return report("complete" if len(history) <= ATTEMPTS else "query-cap")


def run_case(n):
    start = monotonic()
    command = [sys.executable, "-B", __file__, "--worker", str(n)]
    with Popen(command, stdout=PIPE, stderr=PIPE, text=True, start_new_session=True) as process:
        try:
            stdout, stderr = process.communicate(timeout=SECONDS)
            capped = False
        except TimeoutExpired:
            try:
                os.killpg(process.pid, SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = process.communicate()
            capped = True
    lines = stdout.split("\n")[:-1]
    result = json.loads(lines[-1]) if lines else dict(n=n, height=HEIGHT, bits=n.bit_length())
    if capped:
        result["status"] = "time-cap"
    elif process.returncode:
        result.update(status="process-error", error=stderr or str(process.returncode))
    assert result["n"] == n and result["height"] == HEIGHT
    return dict(result, seconds=round(monotonic()-start, 3))


def check_mixed_control():
    fields = [dict(m=2, field=(51, 19, 1), points=[(30, 1)], values=[28, -1], basis=[1])]
    public = [(7, 10)]
    rows = matching_rows(fields, public, lambda marks, auxiliary: augmented_words(marks+auxiliary, []))
    dimensions, selected = bases(rows, 1)
    assert dimensions == dict(field=0, public=0, full=1) and selected == [("mixed", 3)]
    ratio, certificate = exact_ratio(93, fields, [(0, 1)], public, 3)
    assert ratio in (61, 32) and certificate["divisor"] in (3, 31)


def verify(path):
    check_mixed_control()
    labels = run_path(str(HERE / "cogentic-sheared-scaling-cohort.py"))["generate"]()
    rational_words = SHEARED["SUPPORTED"]["QUADRATIC"]["rational_words"]
    results = [json.loads(line) for line in path.read_text().splitlines()]
    baseline = [json.loads(line) for line in (HERE / "cogentic-sheared-scaling-results.jsonl")
                .read_text().splitlines()]
    assert [record["n"] for record in results] == INPUTS == list(labels)
    independently_ranked = 0
    for record, prior in zip(results, baseline, strict=True):
        n = record["n"]
        assert n == prior["n"] and record["height"] == HEIGHT and record["bits"] == n.bit_length()
        assert record["status"] == "complete"
        dimensions, images = record["dimensions"], record["images"]
        assert dimensions.keys() == images.keys() == {"field", "public", "full"}
        assert record["local_dimensions"] == prior["local_dimensions"]
        assert dimensions["field"] == prior["rational_nullity"]
        public = public_menu(n)
        assert record["public"] == len(public)
        expected_public = GRID["eliminate"](rational_words([value for value, _ in public]),
                                           (1 << j for j in range(len(public))))
        assert dimensions["public"] == len(expected_public)
        fields, generators, skipped = prepare_fields(n)
        assert record["local_dimensions"] == [len(field["basis"]) for field in fields]
        assert record["skipped_fields"] == skipped
        independent_rows = matching_rows(fields, public, lambda marks, auxiliary:
                                          SHEARED["BOUNDED"](marks, CUTOFF, extra_values=auxiliary))
        independent_dims, _ = bases(independent_rows, len(generators))
        assert dimensions == independent_dims == dict(field=0, public=0, full=0)
        independently_ranked += 1
        for image in images.values():
            assert image == dict(tested=0, rank_lower=0, complete=True)
        assert record["mixed_gain_complete"] and record["mixed_gain_lower"] == 0
        assert record["certificates"] == []
    assert independently_ranked == len(INPUTS)
    print(f"Validated {len(results)} cohort labels and {independently_ranked} independent ranks.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", type=int)
    parser.add_argument("--verify", type=Path)
    args = parser.parse_args()
    if args.worker is not None:
        def progress(record):
            print(json.dumps(record), flush=True)
        progress(measure(args.worker, progress))
    elif args.verify is not None:
        verify(args.verify)
    else:
        for n in INPUTS:
            print(json.dumps(run_case(n)), flush=True)


if __name__ == "__main__":
    main()
