"""Fixed mixed-field grid on two previously unsplit public semiprimes."""

import argparse
import json
from itertools import combinations
from math import gcd, prod
from pathlib import Path
from runpy import run_path
from subprocess import TimeoutExpired
from time import monotonic


HERE = Path(__file__).resolve().parent
GRID = run_path(str(HERE / "cogentic-monic-large-primes.py"))
DRIVER = run_path(str(HERE / "cogentic-monic-kernel-driver.py"))
SCHEDULED_DEGREE = run_path(str(HERE / "cogentic-monic-pair.py"))["scheduled_degree"]
COLLECT = run_path(str(HERE / "cogentic-monic-lattice-sieve.py"))["collect"]
PROBES = run_path(str(HERE / "cogentic-monic-square-probes.py"))
SQUARES = run_path(str(HERE / "cogentic-monic-dyadic-ascent.py"))
INPUTS = (310556537, 449508911)
HEIGHTS = (128, 256)
PAIRS = tuple(combinations(range(3), 2))
PROBE_CAP, EXACT_SECONDS, QUERY_CAP = 257, 5, 4


def field_library(n):
    m, f, g = GRID["CHECK_PAIR"](n, SCHEDULED_DEGREE(n))
    fields = f, g, (g[0]-4*m, g[1]+4, *g[2:])
    derivatives = [sum(j*c*m**(j-1) for j, c in enumerate(field) if j) for field in fields]
    assert all(sum(c*m**j for j, c in enumerate(field)) == n for field in fields)
    gcds = [gcd(value, n) for value in derivatives]
    if any(value != 1 for value in gcds):
        return dict(n=n, m=m, status="nonunit-derivative", derivative_gcds=gcds)
    source = [list(field) for field in fields]
    discriminants = json.loads(DRIVER["gp_value"](f"apply(poldisc,apply(Polrev,{source}))", 5))
    return m, fields, derivatives, discriminants


def rank_core(collected):
    variables, rows = [], []
    for i, marks in enumerate(collected):
        for point, small, large, _ in marks:
            variables.append((i, point))
            rows.append([(0, *point), *((i+1, p, root) for _, p, root in small+large)])
    core, basis = GRID["parity_basis"](rows)
    return [variables[j] for j in core], basis


def restrict(basis, row):
    pivot = next((word for word in basis if (word & row).bit_count() % 2), 0)
    if not pivot:
        return basis
    return [word ^ pivot if (word & row).bit_count() % 2 else word
            for word in basis if word != pivot]


def probe(fields, discriminants, blocks, basis):
    for field, disc, (offset, points) in zip(fields, discriminants, blocks, strict=True):
        degree = len(field)-1
        derivative = [j*c for j, c in enumerate(field) if j]
        norms = [GRID["homogeneous"](field, *point) for point in points]
        mask = (1 << len(points))-1
        for p in GRID["primes_through"](PROBE_CAP):
            if not basis or not points:
                break
            if p == 2 or disc % p == 0:
                continue
            squares = {r*r % p for r in range(1, p)}
            for root in range(p):
                if not GRID["polynomial"](field, root, p):
                    slope = GRID["polynomial"](derivative, root, p)
                    row, _ = PROBES["leading_unit_row"](degree, points, norms, p, root, slope, squares)
                    basis = restrict(basis, (row & mask) << offset)
    return basis


def pair_parts(basis, field_masks):
    pair_bases = []
    for left, right in PAIRS:
        other = next(i for i in range(3) if i not in (left, right))
        pair_bases.append(GRID["eliminate"]([word & field_masks[other] for word in basis], basis))
    return pair_bases


def independent_after(known, candidates):
    pivots, accepted = {}, []
    for tagged, words in ((False, known), (True, candidates)):
        for original in words:
            word = original
            while word.bit_length() in pivots:
                word ^= pivots[word.bit_length()]
            if word:
                pivots[word.bit_length()] = word
                if tagged:
                    accepted.append(original)
    return len(pivots)-len(accepted), accepted


def roots(n, m, fields, derivatives, blocks, word, deadline):
    half, residues = set(), []
    normalization = 1
    supports = []
    for field, derivative, (offset, points) in zip(fields, derivatives, blocks, strict=True):
        slots = (word >> offset) & ((1 << len(points))-1)
        selected = [points[j] for j in GRID["support"](slots)]
        supports.append(selected)
        value = [1]+[0]*(len(field)-2)
        for a, b in selected:
            SQUARES["check_deadline"](deadline)
            value = SQUARES["multiply_mark"](field, value, a, b)
            if (a, b) in half:
                normalization = normalization*(a-b*m) % n
                half.remove((a, b))
            else:
                half.add((a, b))
        square = SQUARES["square_numerator"](field, value, deadline=deadline)
        if square is None:
            return None
        residue = SQUARES["evaluate"](square, m)*pow(derivative, -1, n) % n
        assert residue**2 % n == prod((a-b*m) % n for a, b in selected) % n
        residues.append(residue)
    assert not half
    ratio = prod(residues)*pow(normalization, -1, n) % n
    assert ratio**2 % n == 1
    divisor = gcd(ratio-1, n)
    summary = dict(sizes=list(map(len, supports)), ratio=ratio, divisor=divisor)
    certificate = dict(n=n, m=m, degree=len(fields[0])-1, fields=fields, points=supports,
                       residues=residues, normalization=normalization, ratio=ratio,
                       divisor=divisor, cofactor=n//divisor) if 1 < divisor < n else None
    return summary, certificate


def case(n, height, library, query_cap, time_cap):
    start = monotonic()
    m, fields, derivatives, discriminants = library
    collected = [COLLECT(n, m, (field,), disc, 2*height**2, height=height,
                         include_ramified_two=True, mark_local=True)
                 for field, disc in zip(fields, discriminants, strict=True)]
    variables, ideal_basis = rank_core(collected)
    blocks, field_masks = [], []
    offset = 0
    for i in range(3):
        points = [point for index, point in variables if index == i]
        blocks.append((offset, points))
        field_masks.append(((1 << len(points))-1) << offset)
        offset += len(points)
    assert all(i == index for i, (offset, points) in enumerate(blocks)
               for index, _ in variables[offset:offset+len(points)])
    probed = probe(fields, discriminants, blocks, ideal_basis)
    pairs_before = pair_parts(ideal_basis, field_masks)
    pairs_after = pair_parts(probed, field_masks)
    pair_dimension, mixed = independent_after([word for pair in pairs_after for word in pair], probed)
    exact, attempts, certificate = [], 0, None
    deadline = monotonic()+time_cap
    for word in sorted(mixed, key=int.bit_count)[:query_cap]:
        try:
            result = roots(n, m, fields, derivatives, blocks, word, deadline)
        except TimeoutExpired:
            exact.append("time-cap")
            break
        attempts += 1
        if result is None:
            exact.append(None)
            continue
        summary, certificate = result
        exact.append(summary)
        if certificate:
            certificate["height"] = height
            break
    status = ("mixed-square-split" if certificate else "no-mixed-survivors" if not mixed
              else "time-cap" if exact and exact[-1] == "time-cap"
              else "no-productive-candidate")
    return dict(n=n, m=m, height=height, status=status, columns=list(map(len, collected)),
                core=[len(points) for _, points in blocks], ideal=len(ideal_basis),
                probed=len(probed), pair_ideal=list(map(len, pairs_before)),
                pair_probed=list(map(len, pairs_after)), pair_span=pair_dimension,
                genuinely_mixed=len(mixed), attempts=attempts, exact=exact, certificate=certificate,
                seconds=round(monotonic()-start, 4))


def search(n, height=256, *, query_cap=QUERY_CAP, time_cap=EXACT_SECONDS):
    """Search a public input using the scheduled pair and one cubic-side shift."""
    if n < 9 or n % 2 == 0 or height < 1 or query_cap < 0 or time_cap < 0:
        raise ValueError("require odd N >= 9 and positive height with nonnegative query limits")
    library = field_library(n)
    if isinstance(library, dict):
        return dict(library, height=height, certificate=None)
    return case(n, height, library, query_cap, time_cap)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="?", help="public input for a single search")
    parser.add_argument("--height", type=int, default=256, help="grid height for a single input")
    parser.add_argument("--certificate-file", type=Path, help="save full JSON certificates here")
    args = parser.parse_args()
    certificates = []
    cases = [(args.n, args.height)] if args.n is not None else [
        (n, height) for n in INPUTS for height in HEIGHTS
    ]
    for n, height in cases:
        result = search(n, height)
        certificate = result.pop("certificate")
        if certificate:
            certificates.append(certificate)
        print(json.dumps(result), flush=True)
    if args.certificate_file is not None:
        args.certificate_file.write_text(json.dumps(certificates, separators=(",", ":"))+"\n")


if __name__ == "__main__":
    main()
