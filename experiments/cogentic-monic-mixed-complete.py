"""Decide the full signed primitive-grid split question for shared-root fields."""

import argparse
import json
import os
from collections import Counter
from fractions import Fraction
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path
from shutil import which
from time import monotonic


HERE = Path(__file__).resolve().parent
MIXED = run_path(str(HERE / "cogentic-monic-mixed-grid.py"))
GRID, PROBES, SQUARES = (MIXED[name] for name in ("GRID", "PROBES", "SQUARES"))
COMPLETE = MIXED["DRIVER"]["complete_basis"]
QUADRATIC = run_path(str(HERE / "cogentic-quadratic-square-kernel.py"))


def scheduled_fields(n):
    m, f, g = GRID["CHECK_PAIR"](n, MIXED["SCHEDULED_DEGREE"](n))
    return m, (f, g, (g[0]-4*m, g[1]+4, *g[2:]))


def centered_fields(n):
    build = run_path(str(HERE / "cogentic-selected-polynomial-recenter.py"))["centered_pair"]
    slopes, constants, _ = build(n)
    return isqrt(n), tuple((b, a, 1) for a, b in zip(slopes, constants, strict=True))


def parity_space(n, m, fields, height):
    collect = run_path(str(HERE / "cogentic-monic-exact-grid.py"))["collect"]
    cutoff = max(2*height**2, 2*max(len(field)-1 for field in fields))
    columns, variables, sizes = [], [], []
    for i, field in enumerate(fields):
        marks = list(collect(n, m, (field,), cutoff, height=height))
        sizes.append(len(marks))
        for point, rows in marks:
            variables.append((i, point))
            columns.append([(0, *point), *((i+1, p, root) for _, p, root in rows)])
        variables.append((i, None))
        columns.append([(0, 0, 0)])  # Every primitive mark has b > 0.
    core, basis = GRID["parity_basis"](columns)
    variables = [variables[j] for j in core]
    blocks, offset = [], 0
    for i in range(len(fields)):
        points = [point for index, point in variables if index == i and point is not None]
        assert variables[offset+len(points)] == (i, None)
        blocks.append((offset, points))
        offset += len(points)+1
    return blocks, basis, sizes


def quadratic_space(n, m, fields, height):
    points = [(a, b) for a in range(-height, height+1) for b in range(1, height+1)
              if gcd(a, b) == gcd(a-b*m, n) == 1]
    blocks, incidence, local_masks = [], [], []
    field_masks = run_path(str(HERE / "cogentic-quadratic-supported-kernel.py"))["grid_square_masks"]
    packed_roots = height >= 16 and which(os.environ.get("GP", "gp")) is not None
    for i, field in enumerate(fields):
        offset = i*(len(points)+1)
        blocks.append((offset, points))
        for mask in field_masks(field, points, height, packed_roots=packed_roots):
            incidence.append(mask)
            local_masks.append(mask << offset)
    return blocks, GRID["eliminate"](incidence, local_masks), [len(points)]*len(fields)


def quadratic_numerator(field, value):
    constant, linear, _ = field
    d = linear**2-4*constant
    radical = Fraction(value[1], 2)
    element = (value[0]-linear*radical, radical)
    root = QUADRATIC["square_root"](d, element)
    if root is None:
        return None
    if QUADRATIC["multiply"](d, root, root) != element:
        raise ArithmeticError("invalid quadratic square root")
    x, y = root
    # Multiplication by P'(alpha) = sqrt(d) clears the power-basis denominators.
    cleared = (d*y+linear*x, 2*x)
    assert all(c.denominator == 1 for c in cleared)
    return [int(c) for c in cleared]


def probe_rounds(fields, blocks):
    cursor, last_prime = 1, 0
    data = [
        (field, [j*c for j, c in enumerate(field) if j],
         offset, points, [GRID["homogeneous"](field, *point) for point in points])
        for field, (offset, points) in zip(fields, blocks, strict=True)
    ]

    def restrict(basis, cutoff):
        nonlocal cursor, last_prime
        for p in GRID["primes_through"](cutoff):
            if not basis:
                break
            if p <= max(2, cursor):
                continue
            last_prime = p
            squares = {r*r % p for r in range(1, p)}
            for field, derivative, offset, points, norms in data:
                for root in range(p):
                    if GRID["polynomial"](field, root, p):
                        continue
                    slope = GRID["polynomial"](derivative, root, p)
                    if slope:
                        row, _ = PROBES["leading_unit_row"](len(field)-1, points, norms,
                                                            p, root, slope, squares)
                        basis = MIXED["restrict"](basis, row << offset)
        cursor = cutoff
        return basis, dict(last_prime=last_prime)

    return restrict


def exact_query(n, m, fields, derivatives, blocks, word, *, quadratics=False):
    counts, signs, supports, residues = Counter(), [], [], []
    for field, derivative, (offset, points) in zip(fields, derivatives, blocks, strict=True):
        mask = word >> offset
        selected = [points[j] for j in GRID["support"](mask & ((1 << len(points))-1))]
        negative = (mask >> len(points)) & 1
        sign = 1-2*negative
        signs.append(sign)
        supports.append(selected)
        counts.update(selected)
        value = [sign]+[0]*(len(field)-2)
        for a, b in selected:
            value = SQUARES["multiply_mark"](field, value, a, b)
        root = quadratic_numerator(field, value) if quadratics else SQUARES["square_numerator"](field, value)
        if root is None:
            return None
        residue = SQUARES["evaluate"](root, m)*pow(derivative, -1, n) % n
        assert residue**2 % n == sign*prod((a-b*m) % n for a, b in selected) % n
        residues.append(residue)
    negatives = signs.count(-1)
    assert negatives % 2 == 0 and all(count % 2 == 0 for count in counts.values())
    normalization = (-1)**(negatives//2)
    for (a, b), count in counts.items():
        normalization = normalization*pow(a-b*m, count//2, n) % n
    normalization %= n
    product = prod(residues) % n
    ratio = product*pow(normalization, -1, n) % n
    assert ratio*ratio % n == 1
    return product, normalization, ratio, signs, supports, residues


def search(n, m, fields, height, *, query_cap=None, stop_at_split=True):
    """Decide a connected grid of quadratic fields or monic Eisenstein fields."""
    start = monotonic()
    fields = tuple(tuple(field) for field in fields)
    if n <= 1 or n % 2 == 0 or height < 1 or len(fields) < 2:
        raise ValueError("require odd N > 1, positive height and at least two fields")
    quadratics = all(len(field) == 3 for field in fields)
    for field in fields:
        if len(field) < 3 or field[-1] != 1 or SQUARES["evaluate"](field, m) % n:
            raise ValueError("require monic polynomials of degree at least two with a shared root")
        if not quadratics and (field[0] % 4 != 2 or any(c % 2 for c in field[:-1])):
            raise ValueError("higher-degree libraries require Eisenstein polynomials at two")
    derivatives = [SQUARES["evaluate"]([j*c for j, c in enumerate(field) if j], m)
                   for field in fields]
    gcds = [gcd(derivative, n) for derivative in derivatives]
    if any(value != 1 for value in gcds):
        divisor = next((g for g in gcds if 1 < g < n), None)
        return dict(n=n, m=m, height=height, status="derivative-split" if divisor else "nonunit-derivative",
                    derivative_gcds=gcds, divisor=divisor, certificate=None)
    if query_cap is not None and query_cap < 0:
        raise ValueError("the exact query cap must be nonnegative")
    if quadratics:
        blocks, initial, sizes = quadratic_space(n, m, fields, height)
        def restrict(basis, _):
            return basis, {"last_prime": 0}
    else:
        blocks, initial, sizes = parity_space(n, m, fields, height)
        restrict = probe_rounds(fields, blocks)
    certificate = None

    def query(word):
        nonlocal certificate
        witness = exact_query(n, m, fields, derivatives, blocks, word, quadratics=quadratics)
        if witness is None:
            if quadratics:
                raise ArithmeticError("nonsquare mask in the quadratic kernel")
            return None
        product, normalization, ratio, signs, supports, residues = witness
        divisor = gcd(product-normalization, n)
        if certificate is None and 1 < divisor < n:
            certificate = dict(n=n, m=m, fields=fields, height=height, signs=signs,
                               points=supports, residues=residues, normalization=normalization,
                               ratio=ratio, divisor=divisor, cofactor=n//divisor)
        return product, normalization

    status, queries, basis, survivors, last_prime = COMPLETE(
        initial, restrict, query, query_cap, n if stop_at_split else None)
    if status == "complete":
        status = "complete-split" if certificate else "complete-no-split"
    return dict(n=n, m=m, height=height, status=status, columns=sizes,
                method="quadratic-descent" if quadratics else "ideal-parity-and-probes",
                ideal=None if quadratics else len(initial),
                surviving=len(survivors), square_basis=len(basis), tests=queries,
                last_prime=last_prime, certificate=certificate, seconds=round(monotonic()-start, 4))


def fixtures():
    for n, height, split in ((895, 20, True), (247, 2, False)):
        m, fields = scheduled_fields(n)
        result = search(n, m, fields, height, stop_at_split=False)
        assert result["status"] == ("complete-split" if split else "complete-no-split")
        assert result["surviving"] == result["square_basis"]
        print(json.dumps(result))
    signed = search(65, 9, ((2, -2, 1), (82, 18, 1), (-70, 6, 1)), 1, stop_at_split=False)
    certificate = signed["certificate"]
    assert signed["status"] == "complete-split" and signed["square_basis"] == 1
    assert certificate["signs"] == [-1, -1, 1] and certificate["normalization"] == 64
    assert not any(certificate["points"]) and certificate["divisor"] in (5, 13)
    print(json.dumps(signed))
    blocks = [(2*i, [(3, 2)]) for i in range(4)]
    word = sum(1 << offset for offset, _ in blocks)
    _, normalization, ratio, _, _, _ = exact_query(79, 9, ((-2, 0, 1),)*4, (18,)*4, blocks, word)
    assert normalization == (3-2*9)**2 % 79 and ratio in (1, 78)
    for n, expected_dimension, split in ((77, 5, True), (187, 2, False)):
        m, fields = centered_fields(n)
        result = search(n, m, fields, 12, stop_at_split=False)
        assert result["method"] == "quadratic-descent" and result["last_prime"] == 0
        assert result["square_basis"] == expected_dimension
        assert result["status"] == ("complete-split" if split else "complete-no-split")
        if split:
            assert result["certificate"]["divisor"] in (7, 11)
        print(f"{n}: quadratic square dimension {expected_dimension}, {result['status']}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="?")
    parser.add_argument("--height", type=int, default=20)
    parser.add_argument("--queries", type=int)
    parser.add_argument("--basis", action="store_true", help="certify a full basis even after a split")
    parser.add_argument("--quadratic", action="store_true", help="use the two near-square fields and rational norm descent")
    args = parser.parse_args()
    if args.n is None:
        fixtures()
        return
    if args.quadratic:
        if args.n < 3 or args.n % 2 == 0:
            parser.error("the centered quadratic grid requires an odd input of at least 3")
        root = isqrt(args.n)
        if root*root == args.n:
            print(json.dumps(dict(n=args.n, status="perfect-square", divisor=root)))
            return
        m, fields = centered_fields(args.n)
    else:
        m, fields = scheduled_fields(args.n)
    print(json.dumps(search(args.n, m, fields, args.height, query_cap=args.queries,
                            stop_at_split=not args.basis)))


if __name__ == "__main__":
    main()
