"""Replay the exact height-six cover in cubic-biquadratic-cover-h6.json."""

from collections import defaultdict
from functools import lru_cache
from itertools import combinations, product
import json
from math import prod
from pathlib import Path
from runpy import run_path

ANCHOR = frozenset({-1, 3})


def sign_rows(classes, branch, fixed):
    rows = []
    for squareclass in classes:
        scope = squareclass ^ ANCHOR if 3 in squareclass else squareclass
        offset = branch * int(3 in squareclass) + sum(fixed[p] for p in scope & fixed.keys())
        rows.append((tuple(sorted(scope - fixed.keys())), offset % 2))
    return rows


def factors(rows, weights):
    return [(scope, {bits: weight * int((sum(bits) + offset) % 2 == 0)
                     for bits in product((0, 1), repeat=len(scope))})
            for (scope, offset), weight in zip(rows, weights, strict=True)]


def variables(rows):
    return {p for scope, _ in rows for p in scope}


def compatible(rows, triangle):
    pivots = {}
    for i in triangle:
        scope, bit = rows[i]
        row = set(scope)
        while row and max(row) in pivots:
            other, other_bit = pivots[max(row)]
            row ^= other
            bit ^= other_bit
        if row:
            pivots[max(row)] = row, bit
        elif bit:
            return False
    return True


def slack_tables(rows, weights, relevant):
    """Eliminate signs, retaining both cost increases on the relevant signs."""
    terms = factors(rows, weights)
    remaining = variables(rows)
    archive = []
    while remaining:
        def neighbors(p):
            return set().union(*(s for s, _ in terms if p in s)) - {p}

        v = min(remaining, key=lambda p: (p in relevant, len(neighbors(p)), -p))
        scope = tuple(sorted(neighbors(v)))
        bucket = [(s, f) for s, f in terms if v in s]
        table, excess = {}, {}
        for bits in product((0, 1), repeat=len(scope)):
            assignment = dict(zip(scope, bits))
            costs = []
            for bit in (0, 1):
                assignment[v] = bit
                costs.append(sum(f[tuple(assignment[p] for p in s)] for s, f in bucket))
            table[bits] = min(costs)
            excess[bits] = tuple(cost - table[bits] for cost in costs)
        if v in relevant:
            assert set(scope) <= relevant
            archive.append((v, scope, excess))
        terms = [(s, f) for s, f in terms if v not in s] + [(scope, table)]
        remaining.remove(v)
    assert all(not s for s, _ in terms)
    return sum(f[()] for _, f in terms), archive


def prove_lower(rows, triangles, weights, denominator, target):
    """Reject every sign profile whose cover objective could reach target."""
    triangles = [t for t in triangles if compatible(rows, t)]
    vertices = sorted({i for t in triangles for i in t})
    relevant = variables(rows[i] for i in vertices)
    vertex_set = set(vertices)
    # Only eligible vertices need retain weights; the others affect just the count.
    lam = [w if i in vertex_set else 0 for i, w in enumerate(weights)]
    minimum, archive = slack_tables(rows, [denominator - w for w in lam], relevant)
    triangle_masks = [sum(1 << i for i in t) for t in triangles]
    incident = defaultdict(list)
    for t, mask in zip(triangles, triangle_masks, strict=True):
        for i in t:
            incident[1 << i].append(mask)

    @lru_cache(maxsize=60_000)
    def matching(available):
        if not available:
            return 0
        first = available & -available
        best = matching(available ^ first)
        for tri in incident[first]:
            if tri & available == tri:
                best = max(best, 1 + matching(available ^ tri))
        return best

    assignment = {}
    leaves = 0
    cap = target * denominator

    def visit(step, slack):
        nonlocal leaves
        if step >= 0:
            v, scope, excess = archive[step]
            for bit, cost in enumerate(excess[tuple(assignment[p] for p in scope)]):
                if cost <= slack:
                    assignment[v] = bit
                    visit(step - 1, slack - cost)
            return

        leaves += 1
        active = [i for i in vertices
                  if (sum(assignment[p] for p in rows[i][0]) + rows[i][1]) % 2 == 0]
        # Branch-cost increases telescope; adding back active lambda recovers Q*n.
        n, remainder = divmod(cap - slack + sum(lam[i] for i in active), denominator)
        assert remainder == 0
        needed = n - target
        if needed <= 0:
            raise AssertionError(f"smaller cover found at objective {n}")
        if 3 * needed > n:
            return
        mask = sum(1 << i for i in active)
        available = 0
        for tri in triangle_masks:
            if tri & mask == tri:
                available |= tri
        if available.bit_count() >= 3 * needed and matching(available) >= needed:
            raise AssertionError(f"smaller cover found at objective {n - matching(available)}")

    if minimum <= cap:
        visit(len(archive) - 1, cap - minimum)
    return leaves


def check(classes, api, denominator, certificate):
    residue, cover = certificate["residue"], certificate["cover"]
    branch = int(residue == 2)
    target = 2 * (cover - 1)
    fixed = {int(p): bit for p, bit in certificate["fixed"].items()}
    assert all(p != 3 and bit in (0, 1) for p, bit in fixed.items())
    discriminants = [n if n % 4 == 1 else 4 * n for n in map(prod, classes)]
    indices = {d: i for i, d in enumerate(discriminants)}
    classes_index = {s: i for i, s in enumerate(classes)}
    weights = [0] * len(classes)
    for d, weight in certificate["weights"].items():
        assert type(weight) is int and 0 <= weight <= denominator
        weights[indices[int(d)]] = weight
    triples = [(i, j, classes_index[x ^ y])
               for (i, x), (j, y) in combinations(enumerate(classes), 2)
               if classes_index.get(x ^ y, -1) > j]
    rows = sign_rows(classes, branch, {})
    triples = [t for t in triples if compatible(rows, t)]
    assert all(sum(weights[i] for i in t) >= denominator for t in triples)

    negative = set(certificate["negative_signs"])
    assert negative <= variables(rows)
    active = {i for i, (scope, offset) in enumerate(rows)
              if (sum(p in negative for p in scope) + offset) % 2 == 0}
    packed = [tuple(indices[d] for d in t) for t in certificate["packing"]]
    covered = [i for t in packed for i in t]
    assert len(covered) == len(set(covered)) and set(covered) <= active
    assert all(len(t) == 3 and tuple(sorted(t)) in triples for t in packed)
    upper = len(active) - len(packed)
    assert (upper + 1) // 2 == cover

    for p, bit in fixed.items():
        assert p in variables(rows)
        other = sign_rows(classes, branch, {p: 1 - bit})
        terms = factors(other, [denominator - w for w in weights])
        costs, _ = api["eliminate"](terms, variables(other), api["merge_counts"])
        assert sum(costs) > target * denominator

    leaves = prove_lower(sign_rows(classes, branch, fixed), triples, weights, denominator, target)
    print(f"H=6 p mod 3={residue}: cover={cover}; objective {target + 1}–{upper}; "
          f"{leaves} profiles exhausted")


def main():
    if not __debug__:
        raise RuntimeError("Run without -O so the certificate checks are enabled")
    here = Path(__file__).resolve()
    api = run_path(str(here.with_name("cubic-resolvent-profiles.py")))
    cert = json.loads(here.with_suffix(".json").read_text())
    assert cert["height"] == 6
    assert type(cert["denominator"]) is int and cert["denominator"] > 0
    assert {branch["residue"] for branch in cert["branches"]} == {1, 2}
    classes = api["box_classes"](cert["height"])
    for branch in cert["branches"]:
        check(classes, api, cert["denominator"], branch)


if __name__ == "__main__":
    main()
