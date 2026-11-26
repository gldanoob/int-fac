"""Exact common-sign constraints for products at the real embeddings of a monic pair."""

from functools import reduce
from math import gcd
import os
from pathlib import Path
import runpy
import subprocess


def multiply(f, g):
    h = [0] * (len(f) + len(g) - 1)
    for i, v in enumerate(f):
        for j, w in enumerate(g):
            h[i + j] += v * w
    return h


def sturm(f):
    chain = [f, [i * v for i, v in enumerate(f) if i]]
    while len(chain[-1]) > 1:
        divisor = chain[-1]
        r = chain[-2].copy()
        while len(r) >= len(divisor):
            shift = len(r) - len(divisor)
            factor = r[-1] if divisor[-1] > 0 else -r[-1]
            r = [v * abs(divisor[-1]) for v in r]
            for i, v in enumerate(divisor):
                r[i + shift] -= factor * v
            while r and r[-1] == 0:
                r.pop()
        if not r:
            raise ValueError("repeated root in the defining product")
        content = reduce(gcd, r, 0)
        chain.append([-v // content for v in r])
    return chain


def variations(values):
    signs = [v > 0 for v in values if v]
    return sum(x != y for x, y in zip(signs, signs[1:]))


def homogeneous(poly, a, b):
    value, scale = poly[-1], 1
    for coefficient in reversed(poly[:-1]):
        scale *= b
        value = a * value + coefficient * scale
    return value


def real_gaps(f, g, cuts):
    chain = sturm(multiply(f, g))
    left = variations(row[-1] * (-1)**(len(row)-1) for row in chain)
    roots = left - variations(row[-1] for row in chain)
    bins = []
    for a, b in cuts:
        if b <= 0:
            raise ValueError("positive denominators required")
        vals = [homogeneous(row, a, b) for row in chain]
        if not vals[0]:
            raise ValueError("cut lies on a defining root")
        bins.append(left - variations(vals))
    return roots, bins


def run():
    pair = runpy.run_path(str(Path(__file__).with_name("cogentic-monic-pair.py")))["monic_pair"]
    cuts = [(a, b) for b in range(1, 9) for a in range(-12, 13) if gcd(a, b) == 1]
    gp = []
    expected = []
    interior = 0
    for n in (35, 77, 143, 221, 323, 895):
        _, f, g = pair(n, 3)
        roots, bins = real_gaps(f, g, cuts)
        interior += sum(0 < j < roots for j in bins)
        if n == 323:
            assert 0 < bins[cuts.index((-1, 2))] < roots
        h = multiply(f, g)
        gp.append(f"h=Polrev({h}); print(polsturm(h));")
        expected.append(roots)
        for (a, b), zone in zip(cuts, bins):
            gp.append(f"print(polsturm(h,[-oo,{a}/{b}]));")
            expected.append(zone)
        # For each subset of these cuts, compare gap parity with direct signs
        # on the ordered embeddings. Repeated cuts and both tails are covered.
        probes = [min(bins), max(bins), *sorted(set(bins)), bins[cuts.index((-1, 2))]]
        for mask in range(1 << len(probes)):
            used = [z for i, z in enumerate(probes) if mask >> i & 1]
            signs = [sum(z < j for z in used) % 2 for j in range(1, roots + 1)]
            assert (len(set(signs)) <= 1) == all(used.count(z) % 2 == 0 for z in range(1, roots))
    result = subprocess.run([os.environ.get("GP", "gp"), "-fq"], input="\n".join(gp) + "\n",
                            capture_output=True, text=True, check=True, timeout=20)
    if result.stderr or [int(x) for x in result.stdout.splitlines()] != expected:
        raise AssertionError("independent PARI root counts disagree: " + result.stderr)
    print(f"{len(expected)} exact root counts checked; {interior} cuts in bounded real gaps")


if __name__ == "__main__":
    run()
