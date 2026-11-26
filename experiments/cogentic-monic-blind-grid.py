"""Frozen-input blind benchmark using the existing monic square interfaces."""

import argparse
import json
from math import gcd, prod
from pathlib import Path
from random import Random
from runpy import run_path
from time import monotonic

HERE = Path(__file__).resolve().parent
DRIVER = run_path(str(HERE / "cogentic-monic-kernel-driver.py"))
GRID = DRIVER["GRID"]
PREFILTER = run_path(str(HERE / "cogentic-monic-square-probes.py"))["prefilter"]
INPUTS = (341854927, 824552227, 647911657, 641626049, 310556537,
          449508911, 2363084519, 929070139, 516173501, 422536969)
HEIGHT, PROBE_CAP, QUERY_CAP, CASE_SECONDS = 64, 257, 32, 5
SCALING_HEIGHTS = (128, 256)


def solve(n, height, primes, cutoff, collect):
    m, f, g = GRID["CHECK_PAIR"](n, 3)
    repaired = DRIVER["REPAIR"](n, m, f, g)
    if isinstance(repaired, int):
        return dict(n=n, height=height, status="derivative-gcd", divisor=repaired, factors=[])
    shift, fields = repaired
    f, g = map(list, fields)
    disc = int(DRIVER["gp_value"](f"poldisc(Polrev({f}))*poldisc(Polrev({g}))", CASE_SECONDS))
    marks = collect(n, m, fields, disc, primes, cutoff, height)
    columns = GRID["parity_words"]([small + large for _, small, large, _ in marks])
    parity = GRID["eliminate"](columns, (1 << j for j in range(len(marks))))
    assert all(GRID["combine"](word, columns) == 0 for word in parity)
    sign_bit, decode, query = DRIVER["exact_oracle"](n, m, fields, marks, CASE_SECONDS)
    surviving, stats = PREFILTER(fields, [point for point, _, _, _ in marks], [sign_bit, *parity], disc,
                                 prime_cutoff=PROBE_CAP)
    status, tests, rank, basis = DRIVER["adaptive"](surviving, query, QUERY_CAP)
    if status == "complete":
        assert len(basis) + rank == len(surviving)
    factors = []
    for word, (left, right) in basis:
        assert GRID["combine"](word & ~sign_bit, columns) == 0
        sign, points = decode(word)
        common = sign * prod(a-b*m for a, b in points) % n
        assert gcd(common, n) == 1 and left**2 % n == right**2 % n == common
        divisor = gcd(left-right, n)
        if 1 < divisor < n:
            assert n % divisor == 0
            factors.append(dict(divisor=divisor, points=points, sign=sign, residues=[left, right], square=common))
    return dict(n=n, height=height, m=m, shift=shift, status=status, columns=len(marks),
                smooth=sum(smooth for _, _, _, smooth in marks), parity=len(parity),
                signed=len(parity)+1, probes=stats["probes"], surviving=len(surviving),
                tests=tests, basis=len(basis), factors=factors)


def validate(batches):
    # Run after solving every public integer. Only this phase sees the fixture factors.
    primes = [p for p in GRID["primes_through"](50000) if p >= 9000]
    factors = Random(20261127).sample(primes, 2*len(INPUTS))
    for height, results in batches:
        for i, result in enumerate(results):
            p, q = factors[2*i:2*i+2]
            assert p*q == result["n"] == INPUTS[i] and min(p, q) > height
            if result["status"] == "derivative-gcd":
                assert result["divisor"] in (p, q)
            assert all(certificate["divisor"] in (p, q) for certificate in result["factors"])
        print(json.dumps(dict(height=height, validated=len(results), prime_range=[min(factors), max(factors)],
                              square_splits=sum(bool(result["factors"]) for result in results))))


def original_collect(n, m, fields, disc, primes, cutoff, height):
    return GRID["relations"](n, m, fields, disc, primes, cutoff, complete_parity=True,
                             height=height, include_ramified_two=True, mark_local=True)


def benchmark(heights, collect):
    batches = []
    for height in heights:
        cutoff = max(GRID["BASE"], 2*height**2)
        primes = tuple(GRID["primes_through"](cutoff))
        results = []
        for n in INPUTS:
            start = monotonic()
            result = solve(n, height, primes, cutoff, collect)
            result["seconds"] = round(monotonic()-start, 4)
            print(json.dumps(result), flush=True)
            results.append(result)
        batches.append((height, results))
    validate(batches)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scale", action="store_true", help="run the two frozen packed scaling grids")
    if parser.parse_args().scale:
        packed = run_path(str(HERE / "cogentic-monic-lattice-sieve.py"))["collect"]

        def packed_collect(n, m, fields, disc, _primes, cutoff, height):
            return packed(n, m, fields, disc, cutoff, height=height,
                          include_ramified_two=True, mark_local=True)

        benchmark(SCALING_HEIGHTS, packed_collect)
    else:
        benchmark((HEIGHT,), original_collect)
