"""Compose full grid parity, adaptive exact squares, and basis gcd extraction."""

import argparse
from ast import literal_eval
import json
from math import gcd, prod
from pathlib import Path
from runpy import run_path
from subprocess import TimeoutExpired
import sys
from time import monotonic


HERE = Path(__file__).resolve().parent
GRID = run_path(str(HERE / "cogentic-monic-large-primes.py"))
REPAIR = run_path(str(HERE / "cogentic-monic-index.py"))["repair"]
PAIR = run_path(str(HERE / "cogentic-monic-pair.py"))
INPUTS = (35, 77, 143, 221, 323, *GRID["INPUTS"])
QUERY_CAP = 128
CASE_SECONDS = 5


class GPStackLimit(Exception):
    """PARI exhausted its arithmetic stack in this query."""


def gp_value(expression, timeout, setup=""):
    code = (setup + f'iferr(print({expression}),err,if(errname(err)=="e_STACK",'
            'print("stack-cap"),print(err);quit(1)));\n')
    line, = GRID["gp"](code, timeout=timeout)
    if line == "stack-cap":
        raise GPStackLimit
    return line


def adaptive(parity_basis, oracle, query_cap=QUERY_CAP, split_modulus=None):
    pivots, square_basis, tests = [], [], 0
    for word in parity_basis:
        for selection in range(1 << len(pivots)):
            if tests == query_cap:
                return "query-cap", tests, len(pivots), square_basis
            candidate = word ^ GRID["combine"](selection, pivots)
            try:
                roots = oracle(candidate)
            except TimeoutExpired:
                return "time-cap", tests, len(pivots), square_basis
            except GPStackLimit:
                return "stack-cap", tests, len(pivots), square_basis
            tests += 1
            if roots:
                square_basis.append((candidate, roots))
                if split_modulus is not None and 1 < gcd(roots[0]-roots[1], split_modulus) < split_modulus:
                    return "first-square-split", tests, len(pivots), square_basis
                break
        else:
            pivots.append(word)
    return "complete", tests, len(pivots), square_basis


def exact_oracle(n, m, fields, marks, time_cap=CASE_SECONDS, *, dyadic=False):
    deadline = monotonic() + time_cap if time_cap is not None else None
    sign_bit = 1 << len(marks)
    coefficients = [list(p) for p in fields]
    local_roots = run_path(str(HERE / "cogentic-monic-dyadic-ascent.py"))["joint_roots"] if dyadic else None

    def decode(word):
        points = [list(marks[j][0]) for j in GRID["support"](word & ~sign_bit)]
        return (-1 if word & sign_bit else 1), points

    def query(word):
        sign, points = decode(word)
        if local_roots is not None:
            return local_roots(n, m, fields, points, sign, deadline=deadline)
        seconds = deadline - monotonic() if deadline is not None else None
        if seconds is not None and seconds <= 0:
            raise TimeoutExpired("GP exact square oracle", time_cap)
        expr = f'kernel_roots({n},{m},apply(Polrev,{coefficients}),{points},{sign})'
        return literal_eval(gp_value(expr, seconds, 'read("cogentic-monic-kernel-driver.gp");\n'))

    return sign_bit, decode, query


def complete_basis(signed, restrict, query, query_cap, split_modulus=None, deadline=None):
    """Grow the probe bound until every surviving basis vector has exact roots."""
    roots = {}
    cutoff = 3
    last_prime = 0

    def partial(status):
        pivots, witnesses = {}, []
        for mask, pair in roots.items():
            if pair is None:
                continue
            word = mask
            while word and word.bit_length() in pivots:
                word ^= pivots[word.bit_length()]
            if word:
                pivots[word.bit_length()] = word
                witnesses.append((mask, pair))
        return status, len(roots), witnesses, signed, last_prime

    while True:
        if deadline is not None and monotonic() >= deadline:
            return partial("time-cap")
        try:
            signed, stats = restrict(signed, cutoff)
        except TimeoutExpired:
            return partial("time-cap")
        last_prime = stats["last_prime"]
        squares = []
        for word in signed:
            if word not in roots:
                if query_cap is not None and len(roots) == query_cap:
                    return partial("query-cap")
                try:
                    roots[word] = query(word)
                except TimeoutExpired:
                    return partial("time-cap")
            pair = roots[word]
            if pair is None:
                break
            squares.append((word, pair))
            if split_modulus is not None and 1 < gcd(pair[0]-pair[1], split_modulus) < split_modulus:
                return "first-square-split", len(roots), squares, signed, last_prime
        else:
            return "complete", len(roots), squares, signed, last_prime
        cutoff *= 2


def replay(n, m, shift, fields, primes, cutoff, *, height=GRID["HEIGHT"],
           query_cap=QUERY_CAP, time_cap=CASE_SECONDS, ramified_two=False,
           mark_local=False, probe_cutoff=0, stop_at_factor=False, all_ideals=False, dyadic=False):
    discriminant = None
    if all_ideals:
        exact_collect = run_path(str(HERE / "cogentic-monic-exact-grid.py"))["collect"]
        marks = list(exact_collect(n, m, fields, cutoff, height=height))
        rows = [part for _, part in marks]
    else:
        left, right = map(list, fields)
        try:
            line = gp_value(f"poldisc(Polrev({left}))*poldisc(Polrev({right}))", time_cap)
        except TimeoutExpired:
            return dict(n=n, m=m, shift=shift, status="discriminant-time-cap", tests=0, factors=[])
        except GPStackLimit:
            return dict(n=n, m=m, shift=shift, status="discriminant-stack-cap", tests=0, factors=[])
        discriminant = int(line)
        if primes is None:
            collect = run_path(str(HERE / "cogentic-monic-lattice-sieve.py"))["collect"]
            marks = collect(n, m, fields, discriminant, cutoff, height=height,
                            include_ramified_two=ramified_two, mark_local=mark_local)
        else:
            marks = GRID["relations"](n, m, fields, discriminant, primes, cutoff, complete_parity=True,
                                      height=height, include_ramified_two=ramified_two, mark_local=mark_local)
        rows = [small + large for _, small, large, _ in marks]
    total_marks = len(marks)
    if height >= 128:
        core, parity_basis = GRID["parity_basis"](rows)
        marks = [marks[j] for j in core]
    else:
        columns = GRID["parity_words"](rows)
        parity_basis = GRID["eliminate"](columns, (1 << j for j in range(len(marks))))
        assert all(GRID["combine"](word, columns) == 0 for word in parity_basis)
    result = dict(n=n, m=m, shift=shift, columns=total_marks, parity=len(parity_basis))
    if not parity_basis and any((len(field)-1) % 2 for field in fields):
        return dict(result, status="zero-parity", tests=0, basis=0, factors=[])

    sign_bit, decode, query = exact_oracle(n, m, fields, marks, time_cap, dyadic=dyadic or all_ideals)
    signed = [sign_bit, *parity_basis]
    if probe_cutoff or all_ideals:
        prefilter = run_path(str(HERE / "cogentic-monic-square-probes.py"))["prefilter"]
        points = [entry[0] for entry in marks]
    if all_ideals:
        deadline = monotonic()+time_cap if time_cap is not None else None
        def restrict(masks, bound):
            return prefilter(fields, points, masks, prime_cutoff=bound, deadline=deadline)
        status, tests, square_basis, signed, last_prime = complete_basis(
            signed, restrict, query, query_cap, n if stop_at_factor else None, deadline)
        rank = 0 if status == "complete" else None
        result.update(probe_rank=1+len(parity_basis)-len(signed), survivors=len(signed), last_prime=last_prime)
    else:
        if probe_cutoff:
            signed, stats = prefilter(fields, points, signed, discriminant, prime_cutoff=probe_cutoff)
            result.update(probe_rank=stats["rank"], survivors=len(signed))
        status, tests, rank, square_basis = adaptive(signed, query, query_cap, n if stop_at_factor else None)
    if status == "complete":
        assert len(square_basis) + rank == len(signed)
        status = "kernel-trivial" if not square_basis else "basis-exhausted"
    factors = []
    for word, (a, b) in square_basis:
        sign, points = decode(word)
        common = sign * prod(x-y*m for x, y in points) % n
        assert gcd(common, n) == 1 and a*a % n == b*b % n == common
        divisor = gcd(a-b, n)
        if 1 < divisor < n:
            assert n % divisor == 0
            factors.append(dict(divisor=divisor, cofactor=n // divisor, sign=sign,
                                points=points, residues=[a, b], square=common))
    if factors and status == "basis-exhausted":
        status = "basis-split"
    return dict(result, status=status, tests=tests, rank=rank, basis=len(square_basis), factors=factors)


def fixtures():
    # Keep an earlier split if the next basis is reordered and the query cap is hit.
    def capped_probe(masks, bound):
        return (masks if bound == 3 else [4, 1]), {"last_prime": bound}
    capped = complete_basis([1, 2, 4], capped_probe, {1: (1, 4), 2: None}.__getitem__, 2)
    assert capped[:3] == ("query-cap", 2, [(1, (1, 4))])
    cutoff = max(GRID["BASE"], 2 * GRID["HEIGHT"]**2)
    primes = tuple(GRID["primes_through"](cutoff))
    outside = 8209
    assert outside > cutoff and all(outside % p for p in primes)
    assert GRID["factor_bounded"](17 * outside**2, primes, cutoff, True) == [(17, 1)]
    assert GRID["factor_bounded"](17 * outside**3, primes, cutoff, True) is None
    for n in INPUTS:
        m, f, g = GRID["CHECK_PAIR"](n, 3)
        fixed = REPAIR(n, m, f, g)
        if isinstance(fixed, int):
            assert 1 < fixed < n and n % fixed == 0
            print(dict(n=n, m=m, status="direct-derivative-gcd", divisor=fixed, cofactor=n // fixed))
        else:
            shift, fields = fixed
            print(replay(n, m, shift, fields, primes, cutoff))


def search(n, degree, height, query_cap, planted, relations_only, all_ideals=False):
    if n < 2 or degree < 2 or height < 1 or (query_cap is not None and query_cap < 0):
        raise ValueError("require N >= 2, degree >= 2, height >= 1, and a nonnegative query limit")
    if query_cap is None and not all_ideals:
        query_cap = QUERY_CAP
    def direct(stage, divisor):
        assert 1 < divisor < n and n % divisor == 0
        return dict(n=n, status=stage, divisor=divisor, cofactor=n // divisor)
    if n in (2, 3, 5, 7):
        return dict(n=n, status="prime")
    if n % 2 == 0:
        return direct("even", 2)
    if not relations_only:
        divisor = PAIR["perfect_power_divisor"](n)
        if divisor is not None:
            return direct("perfect-power", divisor)
    if planted:
        build = run_path(str(HERE / "cogentic-planted-norm-two.py"))["monic_plants"]
        fixed = build(n, degree)
        if isinstance(fixed, int):
            return direct("construction-gcd", fixed)
        m, cuts, f, g = fixed
        shift, fields = None, (f, g)
    else:
        m, f, g = GRID["CHECK_PAIR"](n, degree)
        fixed = REPAIR(n, m, f, g)
        if isinstance(fixed, int):
            return direct("direct-derivative-gcd", fixed)
        shift, fields = fixed
    if not relations_only:
        for a in range(-height, height+1):
            for b in range(1, height+1):
                if gcd(a, b) == 1:
                    divisor = gcd(a-b*m, n)
                    if 1 < divisor < n:
                        return direct("direct-mark-gcd", divisor)
    cutoff = max(GRID["BASE"], 2*height**2, 2*(len(fields[1])-1) if all_ideals else 0)
    # The root lattice repays its setup on larger boxes or wide input coefficients.
    primes = None if all_ideals or height >= 128 or n.bit_length() >= 255 else tuple(GRID["primes_through"](cutoff))
    result = replay(n, m, shift, fields, primes, cutoff, height=height, query_cap=query_cap,
                    time_cap=None, ramified_two=True, mark_local=True, probe_cutoff=257,
                    stop_at_factor=not relations_only, all_ideals=all_ideals, dyadic=True)
    if planted:
        result["planted_cuts"] = cuts
    return result


if __name__ == "__main__":
    # This local arithmetic CLI passes exact coefficients and discriminants to GP.
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", nargs="?", type=int, help="integer to split (omit for fixed replays)")
    parser.add_argument("--height", type=int, default=GRID["HEIGHT"], help="primitive box height")
    parser.add_argument("--degree", type=int, help="override the scheduled degree parameter")
    parser.add_argument("--queries", type=int, help="maximum joint square tests (default 128, unlimited with --all-ideals)")
    parser.add_argument("--planted", action="store_true", help="use the norm-two polynomial family")
    parser.add_argument("--relations-only", action="store_true", help="skip preliminary mark gcd splits")
    parser.add_argument("--all-ideals", action="store_true", help="use SageMath to compute complete ideal parity, including singular prime ideals")
    args = parser.parse_args()
    if args.n is None:
        if args.planted or args.relations_only or args.all_ideals or args.degree is not None or args.height != GRID["HEIGHT"] or args.queries not in (None, QUERY_CAP):
            parser.error("provide N for a configurable search")
        fixtures()
    else:
        degree = PAIR["scheduled_degree"](args.n) if args.degree is None and args.n >= 2 else args.degree
        try:
            print(json.dumps(search(args.n, degree, args.height, args.queries, args.planted, args.relations_only, args.all_ideals)))
        except ModuleNotFoundError as error:
            if args.all_ideals and error.name in ("sage", "sage.all"):
                parser.error("--all-ideals requires a Python environment with SageMath")
            raise
        except ValueError as error:
            parser.error(str(error))
