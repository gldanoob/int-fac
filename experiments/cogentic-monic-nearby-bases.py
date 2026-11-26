"""Test a fixed list of short odd base shifts on the frozen quadratic grid."""

import json
from fractions import Fraction
from math import gcd, prod
from pathlib import Path
from runpy import run_path
from time import monotonic

HERE = Path(__file__).resolve().parent
BLIND = run_path(str(HERE / "cogentic-monic-blind-grid.py"))
DRIVER, GRID, PREFILTER = (BLIND[name] for name in ("DRIVER", "GRID", "PREFILTER"))
COLLECT = run_path(str(HERE / "cogentic-monic-lattice-sieve.py"))["collect"]
HEIGHT, CUTOFF, PROBE_CAP, QUERY_CAP = 256, 2*256**2, 257, 3
LOCAL_PRIMES = tuple(p for p in GRID["primes_through"](43) if p > 2)


def shifted_pair(n, m):
    q, c = divmod((n-m*m)//2, m)
    if c % 2 == 0:
        q, c = q+1, c-m
    f = (2*c, 2*q, 1)
    g = (2*c, 2*q, 1-m, 1)
    assert m >= 3 and m % 2 and n >= m*m and n % 2
    assert all(p[-1] == 1 and p[0] % 4 == 2 and all(x % 2 == 0 for x in p[:-1])
               and sum(c*m**i for i, c in enumerate(p)) == n for p in (f, g))
    return f, g


def local_score(n, m, fields):
    score = Fraction(0)
    for f in fields:
        derivative = [i*c for i, c in enumerate(f) if i]
        for p in LOCAL_PRIMES:
            roots = sum((n % p != 0 or (x-m) % p != 0)
                        and GRID["polynomial"](f, x, p) == 0
                        and GRID["polynomial"](derivative, x, p) != 0 for x in range(p))
            score += Fraction(roots, p+1)
    return score


def prepare(n):
    m, f, g = GRID["CHECK_PAIR"](n, 2)
    attempts = []
    for j in (0, 1, 2):
        m1 = m-2*j
        fields = shifted_pair(n, m1)
        assert fields[0] == (f[0]+2*j*f[1]+4*j*j, f[1]+4*j, 1)
        if j == 0:
            assert fields == (f, g)
        fixed = DRIVER["REPAIR"](n, m1, *fields)
        score = local_score(n, m1, fixed[1] if not isinstance(fixed, int) else fields)
        attempts.append((j, m1, fixed, score))
    baseline, *shifted = attempts
    return baseline, *sorted(shifted, key=lambda trial: (-trial[3], trial[0]))


def measure(n, trial, budget):
    j, m, fixed, score = trial
    out = dict(n=n, j=j, m=m, score=str(score), tests=0, factors=[])
    if isinstance(fixed, int):
        assert 1 < fixed < n and n % fixed == 0
        return dict(out, status="derivative-gcd", divisor=fixed)
    shift, fields = fixed
    f, g = map(list, fields)
    disc = int(DRIVER["gp_value"](f"poldisc(Polrev({f}))*poldisc(Polrev({g}))", 5))
    marks = COLLECT(n, m, fields, disc, CUTOFF, height=HEIGHT,
                    include_ramified_two=True, mark_local=True)
    columns = [small+large for _, small, large, _ in marks]
    core, parity = GRID["parity_basis"](columns)
    out.update(shift=shift, fields=[f, g], quadratic_discriminant=f[1]**2-4*f[0],
               columns=len(marks), smooth=sum(mark[3] for mark in marks),
               rows=[len({key for column in columns for key in column if key[0] == i}) for i in (1, 2)],
               core=len(core), nullity=len(parity))
    if not parity:
        return dict(out, status="zero-parity")
    if j == 0:
        return dict(out, status="baseline-rank-only")
    core_marks = [marks[i] for i in core]
    sign_bit, decode, query = DRIVER["exact_oracle"](n, m, fields, core_marks, 5)
    survivors, stats = PREFILTER(fields, [mark[0] for mark in core_marks], [sign_bit, *parity], disc,
                                prime_cutoff=PROBE_CAP)
    status, tests, rank, basis = DRIVER["adaptive"](survivors, query, budget, n)
    if status == "complete":
        assert rank+len(basis) == len(survivors)
    for word, (left, right) in basis:
        sign, points = decode(word)
        square = sign*prod(a-b*m for a, b in points) % n
        assert gcd(square, n) == 1 and left*left % n == right*right % n == square
        divisor = gcd(left-right, n)
        if 1 < divisor < n:
            out["factors"].append(dict(divisor=divisor, sign=sign, points=points,
                                       residues=[left, right], square=square))
    return dict(out, status=status, tests=tests, probe_rank=stats["rank"], surviving=len(survivors),
                square_basis=len(basis))


def confirm_certificates(results):
    check = run_path(str(HERE / "cogentic-monic-degree-certificate-check.py"))["GP_CHECK"]
    verified = 0
    for result in results:
        n, m = result["n"], result["m"]
        for certificate in result["factors"]:
            f, g = result["fields"]
            points, sign = certificate["points"], certificate["sign"]
            assert sign in (-1, 1) and len({tuple(point) for point in points}) == len(points)
            assert all(abs(a) <= HEIGHT and 1 <= b <= HEIGHT and gcd(a, b) == gcd(a-b*m, n) == 1
                       for a, b in points)
            code = (check + f"points={points};\n"
                    + f"print([check_square(Polrev({f}),points,{sign},{m},{n}),"
                    + f"check_square(Polrev({g}),points,{sign},{m},{n})]);\n")
            roots = json.loads(GRID["gp"](code, timeout=30)[0])
            assert all(a in (b, -b % n) for a, b in zip(certificate["residues"], roots, strict=True))
            left, right = certificate["residues"]
            square = sign*prod(a-b*m for a, b in points) % n
            assert left**2 % n == right**2 % n == square == certificate["square"]
            divisor = gcd(left-right, n)
            assert 1 < divisor < n and divisor == certificate["divisor"]
            verified += 1
    return verified


def run():
    planned = [(n, prepare(n)) for n in BLIND["INPUTS"]]
    print(json.dumps(dict(plan=[(n, [j for j, *_ in trials]) for n, trials in planned],
                          height=HEIGHT, cutoff=CUTOFF, queries=QUERY_CAP)), flush=True)
    results = []
    for n, trials in planned:
        budget = QUERY_CAP
        for trial in trials:
            start = monotonic()
            result = measure(n, trial, budget)
            result["seconds"] = round(monotonic()-start, 4)
            print(json.dumps(result), flush=True)
            results.append(result)
            budget -= result["tests"]
            if result["factors"] or budget == 0:
                break
    print(json.dumps(dict(independent_certificates=confirm_certificates(results))))


if __name__ == "__main__":
    run()
