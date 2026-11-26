"""Compose full grid parity, adaptive exact squares, and basis gcd extraction."""

from ast import literal_eval
from math import gcd, prod
from pathlib import Path
from runpy import run_path
from subprocess import TimeoutExpired
from time import monotonic


HERE = Path(__file__).resolve().parent
GRID = run_path(str(HERE / "cogentic-monic-large-primes.py"))
REPAIR = run_path(str(HERE / "cogentic-monic-index.py"))["repair"]
INPUTS = (35, 77, 143, 221, 323, *GRID["INPUTS"])
QUERY_CAP = 128
CASE_SECONDS = 5


def adaptive(parity_basis, oracle):
    pivots, square_basis, tests = [], [], 0
    for word in parity_basis:
        for selection in range(1 << len(pivots)):
            if tests == QUERY_CAP:
                return "query-cap", tests, len(pivots), square_basis
            candidate = word ^ GRID["combine"](selection, pivots)
            try:
                roots = oracle(candidate)
            except TimeoutExpired:
                return "time-cap", tests, len(pivots), square_basis
            tests += 1
            if roots:
                square_basis.append((candidate, roots))
                break
        else:
            pivots.append(word)
    return "complete", tests, len(pivots), square_basis


def exact_oracle(n, m, fields, marks):
    deadline = monotonic() + CASE_SECONDS
    sign_bit = 1 << len(marks)
    coefficients = [list(p) for p in fields]

    def decode(word):
        points = [list(marks[j][0]) for j in GRID["support"](word & ~sign_bit)]
        return (-1 if word & sign_bit else 1), points

    def query(word):
        sign, points = decode(word)
        seconds = deadline - monotonic()
        if seconds <= 0:
            raise TimeoutExpired("GP exact square oracle", CASE_SECONDS)
        code = ('read("cogentic-monic-kernel-driver.gp");\n'
                f'iferr(print(kernel_roots({n},{m},apply(Polrev,{coefficients}),'
                f'{points},{sign})),err,print(err);quit(1));\n')
        line, = GRID["gp"](code, timeout=seconds)
        return literal_eval(line)

    return sign_bit, decode, query


def replay(n, m, shift, fields, primes, cutoff):
    left, right = map(list, fields)
    try:
        line, = GRID["gp"](f"print(poldisc(Polrev({left}))*poldisc(Polrev({right})));\n",
                           timeout=CASE_SECONDS)
    except TimeoutExpired:
        return dict(n=n, m=m, shift=shift, status="discriminant-time-cap", tests=0, factors=[])
    marks = GRID["relations"](n, m, fields, int(line), primes, cutoff, complete_parity=True)
    columns = GRID["parity_words"]([small + large for _, small, large, _ in marks])
    parity_basis = GRID["eliminate"](columns, (1 << j for j in range(len(marks))))
    result = dict(n=n, m=m, shift=shift, columns=len(marks), parity=len(parity_basis))
    if not parity_basis:
        return dict(result, status="zero-parity", tests=0, basis=0, factors=[])

    assert all(GRID["combine"](word, columns) == 0 for word in parity_basis)
    sign_bit, decode, query = exact_oracle(n, m, fields, marks)
    status, tests, rank, square_basis = adaptive([sign_bit, *parity_basis], query)
    if status == "complete":
        assert len(square_basis) + rank == len(parity_basis) + 1
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


def main():
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


if __name__ == "__main__":
    main()
