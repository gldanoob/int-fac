"""Independent counts for the two auxiliary-prime menus and their moments."""

from collections import Counter
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations, product
from math import factorial, prod
from pathlib import Path

spec = spec_from_file_location("pointwise", Path(__file__).with_name("pointwise-conic-marks.py"))
pointwise = module_from_spec(spec)
spec.loader.exec_module(pointwise)
character = pointwise.character


def sign_counts(rows, signs):
    direct = sum(row == signs for row in rows)
    expansion = 0
    for mask in product((0, 1), repeat=len(signs)):
        moment = sum(prod(x for x, use in zip(row, mask) if use) for row in rows)
        expansion += moment * prod(s for s, use in zip(signs, mask) if use)
    assert expansion == (1 << len(signs)) * direct
    return direct


def main():
    primes = pointwise.prime_numbers(3600)
    first = [r for r in primes if 125 < r <= 625 and r % 8 == 1]
    second = [r for r in primes if 1750 < r <= 3500 and r % 8 == 1]
    partners = [r for r in primes if 23 <= r < 109]
    signed_cases = expanded = 0
    for p, q in combinations(partners, 2):
        erows = [(character(e, p), character(e, q)) for e in first]
        for sign in (-1, 1):
            ecount = sign_counts(erows, (sign, 1))
            expanded += 1
            if not ecount:
                continue
            e = next(e for e, row in zip(first, erows) if row == (sign, 1))
            frows = [(character(f, p), character(f, q), character(f, e)) for f in second]
            fcount = sign_counts(frows, (sign, -1, 1))
            expanded += 1
            if fcount:
                f = next(f for f, row in zip(second, frows) if row == (sign, -1, 1))
                pointwise.witness(e, f, p, q, sign)
                signed_cases += 1
    assert signed_cases > 250
    moment_checks = 0
    for k in range(1, 5):
        for weights in ([1] * 7, [character(r, 13) for r in first[:7]]):
            support = first[:7]
            coefficients = Counter()
            for ix in product(range(len(support)), repeat=k):
                coefficients[prod(support[i] for i in ix)] += prod(weights[i] for i in ix)
            assert sum(a * a for a in coefficients.values()) <= factorial(k) * len(support)**k
            for p in partners:
                lhs = sum(w * character(r, p) for w, r in zip(weights, support))**k
                assert lhs == sum(a * character(n, p) for n, a in coefficients.items())
                moment_checks += 1
    print(f"{len(first)} and {len(second)} auxiliary primes, {expanded} sign expansions, "
          f"{signed_cases} rational witnesses, {moment_checks} moment identities")


if __name__ == "__main__":
    main()
