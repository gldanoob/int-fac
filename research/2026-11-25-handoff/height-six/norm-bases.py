from pathlib import Path
from fractions import Fraction
from itertools import combinations
from math import prod, sqrt
import ast

W = Path(__file__).resolve().parent
profile, groups = ast.literal_eval((W / "collision-profile-0.txt").read_text())


def squareclass(n):
    out = {-1} if n < 0 else set()
    n = abs(n)
    p = 2
    while p * p <= n:
        while n % p == 0:
            out ^= {p}
            n //= p
        p += 1
    if n > 1:
        out.add(n)
    return out


classes = [squareclass(D) for D, m, g in groups]
primes = sorted(set().union(*classes))
masks = [sum(1 << primes.index(p) for p in S) for S in classes]
rank = {D: {-3: 6, -19: 3, -51: 2, -307: 2}.get(D, m) for D, m, g in groups}
P3 = Fraction(5825, 531441)
P19 = Fraction(61, 729)
prob = {
    D: {-3: P3, -19: P19, -51: Fraction(17, 81), -307: Fraction(17, 81)}.get(
        D, Fraction(5, 9) ** m
    )
    for D, m, g in groups
}
P = prod(prob.values())
lookup = {
    mask: (D, 0 if D in (-3, -19) else rank[D], int(D == -3), int(D == -19))
    for mask, (D, m, g) in zip(masks, groups)
}
weights = {
    (n, b, c): Fraction(5, 9) ** n * P3**b * P19**c
    for n in range(56)
    for b in (0, 1)
    for c in (0, 1)
}
ordered = sorted(weights, key=lambda key: weights[key])
order = {key: i for i, key in enumerate(ordered)}
results = []
for k in range(1, 5):
    best = None
    bestscore = 10**9
    tested = 0
    for ids in combinations(range(len(masks)), k):
        span = {0}
        for i in ids:
            span |= {x ^ masks[i] for x in tuple(span)}
        if len(span) != 1 << k:
            continue
        tested += 1
        n = b = c = 0
        covered = []
        for x in span:
            if x in lookup:
                D, u, v, w = lookup[x]
                covered.append(D)
                n += u
                b += v
                c += w
        key = (n, b, c)
        score = order[key]
        if score < bestscore:
            bestscore = score
            best = (ids, sorted(covered), key)
    ids, covered, key = best
    remaining = P / weights[key]
    out = dict(
        binary_rank=k,
        base_degree=1 << k,
        basis=[groups[i][0] for i in ids],
        covered=covered,
        covered_ternary_rank=sum(rank[D] for D in covered),
        remaining_collision=str(remaining),
        birthday_one_expected_pair=sqrt(2 / float(remaining)),
        basis_tuples_tested=tested,
    )
    print(out, flush=True)
    results.append(out)
(W / "norm-bases.txt").write_text("\n".join(map(repr, results)) + "\n")
