from pathlib import Path
from fractions import Fraction
import ast, math, collections, sys, itertools

W = Path(__file__).resolve().parent
branch = int(sys.argv[1]) if len(sys.argv) > 1 else 0
F = [ast.literal_eval(l) for l in (W / "fields6.txt").read_text().splitlines()]


def factors(n):
    z = collections.Counter()
    p = 2
    while p * p <= n:
        while n % p == 0:
            z[p] += 1
            n //= p
        p += 1
    if n > 1:
        z[n] += 1
    return z


def fund(d):
    s = (-1 if d < 0 else 1) * math.prod(p for p, e in factors(abs(d)).items() if e % 2)
    return s if s % 4 == 1 else 4 * s


def row(d):
    odd = [p for p, e in factors(abs(d)).items() if p % 2 and e % 2]
    S = set(odd) - {3}
    if ((d < 0) + sum(p % 4 == 3 for p in odd)) % 2:
        S.add(-1)
    if factors(abs(d))[2] % 2:
        S.add(2)
    return frozenset(S), branch * int(3 in odd)


G = collections.defaultdict(list)
for d, v in F:
    G[fund(d)].append((d, v))
assert len(F) == 369 and len(G) == 330 and len(G[1]) == 4
G.pop(1)


def collision(vectors):
    histogram = collections.Counter()
    for x in itertools.product(range(3), repeat=len(vectors[0])):
        mask = sum(
            (sum(a * b for a, b in zip(x, v)) % 3 != 0) << i
            for i, v in enumerate(vectors)
        )
        histogram[mask] += 1
    return Fraction(sum(c * c for c in histogram.values()), 3 ** (2 * len(vectors[0])))


pure_vectors = [
    [1, 2, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0, 0],
    [1, 1, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0],
    [1, 0, 1, 0, 0, 0],
    [0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0],
    [1, 0, 0, 2, 0, 0],
    [1, 0, 0, 0, 2, 0],
]
pure_probability = collision(pure_vectors)
minus19_probability = collision([[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 0], [1, 0, 1]])
plane_probability = collision([[1, 0], [0, 1], [1, 1]])
assert pure_probability == Fraction(5825, 531441)
assert minus19_probability == Fraction(61, 729)
assert (
    plane_probability == collision([[1, 0], [0, 1], [1, 1], [1, 2]]) == Fraction(17, 81)
)
C = {D: Fraction(5, 9) ** len(g) for D, g in G.items()}
C.update(
    {
        -3: pure_probability,
        -19: minus19_probability,
        -51: plane_probability,
        -307: plane_probability,
    }
)
assert sum({-3: 6, -19: 3, -51: 2, -307: 2}.get(D, len(g)) for D, g in G.items()) == 356
terms = []
for D in G:
    S, o = row(D)
    terms.append(
        (
            S,
            [
                C[D] if (state.bit_count() + o) % 2 == 0 else Fraction(1)
                for state in range(1 << len(S))
            ],
        )
    )
variables = set().union(*(S for S, t in terms))
archive = []
width = 0
while variables:
    adj = collections.defaultdict(list)
    for i, (S, t) in enumerate(terms):
        for v in S:
            adj[v].append(i)

    def neighbors(v):
        return set().union(*(terms[i][0] for i in adj[v])) - {v}

    v = min(variables, key=lambda v: (len(neighbors(v)), len(adj[v]), v))
    scope = sorted(neighbors(v))
    width = max(width, len(scope))
    mapping = {u: 1 << i for i, u in enumerate(scope)}
    old = [
        (tuple(mapping.get(u, 0) for u in sorted(S)), t)
        for S, t in (terms[i] for i in adj[v])
    ]
    new = []
    choices = []
    for state in range(1 << len(scope)):
        scores = [
            math.prod(
                t[
                    sum(
                        (int(bool(state & mask)) if mask else bit) << i
                        for i, mask in enumerate(masks)
                    )
                ]
                for masks, t in old
            )
            for bit in (0, 1)
        ]
        pick = int(scores[1] > scores[0])
        new.append(scores[pick])
        choices.append(pick)
    removed = set(adj[v])
    terms = [t for i, t in enumerate(terms) if i not in removed] + [
        (frozenset(scope), new)
    ]
    archive.append((v, scope, choices))
    variables.remove(v)
profile = {}
for v, scope, choices in reversed(archive):
    profile[v] = choices[sum(profile[u] << i for i, u in enumerate(scope))]
remaining = [
    (D, len(G[D]), G[D])
    for D in sorted(G)
    if (sum(profile[p] for p in row(D)[0]) + row(D)[1]) % 2 == 0
]
prob = math.prod(t[0] for S, t in terms)
print(
    "branch",
    branch + 1,
    "width",
    width,
    "groups",
    len(remaining),
    "fieldbits",
    sum(len(g) for _, _, g in remaining),
    "collision",
    prob,
    "float",
    float(prob),
    "birthday",
    math.sqrt(2 / float(prob)),
)
(W / f"collision-profile-{branch}.txt").write_text(repr((profile, remaining)) + "\n")
(W / f"collision-prob-{branch}.txt").write_text(str(prob) + "\n")
