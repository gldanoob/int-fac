from pathlib import Path
from fractions import Fraction
from math import gcd, lcm, prod
import json, subprocess, ast

W = Path(__file__).resolve().parent
old = json.loads((W.parent / "sample" / "construction.json").read_text())
s = old["seed"]
profile = {int(k): v for k, v in old["profile"].items()}
M = 24 * prod(p for p in profile if p > 3)
C = lcm(117810, 126, 5, 7 * 9 * 13 * 19)
B = lcm(M, C)
Q = s**3
code = f"print([lift(sqrt(Mod(-3,{s}))),lift(sqrt(Mod(-19,{s}))),isprime({s})]);\n"
r = subprocess.run(
    ["gp", "-s", "128000000", "-fq"],
    input=code,
    text=True,
    capture_output=True,
    check=True,
)
a, b, cert = ast.literal_eval(r.stdout.strip())
assert cert == 1
roots = []
for d, z in [(-3, a), (-19, b)]:
    t = (1 + z) * pow(2, -1, s) % s
    mod = s
    for _ in range(2):
        nxt = mod * s
        t = (t - (t * t - t + (1 - d) // 4) * pow(2 * t - 1, -1, nxt)) % nxt
        assert (t * t - t + (1 - d) // 4) % nxt == 0
        mod = nxt
    roots.append(t)
u, v = roots
# Columns generate the homogeneous lattice I^3 ∩ [C,C,B,B] Z^4.
# Every coordinate is a multiple of C, while the v and uv coefficients are multiples of M.
qinv = pow(C, -1, Q)
columns = [
    [C * Q, 0, 0, 0],
    [-C * (u % Q), C, 0, 0],
    [-C * ((B * v * qinv) % Q), 0, B, 0],
    [-C * ((B * u * v * qinv) % Q), 0, 0, B],
]
for x in columns:
    assert (x[0] + x[1] * u + x[2] * v + x[3] * u * v) % Q == 0
matrix = (
    "["
    + ";".join(",".join(str(columns[j][i]) for j in range(4)) for i in range(4))
    + "]"
)
code = f"A={matrix};T=qflll(A);R=A*T;print(vector(4,i,Vec(R[,i])));\n"
r = subprocess.run(
    ["gp", "-s", "128000000", "-fq"],
    input=code,
    text=True,
    capture_output=True,
    check=True,
)
if r.stderr:
    print(r.stderr)
basis = ast.literal_eval(r.stdout.strip())


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


star = []
norm = []
for x in basis:
    z = list(map(Fraction, x))
    for y, n in zip(star, norm):
        c = dot(x, y) / n
        z = [a - c * b for a, b in zip(z, y)]
    star.append(z)
    norm.append(dot(z, z))
alpha = [Q * pow(Q, -1, C), 0, 0, 0]
for x, y, n in reversed(list(zip(basis, star, norm))):
    k = round(dot(alpha, y) / n)
    alpha = [a - k * b for a, b in zip(alpha, x)]
assert alpha[0] % C == 1 and all(x % C == 0 for x in alpha[1:])
assert alpha[2] % M == alpha[3] % M == 0
assert (alpha[0] + alpha[1] * u + alpha[2] * v + alpha[3] * u * v) % Q == 0


def add(a, b):
    return [
        (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
        for i in range(max(len(a), len(b)))
    ]


def scale(a, k):
    return [k * x for x in a]


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def polynomial(beta):
    a, b, c, d = [[x, y] for x, y in zip(alpha, beta)]
    e = add(
        add(mul(a, a), scale(mul(b, b), -1)),
        add(
            add(mul(a, c), scale(mul(b, d), -1)),
            scale(add(mul(c, c), scale(mul(d, d), -1)), 5),
        ),
    )
    f = add(
        add(scale(mul(a, b), 2), mul(b, b)),
        add(
            add(mul(a, d), mul(b, c)),
            add(mul(b, d), add(scale(mul(c, d), 10), scale(mul(d, d), 5))),
        ),
    )
    N = add(add(mul(e, e), mul(e, f)), mul(f, f))
    assert all(x % Q == 0 for x in N)
    return [x // Q for x in N]


for beta in basis:
    coeff = polynomial(beta)
    pol = "+".join(f"({x})*x^{i}" for i, x in enumerate(coeff))
    r = subprocess.run(
        ["gp", "-s", "128000000", "-fq"],
        input=f"print(polisirreducible({pol}));\n",
        text=True,
        capture_output=True,
        check=True,
    )
    if r.stdout.strip() == "1":
        break
else:
    raise AssertionError("all candidate lines reducible")
assert gcd(*coeff) == 1
out = dict(
    seed=s,
    Q=Q,
    marker_modulus=M,
    ray_conductor=C,
    relative_multiplier=B,
    u=u,
    v=v,
    alpha=alpha,
    beta=beta,
    coefficients=coeff,
    profile=profile,
    fields=old["fields"],
    basis=basis,
)
(W / "construction.json").write_text(json.dumps(out, indent=2))
print(
    "seedbits",
    s.bit_length(),
    "C",
    C,
    "Mbits",
    M.bit_length(),
    "alpha bits",
    [abs(x).bit_length() for x in alpha],
    "coefficient bits",
    [abs(x).bit_length() for x in coeff],
)
