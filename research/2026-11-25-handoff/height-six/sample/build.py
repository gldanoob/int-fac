from pathlib import Path
from math import prod, gcd
import ast, subprocess, json

W = Path(__file__).resolve().parent
profile, remaining = ast.literal_eval(
    (W.parent / "collision-profile-0.txt").read_text()
)
R, M = 1, 24
for p, bit in sorted(profile.items()):
    if p in (-1, 2, 3):
        continue
    want = bit ^ (int(p % 4 == 3) * profile[-1])
    value = (
        1
        if not want
        else next(j for j in range(2, p) if pow(j, (p - 1) // 2, p) == p - 1)
    )
    R += M * ((value - R) * pow(M, -1, p) % p)
    M *= p
assert profile[-1] == profile[2] == 0
D = -32 * 3 * prod(p for p in profile if p > 3)
# Correct (D/q*) by a fresh multiplier if necessary.
gp = f"""R={R};M={M};D={D};k=0;while(!ispseudoprime(R+k*M),k++);q=R+k*M;
if(kronecker(D,q)!=1,my(z=2);while(kronecker(z,q)!=-1,z++);D*=z);
F=qfbred(qfbprimeform(D,q));print([D,Vec(F),q]);
"""
p = subprocess.run(["gp", "-fq"], input=gp, text=True, capture_output=True, check=True)
if p.stderr:
    print(p.stderr)
D, (a, b, c), q = ast.literal_eval(p.stdout.strip())
assert b * b - 4 * a * c == D
j0, step = 0, 1
cyclic = {}
for modulus in [7, 9, 13, 19]:
    values = [
        j
        for j in range(modulus)
        if gcd((a * j * j + b * j + c) % modulus, modulus) == 1
    ]
    target = next(
        (
            j
            for j in values
            if (
                pow((a * j * j + b * j + c) % modulus, (modulus - 1) // 3, modulus) == 1
                if modulus != 9
                else (a * j * j + b * j + c) % 9 in (1, 8)
            )
        ),
        values[0],
    )
    j0 += step * ((target - j0) * pow(step, -1, modulus) % modulus)
    step *= modulus
    cyclic[modulus] = (a * target * target + b * target + c) % modulus
A = a * step * step
B = step * (2 * a * j0 + b)
C = a * j0 * j0 + b * j0 + c
fields = [(d, vec) for _, _, group in remaining for d, vec in group]
data = dict(
    D=D,
    seed=q,
    form=[a, b, c],
    j0=j0,
    step=step,
    coefficients=[A, B, C],
    cyclic=cyclic,
    profile=profile,
    fields=fields,
)
(W / "construction.json").write_text(json.dumps(data, indent=2))
(W / "params.txt").write_text(
    "\n".join(map(str, [A, B, C]))
    + "\n"
    + str(len(fields))
    + "\n"
    + "\n".join(" ".join(map(str, [d, *v])) for d, v in fields)
    + "\n"
)
print(
    "D bits",
    abs(D).bit_length(),
    "coeff bits",
    [v.bit_length() for v in [A, B, C]],
    "fields",
    len(fields),
    "cyclic",
    cyclic,
)
