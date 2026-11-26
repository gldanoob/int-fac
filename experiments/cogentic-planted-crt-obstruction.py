"""Certify shared local 2-primary signs on two balanced planted inputs."""

from math import gcd
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).resolve().parent
PLANTS = run_path(str(HERE / "cogentic-planted-norm-two.py"))
GP = run_path(str(HERE / "cogentic-monic-large-primes.py"))["gp"]


def local_signature(p, labels):
    return tuple(pow(label, (p - 1) // 2, p) == 1 for label in labels)


def fixture(bits, h=None):
    x = 1 << bits
    base = PLANTS["BASE"]
    scheduled = h is None
    if scheduled:
        h = base["scheduled_degree"](x*x)
    m = base["integer_root"](x*x, h) | 1
    if m**h > x*x:
        m -= 2
    labels = tuple(m - 2*j for j in range(h // 2))
    assert len(labels) >= 2 and 0 < labels[-1] <= labels[0] < x
    code = f"p={x}; for(i=1,48,p=nextprime(p+1);if(p%4==3,print(p)));\n"
    bins = {}
    for p in map(int, GP(code)):
        assert x <= p <= 5*x//4 and p % 4 == 3 and m**h <= p*p < (m+2)**h
        signature = local_signature(p, labels)
        if all(signature):
            continue
        if signature not in bins:
            bins[signature] = p
            continue
        q = bins[signature]
        n = p*q
        result = PLANTS["monic_plants"](n, h)
        if isinstance(result, int):
            continue
        assert GP(f"print(isprime({p}) && isprime({q}));\n") == ["1"]
        actual_m, cuts, _, _ = result
        assert m == actual_m and labels == tuple(m-t for t in cuts)
        assert gcd(n, m) == 1 and (not scheduled or base["scheduled_degree"](n) == h)
        print(f"{n.bit_length()} bits, h={h}, prime offsets {q-x} and {p-x}, "
              f"shared local signs {tuple(1 if positive else -1 for positive in signature)}")
        return
    raise AssertionError("no same-signature balanced fixture")


if __name__ == "__main__":
    fixture(60, 8)
    fixture(512)
