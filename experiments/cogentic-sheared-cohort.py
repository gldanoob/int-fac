"""Generate the frozen sheared-grid validation cohort without running a solver."""

from hashlib import sha256
import json
from math import isqrt
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).resolve().parent
SEED = b"int-fac/sheared-quadratic-squareclasses/v1/ecaf73d"


def generate():
    old = set(run_path(str(HERE / "cogentic-monic-blind-grid.py"))["INPUTS"])
    old.update(json.loads((HERE / "cogentic-monic-fresh-inputs.json").read_text()))
    primes = [p for p in range(9001, 50000, 2)
              if all(p % q for q in range(3, isqrt(p)+1, 2))]
    labels, used = {}, set()
    counter = 0
    while len(labels) < 8:
        digest = sha256(SEED + counter.to_bytes(8, "big")).digest()
        counter += 1
        p, q = sorted(primes[int.from_bytes(digest[i:i+16], "big") % len(primes)] for i in (0, 16))
        n = p*q
        if p == q or q > 2*p or not 29 <= n.bit_length() <= 32 or n in old or p in used or q in used:
            continue
        labels[n] = (p, q)
        used.update((p, q))
    return labels


if __name__ == "__main__":
    print(json.dumps(list(generate()), indent=2))
