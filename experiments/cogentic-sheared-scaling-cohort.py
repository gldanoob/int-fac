"""Generate the public size-scaling inputs without running the matcher."""

from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

HERE = Path(__file__).resolve().parent
SEED = b"int-fac/sheared-size-scaling/v1/c15e471"
SIZES = (40, 48, 64)


def generate():
    gp = run_path(str(HERE / "cogentic-monic-large-primes.py"))["gp"]
    counter = 0
    labels = {}
    for bits in SIZES:
        low, high = 3 << (bits//2-2), 1 << (bits//2)
        primes = []
        while len(primes) < 6:
            word = int.from_bytes(sha256(SEED+counter.to_bytes(8, "big")).digest(), "big")
            counter += 1
            start = low+2*(word % ((high-low)//2))+1
            line, = gp(f"p=nextprime({start}); while(!isprime(p),p=nextprime(p+1)); print(p);\n")
            p = int(line)
            if p < high and p not in primes:
                primes.append(p)
        for p, q in zip(primes[::2], primes[1::2], strict=True):
            n = p*q
            assert n.bit_length() == bits
            labels[n] = tuple(sorted((p, q)))
    return labels


if __name__ == "__main__":
    print(json.dumps(list(generate()), indent=2))
