"""Generate the public degree-three boundary cohort and verify saved records."""

import argparse
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

HERE = Path(__file__).resolve().parent
SEED = b"int-fac/monic-216/v1/18e2e46"
LOW, HIGH = 3 << 106, 1 << 108


def generate():
    gp = run_path(str(HERE / "cogentic-monic-large-primes.py"))["gp"]
    primes, counter = [], 0
    while len(primes) < 6:
        random_word = int.from_bytes(sha256(SEED+counter.to_bytes(8, "big")).digest(), "big")
        counter += 1
        start = LOW+2*(random_word % ((HIGH-LOW)//2))+1
        line, = gp(f"p=nextprime({start}); while(!isprime(p),p=nextprime(p+1)); print(p);\n")
        prime = int(line)
        if prime < HIGH and prime not in primes:
            primes.append(prime)
    return {p*q: (p, q) for p, q in zip(primes[::2], primes[1::2], strict=True)}


def validate(path):
    labels = generate()
    public = tuple(json.loads((HERE / "cogentic-monic-216-inputs.json").read_text()))
    assert tuple(labels) == public and all(n.bit_length() == 216 for n in public)
    records = [json.loads(line) for line in path.read_text().splitlines()]
    assert set(record["n"] for record in records) == set(public)
    for record in records:
        if "divisor" in record:
            assert record["divisor"] in labels[record["n"]]
    print(f"Validated {len(public)} products of distinct 108-bit primes and {len(records)} records.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", type=Path, help="check records after the benchmark")
    args = parser.parse_args()
    if args.validate is None:
        print(json.dumps(list(generate()), indent=2))
    else:
        validate(args.validate)
