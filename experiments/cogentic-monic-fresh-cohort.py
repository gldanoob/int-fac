"""Generate and validate the frozen fresh cohort without running a solver."""

import argparse
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path

SEED = b"int-fac/monic-fresh/v1/413a062"
FROZEN = tuple(json.loads(Path(__file__).with_name("cogentic-monic-fresh-inputs.json").read_text()))
OLD = {341854927, 824552227, 647911657, 641626049, 310556537,
       449508911, 2363084519, 929070139, 516173501, 422536969}


def generate():
    primes = [p for p in range(9001, 50000, 2)
              if all(p % q for q in range(3, isqrt(p)+1, 2))]
    selected, used = {}, set()
    counter = 0
    while len(selected) < 10:
        digest = sha256(SEED + counter.to_bytes(8, "big")).digest()
        counter += 1
        p, q = sorted(primes[int.from_bytes(digest[i:i+16], "big") % len(primes)] for i in (0, 16))
        n = p*q
        if p == q or q > 2*p or not 29 <= n.bit_length() <= 32:
            continue
        if p in used or q in used or n in OLD:
            continue
        selected[n] = (p, q)
        used.update((p, q))
    return selected


def validate(path):
    labels = generate()
    assert tuple(labels) == FROZEN
    records = [json.loads(line) for line in path.read_text().splitlines()]
    assert set(record["n"] for record in records) == set(FROZEN)
    for record in records:
        n = record["n"]
        p, q = labels[n]
        assert p*q == n
        for certificate in record.get("factors", []):
            assert certificate["divisor"] in (p, q)
    print(json.dumps(dict(validated=len(labels), rows=len(records),
                          prime_range=[min(min(pair) for pair in labels.values()),
                                       max(max(pair) for pair in labels.values())])))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", type=Path, help="validate completed solver records")
    args = parser.parse_args()
    if args.validate:
        validate(args.validate)
    else:
        print(tuple(generate()))
