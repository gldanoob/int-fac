"""Verify the sample indices, published pair and projections to smaller heights."""

import ast
import gzip
import json
import subprocess
from collections import defaultdict
from pathlib import Path

sample = Path(__file__).resolve().parent
construction = json.loads((sample / "construction.json").read_text())
fields = [(disc, tuple(coeffs)) for disc, coeffs in construction["fields"]]
A, B, C = construction["coefficients"]
pair = json.loads((sample / "best-pair.json").read_text())

with gzip.open(sample / "masks.txt.gz", "rt") as stream:
    rows = {}
    last = 0
    for line in stream:
        j, low, high = map(int, line.split())
        assert j > last and 0 <= low < 2**64 and 0 <= high < 64
        rows[j] = low | (high << 64)
        last = j
assert len(rows) == len(set(rows.values())) == 163458
for key, prime in [("j", "p"), ("k", "q")]:
    j = pair[key]
    assert A * j**2 + B * j + C == int(pair[prime])
assert (rows[pair["j"]] ^ rows[pair["k"]]).bit_count() == 7

for height, bits, expected_pairs in [(4, 29, 632), (5, 42, 0)]:
    result = subprocess.run(
        ["gp", "-fq"], cwd=sample.parent, text=True, capture_output=True, check=True,
        input=f'H={height}; iferr(read("enumerate.gp"), E, print(E); quit(1))\n',
    )
    catalog = set()
    for line in result.stdout.splitlines():
        disc, coeffs = ast.literal_eval(line)
        catalog.add((disc, tuple(coeffs)))
    projection = sum(1 << i for i, field in enumerate(fields) if field in catalog)
    assert projection.bit_count() == bits
    groups = defaultdict(list)
    pairs = 0
    closest = None
    for j, mask in rows.items():
        group = groups[mask & projection]
        pairs += len(group)
        for k, earlier in group:
            candidate = ((mask ^ earlier).bit_count(), j, k)
            if closest is None or candidate < closest:
                closest = candidate
        group.append((j, mask))
    assert pairs == expected_pairs
    if height == 4:
        assert closest[0] == 8
    print(f"Height {height}: {bits} active fields, {pairs} matching pairs, closest {closest}")
