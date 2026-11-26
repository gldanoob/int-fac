"""Verify the saved mixed-field splits without rebuilding the relation grids."""

import json
from collections import Counter
from math import gcd, prod
from pathlib import Path
from runpy import run_path


def verify(certificate, pair, gp, gp_check):
    n, m = certificate["n"], certificate["m"]
    height, degree = certificate["height"], certificate["degree"]
    assert height == 256 and degree == pair["scheduled_degree"](n) == 2
    actual_m, first, second = pair["monic_pair"](n, degree)
    third = [second[0] - 4*m, second[1] + 4, *second[2:]]
    fields = certificate["fields"]
    assert m == actual_m and fields == [list(first), list(second), third]

    groups = certificate["points"]
    assert len(groups) == len(fields)
    counts = Counter()
    for points in groups:
        unique = set(map(tuple, points))
        assert points and len(unique) == len(points)
        assert all(abs(a) <= height and 1 <= b <= height and gcd(a, b) == 1
                   and gcd(a-b*m, n) == 1 for a, b in unique)
        counts.update(unique)
    assert set(counts.values()) == {2}
    normalization = prod(a-b*m for a, b in counts) % n
    assert normalization == certificate["normalization"] and gcd(normalization, n) == 1

    calls = [f"check_square(Polrev({field}),{points},1,{m},{n})"
             for field, points in zip(fields, groups, strict=True)]
    line, = gp(gp_check + "print([" + ",".join(calls) + "]);\n")
    roots = json.loads(line)
    saved = certificate["residues"]
    for root, residue, points in zip(roots, saved, groups, strict=True):
        assert residue in (root, (-root) % n)
        assert root**2 % n == prod(a-b*m for a, b in points) % n
    inverse = pow(normalization, -1, n)
    ratio = prod(roots) * inverse % n
    saved_ratio = prod(saved) * inverse % n
    assert saved_ratio == certificate["ratio"] and saved_ratio in (ratio, (-ratio) % n)
    assert ratio**2 % n == 1
    divisor = gcd(saved_ratio-1, n)
    assert 1 < divisor < n and divisor == certificate["divisor"]
    assert divisor * certificate["cofactor"] == n
    assert sorted((gcd(ratio-1, n), gcd(ratio+1, n))) == sorted((divisor, n//divisor))
    print(f"{n} = {divisor} * {n//divisor} verified with field supports "
          f"{[len(points) for points in groups]}")


def main():
    directory = Path(__file__).resolve().parent
    pair = run_path(str(directory / "cogentic-monic-pair.py"))
    gp = run_path(str(directory / "cogentic-monic-large-primes.py"))["gp"]
    gp_check = run_path(str(directory / "cogentic-monic-degree-certificate-check.py"))["GP_CHECK"]
    certificates = json.loads((directory / "cogentic-monic-mixed-certificates.json").read_text())
    assert [certificate["n"] for certificate in certificates] == [310556537, 449508911]
    for certificate in certificates:
        verify(certificate, pair, gp, gp_check)


if __name__ == "__main__":
    main()
