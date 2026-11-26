"""Check radix fibers and the norm congruences used in the scheduled-grid count."""

from collections import Counter
from itertools import product
from math import ceil, gcd
from pathlib import Path
from runpy import run_path


def main():
    pair = run_path(str(Path(__file__).with_name("cogentic-monic-pair.py")))["monic_pair"]
    boxes = fibers = progressions = 0
    for m, d in ((5, 3), (5, 4), (5, 5), (7, 4)):
        k = d - 2
        digits = list(product(range(-m, m, 2), *([range(m)] * k)))
        assert len(digits) == m ** (k + 1)
        for top in (0, 1, d):
            for cs in digits:
                coeff = tuple(2 * v for v in (*cs, top)) + (1,)
                n = sum(v * m**i for i, v in enumerate(coeff))
                if m**d <= n < (m+2)**d:
                    assert pair(n, d) == (m, coeff, coeff[:-1] + (1-m, 1))
                    boxes += 1
        for a in range(-5, 6):
            for b in range(1, 6):
                if gcd(a, b) != 1:
                    continue
                h = max(abs(a), b)
                atoms = Counter(sum(ci*a**i*b**(k-i) for i, ci in enumerate(cs)) for cs in digits)
                assert max(atoms.values()) <= 2 * ceil(m / h)**k
                assert max(atoms) - min(atoms) <= 2*(k+1)*m*h**k
                fibers += len(atoms)
                for degree in (d, d+1):
                    j = degree-k
                    base = a**d + 2*d*a**(d-1)*b
                    if degree == d+1:
                        base = b*base + (a-m*b)*a**d
                    for u in (3, 5, 9, 15, 35):
                        hits = [t for t in atoms if (base + 2*b**j*t) % u == 0]
                        if gcd(b, u) > 1:
                            assert not hits
                        else:
                            root = -base * pow(2*b**j, -1, u) % u
                            assert all(t % u == root for t in hits)
                            span = max(atoms)-min(atoms)
                            assert sum(atoms[t] for t in hits) <= max(atoms.values()) * (1+span//u)
                        progressions += 1
                    for cs in (digits[0], digits[len(digits)//2], digits[-1]):
                        f = tuple(2*x for x in (*cs, d)) + (1,)
                        coeff = f if degree == d else f[:-1] + (1-m, 1)
                        t = sum(ci*a**i*b**(k-i) for i, ci in enumerate(cs))
                        norm = sum(v*a**i*b**(degree-i) for i, v in enumerate(coeff))
                        assert norm == base + 2*b**j*t
                        assert (norm % 2 == 1 if a % 2 else norm % 4 == 2)
    print(f"{boxes} actual input carries, {fibers} digit fibers, {progressions} divisor progressions")


if __name__ == "__main__":
    main()
