"""Check a single conic, its split on a composite, and the several-start accounting."""

from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import gcd, prod
from pathlib import Path
import runpy

cube = runpy.run_path(str(Path(__file__).with_name("mean-time-ecm.py")))
ec = cube["ec"]
chi = ec["character"]


def conic_checks():
    auxiliary = (3, 5, 7, 11, 13)
    larger = ec["primes_up_to"](2000)
    signed = exceptional = arithmetic = 0
    for p in (211, 223, 227, 229, 233, 239):
        sign_sets = [[s for s in auxiliary if chi(s, p) == sign] for sign in (1, -1)]
        majority = max(sign_sets, key=len)
        for q in (v for v in larger if 310 < v < 1650):
            signs = {chi(s, q) for s in majority}
            if len(signs) == 1:
                assert abs(sum(chi(s, q) for s in majority)) == len(majority)
                exceptional += 1
                continue
            f = next(u * v for u, v in combinations(majority, 2) if chi(u*v, q) == -1)
            c = Fraction((f+1)**2, (f-1)**2)
            assert c - 1 == f * Fraction(2, f-1)**2
            for l, expected in ((p, 1), (q, -1)):
                val = c.numerator * pow(c.denominator, -1, l) % l
                assert chi(val, l) == 1 and chi(val-1, l) == expected
            signed += 1
            if q > 470 or arithmetic >= 45:
                continue
            scalar = ec["odd_scalar"](p*q, 17)
            for mark in ec["marks"](c, 6):
                if gcd(mark.numerator * mark.denominator * (mark.numerator-mark.denominator), p*q) != 1:
                    continue
                ap = mark.numerator * pow(mark.denominator, -1, p) % p
                for lam in range(2, p):
                    if chi(ap-lam, p) != 1:
                        continue
                    trace = -sum(chi(x*(x-1)*(x-lam), p) for x in range(p))
                    n = p+1-trace
                    if not trace or trace**2 > p or n % 8 != 4 or scalar % (n//4):
                        continue
                    aq = mark.numerator * pow(mark.denominator, -1, q) % q
                    if aq == lam:
                        continue
                    assert ec["marked_product"](mark, lam, scalar, p) is None
                    assert ec["marked_product"](mark, lam, scalar, q) is not None
                    try:
                        ec["marked_product"](mark, lam, scalar, p*q)
                    except ec["ProperFactor"] as found:
                        assert found.args[0] in (p, q)
                        arithmetic += 1
                        break
                    raise AssertionError("local parity discrepancy gave no proper gcd")
                else:
                    continue
                break
    assert exceptional and arithmetic == 45
    print(f"{signed} one-conic pairs, {exceptional} constant-sign partners, "
          f"{arithmetic} independently checked local and composite scalar splits")


def block_checks():
    cases = tested_words = partners = 0
    for k in range(2, 5):
        d = 1 << k
        p = (3*d)//4+1
        for a in (1, 2):
            shifts = cube["shifts"](k, a)
            for target in ({1}, {0, 1, d-1}):
                missed = {w for w in range(d) if not any((w ^ s) in target for s in shifts)}
                for r in (1, 2, 3):
                    size = d**r
                    def fails(word):
                        return all(((word >> (i*k)) % d) in missed for i in range(r))
                    assert sum(fails(w) for w in range(size)) == len(missed)**r
                    assert (len(missed) * 4**a * len(target))**r <= (d*d*k*k)**r
                    span = size + 17
                    j = p.bit_length()-1
                    histogram = Counter((p*m >> j) % size for m in range(span+1,2*span+1))
                    limit = (2*span+size-1)//size+1
                    assert max(histogram.values()) <= limit
                    assert sum(count for word,count in histogram.items() if fails(word)) <= limit * len(missed)**r
                    tested_words += size
                    partners += span
                    cases += 1
    print(f"{cases} multiblock cases, {tested_words} exact word checks, {partners} integer partners")


if __name__ == "__main__":
    conic_checks()
    block_checks()
