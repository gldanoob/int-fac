"""One finite sample list controls all scalar tests and every child modulus."""

from fractions import Fraction
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations
from math import gcd, prod
from pathlib import Path


spec = spec_from_file_location("advice", Path(__file__).with_name("cogentic-extractor-advice.py"))
advice = module_from_spec(spec)
spec.loader.exec_module(advice)


def smooth_squarefree(n):
    if n <= 0:
        return False
    for p in (2, 3, 5, 7, 11):
        if n % p == 0:
            n //= p
            if n % p == 0:
                return False
    return n == 1


def local_masks(count):
    chosen = []
    for intercept in range(1, 81):
        for step in (1, 2, 3, 5):
            for a in (1, 2, 3):
                mask = sum(int(smooth_squarefree(intercept+step*((w & 3)+a*(w >> 2)))) << w
                           for w in range(16))
                if 4 <= mask.bit_count() <= 12 and all((mask ^ m).bit_count() >= 5 for m in chosen):
                    chosen.append(mask)
                    if len(chosen) == count:
                        return chosen
    raise AssertionError("not enough separated scalar tests")


def main():
    primes = (3, 5, 7, 11, 13, 17)
    masks = local_masks(len(primes))
    tests = set(masks) | {x & y for x, y in combinations(masks, 2)}
    # Taking all 224 multipliers of this explicit finite family keeps the
    # scalar score errors small; this is not the asymptotic GUV construction.
    multipliers = [1]
    for _ in range(223):
        multipliers.append(advice.multiply(3, multipliers[-1]))
    denom = len(multipliers)
    good_masters = set()
    largest_good = Fraction(0)
    sample_lists = []
    for a in range(256):
        words = [advice.multiply(a, s) >> 4 for s in multipliers]
        freq = [words.count(w) for w in range(16)]
        sample_lists.append(tuple(w for w in range(16) if freq[w]))
        error = max(abs(sum(Fraction(freq[w], denom) for w in range(16) if (mask >> w) & 1)
                        - Fraction(mask.bit_count(), 16)) for mask in tests)
        if error < Fraction(1, 16):
            good_masters.add(a)
            largest_good = max(largest_good, error)
            # Each pair's miss score is 1-Fp-Fq+2FpFq. The worst discrepancy
            # is strictly less than 4/16, below its uniform margin of 5/16.
            assert all(any(((m ^ n) >> w) & 1 for w in words) for m, n in combinations(masks, 2))
    columns = [prod(p for p, m in zip(primes, masks) if m >> w & 1) for w in range(16)]
    calls = 0

    def factor(n, words):
        nonlocal calls
        calls += 1
        if n == 1:
            return []
        for p in primes:
            v, k = n, 0
            while v % p == 0:
                v //= p
                k += 1
            if v == 1:
                return [p]*k
        for w in words:
            g = gcd(n, pow(columns[w], n.bit_length(), n))
            if 1 < g < n:
                return factor(g, words)+factor(n//g, words)
        raise AssertionError(n)

    completed = 0
    for first, second in combinations(primes, 2):
        for extra in (1, first, second, first*second):
            n = first*second*extra
            master = n % 256
            if master in good_masters:
                assert prod(factor(n, sample_lists[master])) == n
                completed += 1
    for p, q, r in combinations(primes, 3):
        for extra in (1, p, q*r):
            n = p*q*r*extra
            master = n % 256
            if master in good_masters:
                assert prod(factor(n, sample_lists[master])) == n
                completed += 1
    assert 0 < len(good_masters) < 256 and completed > 0
    print(f"{len(tests)} distinct affine smooth scalar tests; {len(good_masters)} simultaneous "
          f"masters out of 256; largest passing error {largest_good}; {completed} composite "
          f"factorizations in {calls} recursive calls")


if __name__ == "__main__":
    main()
