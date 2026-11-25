"""Check the two ways a nontrivial modular power can hit a shifted prime."""
from collections import Counter
from math import gcd, prod
from pathlib import Path
from runpy import run_path

primes_through = run_path(str(Path(__file__).with_name("smooth-predecessor-products.py")))["primes_through"]


def factors(n, primes):
    result = {}
    for s in primes:
        if s * s > n:
            break
        while n % s == 0:
            result[s] = result.get(s, 0) + 1
            n //= s
    if n > 1:
        result[n] = 1
    return result


def replay():
    primes = primes_through(60000)
    counts = Counter()
    for x in (50, 150, 500, 1500, 5000, 15000, 30000):
        above = [p for p in primes if x < p <= 2 * x]
        precursors = {p: factors(p - 1, primes) for p in above}
        markers = {p: max(fs) for p, fs in precursors.items() if max(fs)**5 > x**3}
        # Include actual exponents carrying large markers and signed rational bases.
        marker = next(iter(markers.values()))
        menus = [(2, 1, 60), (-3, 2, 24), (5, -2, 360), (7, 3, 4 * marker),
                 (-11, 1, 2 * marker), (31, 6, 2 * marker + 2)]
        seen, individual = set(), set()
        for p, s in markers.items():
            k = (p - 1) // s
            assert gcd(k, s) == 1
            for A, B, M in menus:
                assert gcd(A, B) == 1 and abs(A) != abs(B)
                hits = any((pow(A, M, p) - sign * pow(B, M, p)) % p == 0 for sign in (-1, 1))
                if not hits:
                    continue
                seen.add(p)
                if (2 * M) % s == 0:
                    counts["exponent hits"] += 1
                else:
                    assert pow(A, k, p) == pow(B, k, p)
                    counts["short order hits"] += 1
            counts["marker primes"] += 1
        K = max((p - 1) // s for p, s in markers.items())
        # Recompute the two allowed sets using literal integer products.
        scalar_product = prod(2 * M for _, _, M in menus)
        short_product = prod(abs(A**j - B**j) for A, B, _ in menus for j in range(1, K + 1))
        for p, s in markers.items():
            if scalar_product % s == 0 or short_product % p == 0:
                individual.add(p)
        assert seen <= individual
        for modulus in (12, 35, 44):
            for p, fs in precursors.items():
                forced = prod(s ** min(e, factors(modulus, primes).get(s, 0)) for s, e in fs.items())
                assert forced == gcd(p - 1, modulus)
                assert prod(s**e for s, e in fs.items()) == p - 1
                counts["weighted factorizations"] += 1
        if x >= 1500:
            for a in (1, 5, 7, 11):
                assert any(p % 12 == a for p in markers.keys() - seen)
                counts["classes with all-negative transcripts"] += 1
    assert counts["exponent hits"] and counts["short order hits"]
    return counts


def input_polynomials():
    x = 2000
    primes = primes_through(2 * x)
    bases = [(2, 1, (2, -3, 1)), (-3, 2, (1, 1)), (5, 7, (6,)),
             (8, 1, (13, 2)), (19, 3, (-7, 0, 1))]
    good = {}
    for p in primes:
        if p <= x:
            continue
        s = max(factors(p - 1, primes))
        k = (p - 1) // s
        if s**5 > x**3 and all(coef[-1] % s and pow(A, k, p) != pow(B, k, p)
                                for A, B, coef in bases):
            good[p] = s
    missed = hits = roots = 0
    for p, s in good.items():
        for q in good:
            if p % 12 != 11 or q % 12 == 11:
                continue
            n = p * q
            any_hit = False
            for A, B, coef in bases:
                exponent = abs(sum(c * n**j for j, c in enumerate(coef)))
                for tested, partner, marker in ((p, q, s), (q, p, good[q])):
                    # The public rational (A+2N)/(B+N) specializes to A/B.
                    residual = pow(A + 2*n, exponent, tested) * pow(B + n, -exponent, tested) % tested
                    is_root = sum(c * partner**j for j, c in enumerate(coef)) % marker == 0
                    roots += is_root
                    if residual in (1, tested - 1):
                        assert is_root
                        hits += 1
                        any_hit = True
            missed += not any_hit
    assert hits and missed and roots >= hits
    return hits, roots, missed


if __name__ == "__main__":
    for case, count in sorted(replay().items()):
        print(case, count)
    print("polynomial hits, marker roots, mixed-class simultaneous misses", *input_polynomials())
