"""Check the prime pools, exact-bit interpolation and small modular splits."""

from bisect import bisect_right
from math import gcd, isqrt, prod


def primes_through(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p :: p] = bytes((limit - p * p) // p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def smooth_pool(primes, bound, lower, upper):
    # Mark all multiples of a prime above the cutoff once, including prime powers.
    smooth = bytearray(b"\x01") * (upper + 1)
    for p in primes[bisect_right(primes, bound) : bisect_right(primes, upper)]:
        smooth[p::p] = bytes(upper // p)
    return [p for p in primes[bisect_right(primes, lower) : bisect_right(primes, upper)] if smooth[p - 1]]


def exact_length(core, lows, highs, bits):
    target = 1 << (bits - 1)
    total = prod(core)
    used = 0
    while total < target:
        total *= highs[used]
        used += 1
    for replaced in range(used):
        next_total = total // highs[replaced] * lows[replaced]
        if next_total < target:
            assert total.bit_length() == bits
            pads = lows[:replaced] + highs[replaced:used]
            return total, pads, replaced
        total = next_total
    raise AssertionError("the two prime pools did not bracket the target")


def public_split(n):
    # A simple deterministic modular witness search for the finite fixtures.
    bits = n.bit_length()
    primes = primes_through(bits)
    odd_scalar = 1
    for p in primes[1:]:
        power = p
        while power <= n // p:
            power *= p
        odd_scalar *= power
    factors = [n]
    for base in range(2, bits + 1):
        next_factors = []
        for part in factors:
            x = pow(base, odd_scalar, part)
            pieces = [part]
            for _ in range(bits):
                updated = []
                for v in pieces:
                    d = gcd(x - 1, v)
                    updated.extend(c for c in (d, v // d) if c > 1)
                pieces = updated
                if x == 1:
                    break
                x = x * x % part
            next_factors.extend(pieces)
        factors = next_factors
    return sorted(factors)


def main():
    scale = 65536
    primes = primes_through(2 * scale)
    length_checks = 0
    min_changes = 10**9
    max_changes = 0
    first = None
    for bits in range(8160, 8192):
        lows = smooth_pool(primes, bits, scale, 11 * scale // 10)
        highs = smooth_pool(primes, bits, 13 * scale // 10, 14 * scale // 10)
        pool = smooth_pool(primes, bits, 16 * scale // 10, 19 * scale // 10)
        # Keep sufficient filler at this finite scale to exercise interior steps.
        for start in range(0, 300, 25):
            core = pool[start : start + 360]
            n, pads, changes = exact_length(core, lows, highs, bits)
            all_factors = core + pads
            assert len(set(all_factors)) == len(all_factors) and prod(all_factors) == n
            assert [p for p in all_factors if 16 * scale < 10 * p <= 19 * scale] == core
            if first is None:
                first = (bits, len(pool), len(lows), len(highs), len(all_factors), min(all_factors), max(all_factors))
            min_changes, max_changes = min(min_changes, changes), max(max_changes, changes)
            length_checks += 1
    assert 0 <= min_changes < max_changes
    print("exact products, bit lengths, padding replacements", length_checks, 32, (min_changes, max_changes))
    print("first length, pool sizes, number and range of factors", first)
    semiprime_counts = []
    for bits in (27, 28):
        pmin = next(p for p in primes if p**3 > bits**4)
        all_primes = primes_through((1 << bits) // pmin)
        p_choices = [p for p in primes if bits**4 < p**3 <= bits**8]
        covered = set(smooth_pool(primes, bits, p_choices[0] - 1, p_choices[-1]))
        total_pairs = smooth_pairs = 0
        for p in p_choices:
            left, right = ((1 << (bits - 1)) - 1) // p, ((1 << bits) - 1) // p
            assert p < left
            partners = bisect_right(all_primes, right) - bisect_right(all_primes, left)
            total_pairs += partners
            smooth_pairs += partners * (p in covered)
        semiprime_counts.append((bits, len(p_choices), len(covered), total_pairs, smooth_pairs))
    print("semiprimes by length, candidate small primes, smooth primes, pairs, smooth pairs", semiprime_counts)
    fixtures = [[257, 331, 433, 487], [1009, 1153, 1297, 1459, 1621], [2593, 2689, 2917, 3457]]
    for known in fixtures:
        n = prod(known)
        assert public_split(n) == known
        for p in known:
            assert p in smooth_pool(primes, n.bit_length(), p - 1, p)
    print("N-only modular splits", [(prod(known), known) for known in fixtures])


if __name__ == "__main__":
    main()
