"""Check disjoint-bin atom weights and sign-prefix bounds in finite cases."""

from collections import Counter
from itertools import combinations, product
from math import isqrt, prod


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def is_odd_smooth(n, primes):
    if n % 2 == 0:
        return False
    for r in primes:
        while n % r == 0:
            n //= r
    return n == 1


def bin_atoms():
    centers = (29, 57, 113)
    bins = [[r for r in range(4 * z // 5 + 1, 6 * z // 5 + 1) if is_prime(r)]
            for z in centers]
    labels = {r: i for i, block in enumerate(bins) for r in block}
    assert len(labels) == sum(map(len, bins))
    smooth_primes = [r for r in range(3, 257, 2) if is_prime(r)]
    slots = 3
    target = 37_000_000
    cofactors = {}
    weight = Counter()
    assignments = 0
    for indices in product(range(len(bins)), repeat=slots):
        scale = prod(centers[i] for i in indices)
        low = (target + scale - 1) // scale
        high = (105 * target) // (100 * scale)
        allowed = {m for m in range(low, high + 1) if is_odd_smooth(m, smooth_primes)}
        cofactors[indices] = allowed
        for primes in product(*(bins[i] for i in indices)):
            rprod = prod(primes)
            # v times the unnormalized mass with bit length replacing log.
            log_weight = prod(r.bit_length() for r in primes)
            for m in allowed:
                assignments += 1
                weight[m * rprod] += log_weight

    for v, exact in weight.items():
        divisors = [r for r in labels if v % r == 0]
        assert exact <= (len(divisors) * max(r.bit_length() for r in labels)) ** slots
        reconstructed = 0
        for primes in product(divisors, repeat=slots):
            m, remainder = divmod(v, prod(primes))
            if remainder == 0 and m in cofactors[tuple(labels[r] for r in primes)]:
                reconstructed += prod(r.bit_length() for r in primes)
        assert reconstructed == exact
    return assignments, len(weight), sum(weight.values()), len(bins) ** slots


def sign_prefixes():
    checks = disagreements = 0
    for p in range(11, 130, 2):
        if not is_prime(p):
            continue
        chi = [-1] * p
        chi[0] = 0
        for x in range(1, p):
            chi[x * x % p] = 1
        for h in range(1, 6):
            for roots in combinations(range(6), h):
                for signs in product((-1, 1), repeat=h):
                    missing = sum(all(chi[(x - a) % p] != s for a, s in zip(roots, signs))
                                  for x in range(p))
                    constant = p + (h << h)
                    sqrt_coefficient = sum(max(len(subset) - 1, 0)
                                           for j in range(1, h + 1)
                                           for subset in combinations(roots, j))
                    assert sqrt_coefficient == (h - 2) * 2 ** (h - 1) + 1
                    lhs = (missing << h) - constant
                    assert lhs <= 0 or lhs * lhs <= p * sqrt_coefficient ** 2
                    checks += 1
                    disagreements += missing
    return checks, disagreements


if __name__ == "__main__":
    print("assignments, distinct atoms, total integer weights, averaging denominator",
          *bin_atoms())
    print("exact one-sign inequalities and their missed-parameter total", *sign_prefixes())
