"""Check the exact residue-stratum energy identity and exceptional slopes."""

from collections import Counter
from itertools import product
from math import gcd, isqrt


def is_prime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n) + 1))


def autocorrelation(counts, ratio, modulus):
    return sum(count * counts[x * ratio % modulus] for x, count in counts.items())


def replay():
    checks = 0
    for p, q, auxiliary, bound in ((5, 7, 3, 49), (7, 11, 4, 39), (11, 13, 3, 31)):
        modulus = p * q
        for num_class, den_class in product(range(auxiliary), repeat=2):
            if gcd(den_class, auxiliary) != 1:
                continue
            numerators = [a for a in range(-bound, bound + 1) if a % auxiliary == num_class]
            denominators = [b for b in range(2, bound + 1)
                            if is_prime(b) and b % auxiliary == den_class and gcd(b, modulus) == 1]
            counts = Counter(a * pow(b, -1, modulus) % modulus
                             for a, b in product(numerators, denominators))
            for g in (1, p, q, modulus):
                local_modulus = modulus // g
                units = [r for r in range(local_modulus) if gcd(r, local_modulus) == 1]
                a_counts = Counter(a // g % local_modulus for a in numerators if gcd(a, modulus) == g)
                b_counts = Counter(b % local_modulus for b in denominators)
                energies = sum(autocorrelation(a_counts, r, local_modulus)
                               * autocorrelation(b_counts, r, local_modulus) for r in units)
                assert sum(counts[g*r] ** 2 for r in units) == energies
                mass = a_counts.total() * len(denominators)
                assert sum(counts[g*r] for r in units) == mass
                # Compare the centered second moments with integer-scaled means.
                cardinality = len(units)
                assert (sum((cardinality * counts[g*r] - mass) ** 2 for r in units)
                        == cardinality**2 * energies - cardinality * mass**2)
                checks += 1

    # Height lies strictly between the row prime scale and their product.
    modulus, bound = 11 * 13, 31
    narrow = [(a, b) for b in range(17, bound + 1) if is_prime(b)
              for a in range(1, b) if 5 * a < 4 * b]
    slopes = Counter(a * pow(b, -1, modulus) % modulus for a, b in narrow)
    assert slopes[0] == slopes[1] == 0 and len(narrow) > 0
    assert sum(slopes.values()) == len(narrow)
    # Signed primitive occupancy, including exceptional and nonunit residues.
    primitive = Counter(a * pow(b, -1, modulus) % modulus
                        for a, b in product(range(-bound, bound + 1), range(1, bound + 1))
                        if gcd(a, b) == 1 and gcd(b, modulus) == 1)
    assert max(primitive.values()) <= 16 * (1 + bound**2 / modulus)
    print(f"exact centered energy checks: {checks}; slopes 0 and 1 absent in the narrow fixture")


if __name__ == "__main__":
    replay()
