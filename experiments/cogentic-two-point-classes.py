"""Check the p-adic classes in both-coordinate Gaussian conditioning."""

from collections import Counter, defaultdict
from itertools import product
from math import gcd


def check_condition(prime, a, difference, root):
    modulus = prime**2
    prescribed = 1
    counts = defaultdict(Counter)
    for intercept, slope in product(range(modulus), repeat=2):
        if root is not None and (intercept + root * slope - prescribed) % prime:
            continue
        first = (intercept + a * slope) % modulus
        second = (first + difference * slope) % modulus
        counts[first][second] += 1

    feasible = 0
    for first in range(modulus):
        hits = root is not None and (root - a) % prime == 0
        if hits and (first - prescribed) % prime:
            assert not counts[first]
            continue
        if root is None or hits:
            representative = first
            period = gcd(difference, modulus)
        else:
            slope_class = (prescribed - first) * pow((root - a) % prime, -1, prime)
            representative = first + difference * slope_class
            period = gcd(difference * prime, modulus)
        expected = {y for y in range(modulus) if (y - representative) % period == 0}
        assert set(counts[first]) == expected
        assert len(set(counts[first].values())) == 1
        feasible += len(expected)
    return feasible


def main():
    systems = feasible = 0
    for prime in (3, 5, 7):
        for a in (1, 2, prime + 1):
            for difference in (1, 2, prime, 2 * prime, prime**2):
                for root in (None, *range(prime)):
                    feasible += check_condition(prime, a, difference, root)
                    systems += 1
    print(f"{systems} condition systems, {feasible} feasible residue-pair classes")


if __name__ == '__main__':
    main()
