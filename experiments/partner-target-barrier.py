"""Realize the complete-graph and partial-graph oracle obstructions exactly."""

from itertools import combinations
from math import isqrt


def probe(n, counter, history):
    return (n * (counter + 1) ** 3 + (n >> (counter % 6))
            + 41 * counter + sum((i + 1) * response for i, response in enumerate(history)))


def realize(dimension, degree, tries):
    primes = [p for p in range(51, 102)
              if p > 50 and not any(p % i == 0 for i in range(2, isqrt(p) + 1))]
    n = len(primes)
    edges = [(p, q) for i, p in enumerate(primes) for j, q in enumerate(primes)
             if i < j and (degree == n - 1 or min(j - i, n - j + i) <= degree // 2)]
    prohibited = {p: set() for p in primes}
    for p, q in edges:
        for a in range(tries):
            code = probe(p * q, a, [0] * a)
            for r in (p, q):
                prohibited[r].add(code % r ** dimension)
    targets = {}
    for p in primes:
        size = (p ** dimension + 3) // 4
        allowed = (a for a in range(p ** dimension) if a not in prohibited[p])
        targets[p] = {next(allowed) for _ in range(size)}

    forced = set(edges)
    total_misses = 0
    for p, q in combinations(primes, 2):
        history = []
        for a in range(tries):
            code = probe(p * q, a, history)
            response = ((code % p ** dimension in targets[p])
                        + 2 * (code % q ** dimension in targets[q]))
            history.append(response)
        if not any(history):
            total_misses += 1
        if (p, q) in forced:
            assert not any(history)
    return n, len(edges), total_misses, sum(map(len, targets.values()))


if __name__ == "__main__":
    print("dimension 1: vertices, forced misses, actual misses, target labels",
          *realize(1, 4, 7))
    print("dimension 2: vertices, forced misses, actual misses, target labels",
          *realize(2, 10, 35))
