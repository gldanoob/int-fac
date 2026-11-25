"""Check determinant and rational-rank recovery using streamed modular traces."""

from itertools import combinations, permutations, product
from math import prod
from random import Random


def characteristic(n, entry, p):
    traces = [0] * (n + 1)
    for start in range(n):
        vector = [int(i == start) for i in range(n)]
        for k in range(1, n + 1):
            vector = [sum(entry(i, j) * vector[j] for j in range(n)) % p
                      for i in range(n)]
            traces[k] = (traces[k] + vector[start]) % p
    elementary = [1]
    for k in range(1, n + 1):
        numerator = sum((-1)**(j - 1) * elementary[k - j] * traces[j]
                        for j in range(1, k + 1))
        elementary.append(numerator * pow(k, -1, p) % p)
    return elementary


def determinant(a):
    n = len(a)
    return sum((-1)**sum(col[i] > col[j] for i in range(n) for j in range(i + 1, n))
               * prod(a[i][col[i]] for i in range(n)) for col in permutations(range(n)))


def rational_rank(a):
    for k in range(min(len(a), len(a[0])), 0, -1):
        for rows in combinations(a, k):
            for cols in combinations(range(len(a[0])), k):
                if determinant([[row[j] for j in cols] for row in rows]):
                    return k
    return 0


def check():
    primes = [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
    rng = Random(251126)
    matrices = [[word[:5], word[5:]] for word in product(range(2), repeat=10)]
    matrices += [[[rng.randrange(-8, 9) for _ in range(cols)] for _ in range(rows)]
                 for rows, cols in [(3, 4), (4, 5), (5, 5)] for _ in range(12)]
    rank_drops = crt_checks = 0
    for a in matrices:
        rows, cols = len(a), len(a[0])
        true_rank = rational_rank(a)
        gram = lambda i, j: sum(a[i][k] * a[j][k] for k in range(cols))
        recovered = 0
        for p in primes:
            coeff = characteristic(rows, gram, p)
            rank = max(k for k, c in enumerate(coeff) if c)
            rank_drops += rank < true_rank
            recovered = max(recovered, rank)
        assert recovered == true_rank
        # Reconstruct a signed nonsymmetric minor without storing elimination data.
        size = min(rows, cols)
        minor = [row[:size] for row in a[:size]]
        direct = determinant(minor)
        value, modulus = 0, 1
        for p in primes:
            residue = characteristic(size, lambda i, j: minor[i][j], p)[-1]
            value += modulus * ((residue - value) * pow(modulus, -1, p) % p)
            modulus *= p
            if modulus > 2 * (size * 8)**size:
                break
        assert (value if 2 * value < modulus else value - modulus) == direct
        crt_checks += 1
    print(len(matrices), "rational ranks,", crt_checks, "signed minors,", rank_drops,
          "individual-prime drops")


if __name__ == "__main__":
    check()
