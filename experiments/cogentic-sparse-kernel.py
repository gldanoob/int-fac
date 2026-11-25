"""Verify sparse Krylov nullspace recovery with exact binary extension fields."""
from itertools import product
from random import Random


def multiply(x, y):
    value = 0
    while y:
        if y & 1:
            value ^= x
        x <<= 1
        if x & 16:
            x ^= 19  # X^4+X+1 is irreducible over F_2.
        y >>= 1
    return value


mul = [[multiply(x, y) for y in range(16)] for x in range(16)]
inverse = [0] + [row.index(1) for row in mul[1:]]


def dot(x, y):
    value = 0
    for a, b in zip(x, y):
        value ^= mul[a][b]
    return value


def recurrence(s):
    # Coefficients first describe s[t] + c[1]s[t-1] + ... = 0.
    c = [1] + [0] * len(s)
    old = c.copy()
    degree, shift, previous = 0, 1, 1
    for t, item in enumerate(s):
        error = item
        for i in range(1, degree + 1):
            error ^= mul[c[i]][s[t-i]]
        if not error:
            shift += 1
            continue
        saved = c.copy()
        scale = mul[error][inverse[previous]]
        for j in range(len(c) - shift):
            c[j + shift] ^= mul[scale][old[j]]
        if 2 * degree <= t:
            degree = t + 1 - degree
            old, previous, shift = saved, error, 1
        else:
            shift += 1
    return c[:degree+1][::-1]


def binary_rank(words):
    pivots = {}
    for word in words:
        while word:
            high = word.bit_length() - 1
            if high not in pivots:
                pivots[high] = word
                break
            word ^= pivots[high]
    return len(pivots)


def verify_system(rows, n, rng):
    row_vectors = [[(row >> j) & 1 for j in range(n)] for row in rows]
    columns = list(zip(*row_vectors))
    sparse_rows = [[j for j in range(n) if row >> j & 1] for row in rows]
    found = 0
    for attempt in range(16):
        d = [rng.randrange(16) for _ in rows]
        e = [rng.randrange(16) for _ in range(n)]

        def apply_c(v):
            av = []
            for entry, indices in zip(d, sparse_rows):
                val = 0
                for j in indices:
                    val ^= v[j]
                av.append(mul[entry][val])
            return [mul[ej][dot(col, av)] for ej, col in zip(e, columns)]

        components = []
        for _ in range(3):
            x = [rng.randrange(16) for _ in range(n)]
            probe = [rng.randrange(16) for _ in range(n)]
            term = apply_c(x)
            samples = []
            for _ in range(2*n):
                samples.append(dot(probe, term))
                term = apply_c(term)
            h = recurrence(samples)
            if not h[0]:
                continue
            # The nonzero scalar denominator does not affect membership.
            projected = [0] * n
            for coefficient in reversed(h):
                projected = [a ^ mul[coefficient][b] for a,b in zip(apply_c(projected), x)]
            if any(dot(row, projected) for row in row_vectors):
                continue
            for bit in range(4):
                components.append(sum(((z >> bit) & 1) << j for j, z in enumerate(projected)))
        assert all((row & w).bit_count() % 2 == 0 for row in rows for w in components)
        found = binary_rank(components)
        if found >= 3:
            return attempt + 1, found
    raise AssertionError((rows, n, found))


if __name__ == "__main__":
    rng = Random(2625)
    systems = [(list(rows), 5) for rows in product(range(32), repeat=2)]
    for n in range(6, 14):
        for density in (1, 2, 3, 8):
            for _ in range(3):
                rows = [sum((rng.randrange(density) == 0) << j for j in range(n))
                        for _ in range(n-3)]
                systems.append((rows, n))
    counts = [verify_system(rows, n, rng) for rows, n in systems]
    print("binary matrices, first-try successes, maximum attempts, minimum verified rank",
          len(counts), sum(a == 1 for a, _ in counts), max(a for a, _ in counts),
          min(r for _, r in counts))
