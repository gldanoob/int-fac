"""Check sparse relation collection and modular pivot proposals on finite integer matrices."""

from fractions import Fraction
from random import Random


def pivot_lists(columns, prime):
    basis = []
    rows, selected = [], []
    for j, column in enumerate(columns):
        v = list(column) if prime else [Fraction(x) for x in column]
        for row, b in zip(rows, basis):
            c = v[row]
            v = [(x - c * y) % prime if prime else x - c * y for x, y in zip(v, b)]
        row = next((i for i, y in enumerate(v) if y), None)
        if row is not None:
            scale = pow(v[row], -1, prime) if prime else 1 / v[row]
            basis.append([(x * scale) % prime if prime else x * scale for x in v])
            rows.append(row)
            selected.append(j)
    return rows, selected


def inverse(mat):
    n = len(mat)
    arr = [[Fraction(x) for x in row] + [Fraction(i == j) for j in range(n)] for i, row in enumerate(mat)]
    for k in range(n):
        r = next(i for i in range(k, n) if arr[i][k])
        arr[k], arr[r] = arr[r], arr[k]
        c = arr[k][k]
        arr[k] = [x / c for x in arr[k]]
        for i in range(n):
            if i != k:
                c = arr[i][k]
                arr[i] = [x - c*y for x, y in zip(arr[i], arr[k])]
    return [x[n:] for x in arr]


def test_pivots():
    rng = Random(7327)
    mats = [[[1, 1, 0], [1, 0, 1], [0, 1, 1]]]
    for _ in range(28):
        cols = [[int(rng.randrange(4) == 0) for _ in range(7)] for _ in range(10)]
        cols += [cols[2][:], cols[4][:]]
        mats.append(cols)
    good = bad = identities = 0
    for columns in mats:
        exact_rank = len(pivot_lists(columns, None)[0])
        for p in [2, 3, 5, 7, 11, 13]:
            rows, piv = pivot_lists(columns, p)
            mat = [[columns[j][i] for j in piv] for i in rows]
            inv = inverse(mat)
            misses = 0
            for col in columns:
                coeffs = [sum(x * col[i] for x, i in zip(row, rows)) for row in inv]
                for i, c in enumerate(col):
                    misses += sum(x * columns[j][i] for j, x in zip(piv, coeffs)) != c
                    identities += 1
            assert (misses == 0) == (len(rows) == exact_rank)
            good += not misses
            bad += bool(misses)
    assert bad
    return good, bad, identities


def test_sieve():
    primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    marks_checked = retained = 0
    for c0, c1 in [(1, 1), (-4, 7), (11, -3)]:
        filters = []
        for f in (lambda a: a*a + c0, lambda a: 2*a + c1):
            products = [1] * 251
            for p in primes:
                for r in range(p):
                    if f(r) % p == 0:
                        for a in range(r, len(products), p):
                            products[a] *= p
            found = [f(a) != 0 and abs(f(a)) == products[a] for a in range(len(products))]
            for a, got in enumerate(found):
                n = abs(f(a))
                for p in primes:
                    if n and n % p == 0:
                        n //= p
                assert got == (n == 1)
                marks_checked += 1
            filters.append(found)
        retained += sum(p and q for p, q in zip(*filters))
    return marks_checked, retained


if __name__ == "__main__":
    print("exact-rank prime choices, rank drops, row equations:", *test_pivots())
    print("sieved mark checks, joint retained marks:", *test_sieve())
