"""Enumerate certified square dependencies in a small, single-input quadratic fan."""

from itertools import combinations
from math import gcd, isqrt, prod

from sage.all import GF, Matrix, NumberField, PolynomialRing, QQ, ZZ


def parity(value, bound):
    factors = ZZ(abs(value)).factor()
    if any(prime > bound for prime, _ in factors):
        return None
    return ([-1] if value < 0 else []) + [p for p, e in factors if e % 2]


def evaluate(root, m, n):
    value = root.polynomial()(m)
    assert gcd(value.denominator(), n) == 1
    return int(value.numerator())*pow(int(value.denominator()), -1, n) % n


def match_roots(n, m, fields, marks):
    representatives = {}
    for i, field in enumerate(fields):
        local = [(r, z) for j, r, z in marks if i == j]
        for size in range(1, 4):
            for subset in combinations(local, size):
                value = prod((z for _, z in subset), start=field.one())
                if not value.is_square():
                    continue
                rational = ZZ(prod(r for r, _ in subset))
                key = rational.squarefree_part()
                scale = isqrt(int(rational // key))
                normalized = evaluate(value.sqrt(), m, n)*pow(scale, -1, n) % n
                assert (normalized**2-key) % n == 0
                first = representatives.setdefault(key, normalized)
                factor = gcd(normalized-first, n)
                if 1 < factor < n:
                    return factor
    return None


def replay(n):
    m = isqrt(n)
    x = PolynomialRing(QQ, "x").gen()
    columns = []
    marks = []
    fields = []
    for shift in (1, 2, 3):
        polynomial = x*x + (n//m % m + shift)*x + n % m - shift*m
        assert polynomial(m) == n
        if gcd(2*int(polynomial.discriminant()), n) != 1 or not polynomial.is_irreducible():
            continue
        field = NumberField(polynomial, "t")
        fields.append(field)
        for b in range(1, 4):
            for a in range(-13, 14):
                if gcd(a, b) != 1:
                    continue
                rational = a-b*m
                element = a-b*field.gen()
                norm = int(element.norm())
                if gcd(rational*norm, n) != 1:
                    continue
                rational_rows = parity(rational, 13)
                algebraic_rows = parity(norm, 13)
                if rational_rows is None or algebraic_rows is None:
                    continue
                columns.append({(0, p) for p in rational_rows} | {(shift, p) for p in algebraic_rows})
                marks.append((len(fields)-1, rational, element))

    rows = sorted(set().union(*columns))
    necessary = Matrix(GF(2), [[int(row in col) for col in columns] for row in rows])
    certified = splits = single = 0
    for dependency in necessary.right_kernel():
        selected = [marks[i] for i in dependency.nonzero_positions()]
        rational = prod(r for _, r, _ in selected)
        root_x = isqrt(rational)
        assert root_x*root_x == rational
        products = [field.one() for field in fields]
        for i, _, element in selected:
            products[i] *= element
        if any(not value.is_square() for value in products):
            continue
        y = prod(evaluate(value.sqrt(), m, n) for value in products) % n
        assert (root_x*root_x-y*y) % n == 0
        certified += 1
        if 1 < gcd(root_x-y, n) < n:
            splits += 1
            single += len({i for i, _, _ in selected}) == 1
    return len(marks), necessary.right_kernel().dimension(), certified, splits, single, match_roots(n, m, fields, marks)


if __name__ == "__main__":
    for n, expected in [(119, (16, 5, 16, 0, 0)), (341, (23, 10, 64, 32, 0))]:
        result = replay(n)
        assert result[:-1] == expected, (n, result)
        assert result[-1] in ((11, 31) if n == 341 else (None,))
        print(f"N={n}, marks={result[0]}, norm-parity nullity={result[1]}, "
              f"certified={result[2]}, splitting={result[3]}, single-field splits={result[4]}, matched factor={result[5]}")
