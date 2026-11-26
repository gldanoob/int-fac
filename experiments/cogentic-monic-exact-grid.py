"""Collect exact monic-grid ideal parities without factoring private cofactors."""

from collections import Counter, defaultdict
from math import gcd, isqrt
from pathlib import Path
from runpy import run_path

from sage.all import GF, QQ, ZZ, PolynomialRing, identity_matrix, matrix, vector

HERE = Path(__file__).resolve().parent
GRID = run_path(str(HERE / "cogentic-monic-large-primes.py"))
COMPOSITE = run_path(str(HERE / "cogentic-composite-private-parity.py"))
PowerBasis = COMPOSITE["PowerBasis"]
lattice = COMPOSITE["lattice"]
private_ideal_even = COMPOSITE["private_ideal_even"]


class NamedPrime:
    def __init__(self, polynomial, p):
        self.algebra = PowerBasis(polynomial)
        self.order = self.algebra.identity
        self.p = p
        self.field = GF(p)
        degree = polynomial.degree()
        exponent = p
        while exponent < degree:
            exponent *= p
        # The Frobenius kernel lifts to the radical used in the p-maximal order iteration.
        while True:
            self.inverse = self.order.inverse()
            self.one = vector(self.field, self.inverse[0])
            self.operators = [
                (self.order * self.algebra.multiplication(x) * self.inverse).change_ring(self.field)
                for x in self.order
            ]
            images = [self.power(x, exponent) for x in identity_matrix(self.field, degree)]
            frobenius = matrix(self.field, images)
            radical = self.lift_kernel(frobenius)
            overorder = self.algebra.colon(radical, radical)
            if overorder == self.order:
                break
            self.order = overorder

        images = [self.power(x, p) for x in identity_matrix(self.field, degree)]
        fixed = (matrix(self.field, images) - identity_matrix(self.field, degree)).left_kernel().basis()
        # The Frobenius-fixed algebra contains one primitive idempotent per local factor.
        idempotents = [self.one]
        for x in fixed:
            if len(idempotents) == len(fixed):
                break
            pieces = []
            for c in self.field:
                selector = self.one - self.power(x - c * self.one, p - 1)
                for e in idempotents:
                    piece = self.product(e, selector)
                    if not piece.is_zero():
                        pieces.append(piece)
            idempotents = pieces
        assert len(idempotents) == len(fixed)
        self.ideals = []
        for e in idempotents:
            ideal = self.lift_kernel(self.operator(e) * frobenius)
            degree = ZZ((ideal * self.inverse).det()).valuation(p)
            self.ideals.append((ideal, degree, []))

    def operator(self, x):
        return sum(coefficient * operator for coefficient, operator in zip(x, self.operators))

    def product(self, x, y):
        return x * self.operator(y)

    def power(self, x, exponent):
        result = self.one
        while exponent:
            if exponent % 2:
                result = self.product(result, x)
            exponent //= 2
            if exponent:
                x = self.product(x, x)
        return result

    def lift_kernel(self, action):
        rows = [vector(ZZ, x) for x in action.left_kernel().basis()]
        basis = lattice((self.p * self.algebra.identity).rows() + rows)
        return lattice(basis * self.order)

    def parity(self, a, b, norm_exponent):
        mark = vector(QQ, [a, -b] + [0] * (self.order.nrows() - 2))
        weighted = 0
        odd = []
        for j, (ideal, residue_degree, powers) in enumerate(self.ideals, 1):
            exponent = 0
            for k in range(norm_exponent // residue_degree):
                if k == len(powers):
                    previous = self.order if k == 0 else powers[-1][0]
                    current = lattice([
                        row for x in ideal for row in previous * self.algebra.multiplication(x)
                    ])
                    powers.append((current, current.inverse()))
                if not all(x in ZZ for x in mark * powers[k][1]):
                    break
                exponent += 1
            weighted += residue_degree * exponent
            if exponent % 2:
                odd.append(j)
        assert weighted == norm_exponent
        return odd


def bounded_parts(value, primes):
    valuation = []
    for p in primes:
        if value == 1:
            break
        if value % p == 0:
            exponent = 0
            while value % p == 0:
                exponent += 1
                value //= p
            valuation.append((p, exponent))
    return valuation, value


def collect(n, m, fields, cutoff, *, height):
    """Yield deterministic (primitive unit grid point, odd ideal row labels) pairs."""
    fields = tuple(tuple(field) for field in fields)
    if n < 2 or height < 1 or not fields or any(len(field) < 3 or field[-1] != 1 for field in fields):
        raise ValueError("expected a modulus, positive height and monic field polynomials of degree >= 2")
    if cutoff < max(2 * height**2, 2 * max(len(field) - 1 for field in fields)):
        raise ValueError("prime cutoff must cover the box determinants and twice each field degree")
    ring = PolynomialRing(QQ, "t")
    polynomials = tuple(ring([ZZ(value) for value in values]) for values in fields)
    if not all(polynomial.is_irreducible() for polynomial in polynomials):
        raise ValueError("expected irreducible field polynomials")
    discriminants = [polynomial.discriminant() for polynomial in polynomials]
    derivatives = [tuple(j * c for j, c in enumerate(values) if j) for values in fields]
    primes = tuple(GRID["primes_through"](cutoff))
    homogeneous = GRID["homogeneous"]
    named = {}
    for a in range(-height, height + 1):
        for b in range(1, height + 1):
            if gcd(a, b) != 1 or gcd(a - b * m, n) != 1:
                continue
            mark_parts = []
            for field, derivative, polynomial in zip(fields, derivatives, polynomials, strict=True):
                value = abs(homogeneous(field, a, b))
                if not value:
                    break
                factors, residual = bounded_parts(value, primes)
                if isqrt(residual)**2 != residual:
                    break
                if residual > 1 and gcd(residual, homogeneous(derivative, a, b)) != 1:
                    if not private_ideal_even(polynomial, a, b, residual):
                        break
                mark_parts.append(factors)
            else:
                rows = []
                for i, factors in enumerate(mark_parts, 1):
                    for p, exponent in factors:
                        if discriminants[i - 1] % p:
                            if exponent % 2:
                                rows.append((i, p, a * pow(b, -1, p) % p))
                        else:
                            key = (i, p)
                            if key not in named:
                                named[key] = NamedPrime(polynomials[i - 1], p)
                            rows.extend((i, p, j) for j in named[key].parity(a, b, exponent))
                yield (a, b), rows


def row_supports(columns):
    support = defaultdict(list)
    for slot, rows in enumerate(columns):
        for row in rows:
            support[tuple(row)].append(slot)
    return Counter((i, p, tuple(slots)) for (i, p, _), slots in support.items())


def replay():
    reference = run_path(str(HERE / "cogentic-all-ideal-reference.py"))["reference"]

    def compare(n, m, fields, cutoff, height):
        points = [(a, b) for a in range(-height, height + 1) for b in range(1, height + 1)
                  if gcd(a, b) == 1 and gcd(a - b * m, n) == 1]
        coefficients = [list(field) for field in fields]
        args = f"{coefficients},{[list(point) for point in points]},{cutoff}"
        _, rows, even = reference(f"all_ideal_reference({args})")
        expected = [(point, row) for point, row, flags in zip(points, rows, even, strict=True)
                    if all(flags)]
        actual = list(collect(n, m, fields, cutoff, height=height))
        assert [point for point, _ in actual] == [point for point, _ in expected]
        assert row_supports([row for _, row in actual]) == row_supports([row for _, row in expected])
        return actual

    m, left, right = GRID["CHECK_PAIR"](895, 2)
    actual = compare(895, m, (left, right), 800, 20)
    columns = GRID["parity_words"]([rows for _, rows in actual])
    basis = GRID["eliminate"](columns, (1 << j for j in range(len(columns))))
    assert (len(columns), len(basis)) == (151, 7)
    print("895: 151 columns and nullity 7 match the factorizing reference")

    seed = (2**13 - 1) * (2**31 - 1)**2
    for power in (1, 2):
        residual = seed**(2 * power)
        fields = ((residual, 0, 1), (residual, 0, 0, 1))
        actual = compare(residual + 1, 1, fields, 8, 1)
        assert actual == ([] if power == 1 else [((0, 1), [])])
        print(f"{residual.bit_length()}-bit square residual: {len(actual)} accepted columns")


if __name__ == "__main__":
    replay()
