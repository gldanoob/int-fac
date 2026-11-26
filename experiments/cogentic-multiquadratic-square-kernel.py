"""Compute an exact binary square kernel in one explicit multiquadratic field.

Input JSON contains integer radicands and columns of rational coefficients.
Coefficient index s denotes the product of radicals selected by the bits of s.
Output masks index the input columns. Run without input for the Sage replay.
"""

import argparse
import json
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt, prod
from pathlib import Path


def support(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def binary_kernel(columns):
    pivots, basis = {}, []
    for i, column in enumerate(columns):
        mask = 1 << i
        while column and column.bit_length() in pivots:
            old_column, old_mask = pivots[column.bit_length()]
            column ^= old_column
            mask ^= old_mask
        if column:
            pivots[column.bit_length()] = column, mask
        else:
            basis.append(mask)
    return basis


def combine(mask, basis):
    result = 0
    for i in support(mask):
        result ^= basis[i]
    return result


def intersection(left, right):
    # Each relation between the two bases represents one vector in both spans.
    left_bits = (1 << len(left)) - 1
    return [combine(mask & left_bits, left) for mask in binary_kernel(left + right)]


def rational_kernel(values):
    integers = [v.numerator * v.denominator for v in map(Fraction, values)]
    if not all(integers):
        raise ValueError("squareclasses require nonzero rational values")
    atoms = {abs(v) for v in integers} - {1}
    while True:
        for a, b in combinations(sorted(atoms), 2):
            common = gcd(a, b)
            if common > 1:
                atoms.difference_update((a, b))
                atoms.update((common, a//common, b//common))
                atoms.discard(1)
                break
        else:
            break
    columns = []
    rows = [(atom, 0 if isqrt(atom)**2 == atom else 1 << i) for i, atom in enumerate(sorted(atoms), 1)]
    for value in integers:
        column, remaining = int(value < 0), abs(value)
        for atom, bit in rows:
            while remaining % atom == 0:
                remaining //= atom
                column ^= bit
        assert remaining == 1
        columns.append(column)
    return binary_kernel(columns)


class RadicalField:
    """Exact coordinates indexed by subsets of the radicands."""

    def __init__(self, radicands):
        self.radicands = tuple(radicands)
        self.size = 1 << len(self.radicands)
        self.products = [prod(self.radicands[i] for i in support(mask)) for mask in range(self.size)]
        self.lower = RadicalField(self.radicands[:-1]) if self.radicands else None

    def element(self, coefficients):
        value = tuple(map(Fraction, coefficients))
        if len(value) != self.size:
            raise ValueError("wrong number of tensor basis coefficients")
        return value

    def multiply(self, left, right):
        result = [Fraction(0)] * self.size
        terms = [(j, b) for j, b in enumerate(right) if b]
        for i, a in enumerate(left):
            if not a:
                continue
            for j, b in terms:
                result[i ^ j] += a*b*self.products[i & j]
        return tuple(result)

    def product(self, columns, mask):
        value = (Fraction(1),) + (Fraction(0),) * (self.size - 1)
        for i in support(mask):
            value = self.multiply(value, columns[i])
        return value

    def quadratic_parts(self, value):
        half = self.size // 2
        a, b = value[:half], value[half:]
        aa = self.lower.multiply(a, a)
        bb = self.lower.multiply(b, b)
        norm = tuple(x - self.radicands[-1]*y for x, y in zip(aa, bb, strict=True))
        return a, b, norm

    def inverse(self, value):
        if not self.lower:
            return (1/value[0],)
        a, b, norm = self.quadratic_parts(value)
        reciprocal = self.lower.inverse(norm)
        constant = self.lower.multiply(a, reciprocal)
        radical = self.lower.multiply(tuple(-x for x in b), reciprocal)
        return constant + radical

    def square_root(self, value):
        if not self.lower:
            v = value[0]
            if v < 0:
                return None
            a, b = isqrt(v.numerator), isqrt(v.denominator)
            return (Fraction(a, b),) if a*a == v.numerator and b*b == v.denominator else None
        a, b, norm = self.quadratic_parts(value)
        if not any(b):
            zero = (Fraction(0),) * len(b)
            root = self.lower.square_root(a)
            if root is not None:
                return root + zero
            root = self.lower.square_root(tuple(x/self.radicands[-1] for x in a))
            return None if root is None else zero + root
        t = self.lower.square_root(norm)
        if t is None:
            return None
        for sign in (1, -1):
            root = self.lower.square_root(tuple((x + sign*y)/2 for x, y in zip(a, t, strict=True)))
            if root is not None and any(root):
                half_b = tuple(x/2 for x in b)
                return root + self.lower.multiply(half_b, self.lower.inverse(root))
        return None

    def norm_columns(self, columns, sign):
        """Project relative norms into a monomial basis of the fixed field."""
        pivot = sign & -sign
        generators = []
        for i in range(len(self.radicands)):
            bit = 1 << i
            if bit != pivot:
                generators.append(bit ^ (pivot if bit & sign else 0))
        fixed = RadicalField([self.products[mask] for mask in generators])
        embedding = [(0, 1)]
        for mask in generators:
            embedding += [(old ^ mask, scalar*self.products[old & mask]) for old, scalar in embedding]
        norms = []
        for value in columns:
            image = tuple(-x if (i & sign).bit_count() % 2 else x for i, x in enumerate(value))
            norm = self.multiply(value, image)
            norms.append(tuple(norm[i]/scalar for i, scalar in embedding))
        return fixed, norms

    def rational_representative(self, value):
        """Descend a squareclass already certified to come from the rationals."""
        field = self
        while field.lower:
            a, _, norm = field.quadratic_parts(value)
            t = field.lower.square_root(norm)
            if t is None:
                raise ArithmeticError("the relative norm does not have a root")
            value = tuple(2*(x+y) for x, y in zip(a, t, strict=True))
            if not any(value):
                value = tuple(2*(x-y) for x, y in zip(a, t, strict=True))
            field = field.lower
        return value[0]

    def square_kernel(self, columns):
        if not self.lower:
            return rational_kernel([value[0] for value in columns])
        signs = [1 << i for i in range(len(self.radicands))]
        basis = [1 << i for i in range(len(columns))]
        for sign in signs + [a ^ b for a, b in combinations(signs, 2)]:
            fixed, norms = self.norm_columns(columns, sign)
            basis = intersection(basis, fixed.square_kernel(norms))
            if not basis:
                return []
        representatives = [self.rational_representative(self.product(columns, mask)) for mask in basis]
        rational_basis = rational_kernel([*representatives, *self.radicands])
        bits = (1 << len(basis)) - 1
        return [combine(mask & bits, basis) for mask in rational_basis]


def replay():
    from sage.all import NumberField, PolynomialRing, QQ

    field = RadicalField((2, -2, 3))
    a, b, c, seed, rational = [
        field.element(row) for row in (
            (0, 1, 0, 0, 0, 0, 0, 0),
            (0, 0, 1, 0, 0, 0, 0, 0), (0, 0, 0, 0, 1, 0, 0, 0),
            (1, 1, 1, 0, 1, 0, 0, 0), (7, 0, 0, 0, 0, 0, 0, 0),
        )
    ]
    square = field.multiply(seed, seed)
    x = PolynomialRing(QQ, "x").gen()

    def reference(radicals):
        tower = NumberField([x*x-d for d in radicals], names=tuple(f"a{i}" for i in range(len(radicals))))
        absolute = tower.absolute_field("z")
        generators = [absolute.structure()[1](g) for g in tower.gens()]
        return [prod((generators[i] for i in support(mask)), start=absolute.one())
                for mask in range(1 << len(radicals))]

    def to_sage(value, basis):
        return sum(QQ(v.numerator)/v.denominator * b for v, b in zip(value, basis, strict=True))

    def check_kernel(columns, coefficients, basis):
        span = {0}
        for mask in coefficients:
            assert mask not in span
            span |= {mask ^ word for word in span}
        exact = [to_sage(value, basis) for value in columns]
        one = exact[0].parent().one()
        for word in range(1 << len(columns)):
            assert (word in span) == prod((exact[i] for i in support(word)), start=one).is_square()
        return span

    seven_square = field.multiply(rational, square)
    columns = [a, b, c, square, rational, seven_square, field.multiply(a, rational),
               field.element((0, 0, 0, 0, 0, 0, 0, "1/5"))]
    sage_basis = reference(field.radicands)
    decisions = []
    for sign, generators in ((1, (2, 4)), (2, (1, 4)), (4, (1, 2)),
                             (3, (3, 4)), (5, (2, 5)), (6, (1, 6))):
        fixed, norms = field.norm_columns(columns, sign)
        x0, x1 = (sage_basis[i] for i in generators)
        embedded = [sage_basis[0], x0, x1, x0*x1]
        conjugate_basis = [v if (i & sign).bit_count() % 2 == 0 else -v for i, v in enumerate(sage_basis)]
        for value, norm in zip(columns, norms, strict=True):
            assert to_sage(norm, embedded) == to_sage(value, sage_basis)*to_sage(value, conjugate_basis)
        span = check_kernel(norms, fixed.square_kernel(norms), reference(fixed.radicands))
        decisions.append(1 in span)
    assert decisions == [True, True, True, False, True, True]

    representative = field.rational_representative(seven_square)
    value = to_sage(seven_square, sage_basis)
    assert not value.is_square() and (value/QQ(representative)).is_square()
    basis = field.square_kernel(columns)
    for mask in basis:
        value = field.product(columns, mask)
        root = field.square_root(value)
        assert root is not None and field.multiply(root, root) == value
    check_kernel(columns, basis, sage_basis)
    print(f"Degree eight: six relative kernels and the full kernel match Sage on {1 << len(columns)} masks each")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, nargs="?", help="JSON with independent integer radicands and coefficient columns")
    args = parser.parse_args()
    if args.input is None:
        replay()
        return
    data = json.loads(args.input.read_text(), parse_float=Fraction)
    radicands = data["radicands"]
    if any(type(d) is not int for d in radicands) or rational_kernel(radicands):
        raise ValueError("expected independent nonzero integer radicands")
    field = RadicalField(radicands)
    columns = [field.element(coefficients) for coefficients in data["columns"]]
    if any(not any(value) for value in columns):
        raise ValueError("squareclasses require nonzero field elements")
    print(json.dumps({"basis": field.square_kernel(columns)}))


if __name__ == "__main__":
    main()
