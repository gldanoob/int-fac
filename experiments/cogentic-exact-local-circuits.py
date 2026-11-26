"""Verify the four overlapping six-mark relations modulo 77."""

from fractions import Fraction
from math import gcd, prod

from sympy import Matrix, Poly, factorint, symbols


def main():
    modulus = 77
    x = symbols("x")
    fields = [
        # Origin, step, offset, affine slope, translation, discriminant, ratio, exponent.
        (38, 21, 16, 1, 0, 4524, Fraction(54, 23), 3),
        (12, 56, 33, 1, -77, 34365, Fraction(45, 32), -1),
        (9, 63, 44, -1, 154, 41820, Fraction(3, 80), -7),
        (23, 70, 9, -1, 77, 58557, Fraction(23, 100), 3),
    ]
    support = []
    ratio_product = Fraction(1)
    label_rows = []
    for a, step, offset, slope, shift, discriminant, expected_ratio, exponent in fields:
        plus = [slope * (a + j * step) + shift for j in range(3)]
        minus = [mark + slope * offset for mark in plus]
        marks = plus + minus
        numerator = Poly(prod(x - mark for mark in plus), x)
        denominator = Poly(prod(x - mark for mark in minus), x)
        polynomial = Poly((numerator - denominator).as_expr() / (slope * offset), x)
        assert polynomial.LC() == 3 and polynomial.is_primitive
        assert polynomial.discriminant() == discriminant and polynomial.is_irreducible
        assert polynomial.eval(0) % modulus == 0
        assert all(gcd(mark, modulus) == 1 for mark in marks)

        valuations = []
        for mark in marks:
            value = abs(polynomial.eval(mark))
            assert gcd(value, 3 * modulus) == 1
            factors = factorint(value)
            assert all(multiplicity == 1 for multiplicity in factors.values())
            valuations.append({(prime, mark % prime) for prime in factors})
        rows = [[1] * 6]
        for key in sorted(set.union(*valuations)):
            rows.append([int(key in column) for column in valuations])
        signed_marks = Matrix([1, 1, 1, -1, -1, -1])
        finite = Matrix(rows)
        assert finite * signed_marks == Matrix.zeros(len(rows), 1)
        assert finite.rank() == 5

        labels = [min(mark % modulus, -mark % modulus) for mark in marks]
        ratio = Fraction(prod(labels[:3]), prod(labels[3:]))
        assert ratio == expected_ratio
        residue = ratio.numerator * pow(ratio.denominator, -1, modulus) % modulus
        assert residue in (1, modulus - 1)
        num_factors = factorint(ratio.numerator)
        den_factors = factorint(ratio.denominator)
        label_rows.append([num_factors.get(p, 0) - den_factors.get(p, 0) for p in (2, 3, 5, 23)])
        ratio_product *= ratio ** exponent
        support.append(set(marks))

    assert [support[i] & support[j] for i, j in ((0, 1), (0, 2), (2, 3), (0, 3))] == [
        {80}, {38}, {-25}, {54}
    ]
    rows = Matrix(label_rows).T
    assert rows[1:, :].rank() == 3
    assert rows * Matrix([3, -1, -7, 3]) == Matrix([30, 0, 0, 0])
    assert ratio_product == 2 ** 30 and pow(2, 30, modulus) == 1
    factor = gcd(pow(2, 15, modulus) - 1, modulus)
    assert factor == 7
    print(f"Verified four rank-five field relations and the split {modulus} = {factor} × {modulus // factor}.")


if __name__ == "__main__":
    main()
