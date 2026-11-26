"""Replay homogeneous interpolation and balanced rational-side product bounds."""

from fractions import Fraction
from itertools import combinations_with_replacement
from math import factorial, gcd, prod
from random import Random


def det(first, second):
    return first[0] * second[1] - first[1] * second[0]


def value(coefficients, point):
    a, b = point
    degree = len(coefficients) - 1
    return sum(c * a**j * b ** (degree - j) for j, c in enumerate(coefficients))


def check_form(coefficients, marks, target):
    degree = len(coefficients) - 1
    evaluations = [value(coefficients, mark) for mark in marks]
    reconstructed = sum(
        y * prod(Fraction(det(target, other), det(mark, other))
                 for other in marks if other != mark)
        for mark, y in zip(marks, evaluations)
    )
    actual = value(coefficients, target)
    radius = max(abs(det(target, mark)) for mark in marks)
    maximum = max(map(abs, evaluations))
    assert actual == reconstructed and abs(actual) <= (degree + 1) * maximum * radius**degree
    coefficient_bound = sum(
        abs(y) * prod(Fraction(abs(other[0]) + abs(other[1]), abs(det(mark, other)))
                      for other in marks if other != mark)
        for mark, y in zip(marks, evaluations)
    )
    assert sum(map(abs, coefficients)) <= coefficient_bound
    if target[1] == 1 and all(b == 1 for _, b in marks):
        assert factorial(degree) * abs(actual) <= maximum * (2 * radius)**degree


def main():
    rng = Random(173)
    marks = [(a, b) for a in range(-6, 7) for b in range(1, 7) if gcd(a, b) == 1]
    marks.append((1, 0))
    projective = integer = 0
    for degree in range(1, 7):
        for _ in range(120):
            coefficients = [rng.randrange(-20, 21) for _ in range(degree + 1)]
            check_form(coefficients, rng.sample(marks, degree + 1), rng.choice(marks))
            projective += 1
            integer_marks = [(a, 1) for a in rng.sample(range(-15, 16), degree + 1)]
            check_form(coefficients, integer_marks, (rng.randrange(20, 50), 1))
            integer += 1
    # The slopes differ by as little as order M^-2.
    for degree in range(2, 10):
        for size in (101, 10007):
            near = [(size-1+j, size+j) for j in range(degree+1)]
            assert [((size*a-(size-1)*b)**degree - 2*(b-a)**degree) for a, b in near] == [
                j**degree-2 for j in range(degree+1)
            ]
            assert size**degree-2*(-1)**degree > (size//2)**degree
    exceptional_marks = range(1, 5)
    test = lambda x: 1 + 59 * prod(x - a for a in exceptional_marks)
    assert test(5) == 1417 == 13 * 109 and all(test(a) == 1 for a in exceptional_marks)
    assert 5 * 4**4 < test(5)
    products = 0
    for bound in range(2, 6):
        bounded = [(a, b) for a in range(-bound, bound + 1) for b in range(1, bound + 1) if gcd(a, b) == 1]
        for k in range(1, 5):
            target = (2 * (2 * bound)**k + 1, 2)
            determinants = [det(target, point) for point in bounded]
            seen = set()
            for factors in combinations_with_replacement(determinants, k):
                product = prod(factors)
                assert product not in seen
                seen.add(product)
            products += len(seen)
    print(f"{projective} projective and {integer} integer interpolations; sharp four-mark example at 1417")
    print(f"{products} distinct balanced products across sixteen height/order choices")


if __name__ == '__main__':
    main()
