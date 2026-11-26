#!/usr/bin/env python3
"""Verify a growing-degree Pell split using two fixed ordinary marks."""

from math import gcd, isqrt


def pell_values(m, j):
    """Compute V + U sqrt(C) using the integral three-step recurrence."""
    y = 2*m+1
    c = y*y-4
    u, v = (c+y)//2, c*(y+1)//2
    a, b = (y**3-3*y)//2, (y*y-1)//2
    for _ in range((j-1)//3):
        u, v = a*u+b*v, a*v+b*c*u
    return c, u, v


def lift_even(m, value, degree):
    """Lift an even integer to a monic polynomial congruent to X^degree+1 mod 2."""
    remainder = m**degree-value
    coefficients = []
    for _ in range(degree):
        remainder, digit = divmod(remainder, m)
        coefficients.append(-digit)
    assert remainder == 0
    coefficients.append(1)
    for i in range(degree-1, 0, -1):
        if coefficients[i] % 2:
            coefficients[i] += 1
            coefficients[i-1] -= m
    return coefficients


def evaluate(coefficients, m):
    value = 0
    for coefficient in reversed(coefficients):
        value = value*m+coefficient
    return value


def field_polynomial(root):
    coefficients = [0]*(2*len(root)-1)
    for i, a in enumerate(root):
        for j, b in enumerate(root):
            coefficients[i+j] += a*b
    coefficients[0] -= 3
    coefficients[1] += 4
    coefficients[2] += 4
    return coefficients


def check(m, j):
    c, u, v = pell_values(m, j)
    n = u*u+c
    assert u % 2 == v % 2 == 0 and gcd(u*v, n) == 1
    assert v*v+c == c*n and 0 < v-u < v+u < n
    first, second = gcd(v-u, n), gcd(v+u, n)
    assert 1 < first < n and first*second == n

    degree = 1
    while m**degree <= u:
        degree += 1
    other = degree+1
    while m**other <= v:
        other += 1
    for value, size, multiplier in ((u, degree, 1), (v, other, c)):
        root = lift_even(m, value, size)
        polynomial = field_polynomial(root)
        assert evaluate(root, m) == value and max(map(abs, root)) <= 2*m
        assert polynomial[-1] == 1 and polynomial[0] % 4 == 2
        assert all(coefficient % 2 == 0 for coefficient in polynomial[:-1])
        assert evaluate(polynomial, m) == multiplier*n
    return n, first, second, 2*degree, 2*other


def recover(n):
    """Recognize a Pell input from its integer value and return a proper split."""
    for j in range(1, n.bit_length()+1, 3):
        lo, hi = 1, (isqrt(n)-1)//2
        while lo <= hi:
            index = (lo+hi)//2
            m = 2*index+1
            c, u, v = pell_values(m, j)
            if u*u+c == n:
                factor = gcd(v-u, n)
                assert 1 < factor < n
                return factor
            if u*u+c < n:
                lo = index+1
            else:
                hi = index-1
    return None


if __name__ == "__main__":
    assert check(3, 1) == (721, 7, 103, 6, 10)
    assert recover(721) == 7 and recover(723) is None
    for m, j in ((3, 1), (17, 4), (1+(1 << 100), 7), (1+(1 << 521), 13)):
        n, first, second, d, e = check(m, j)
        if n.bit_length() <= 50:
            assert recover(n) in (first, second)
        print(f"{n.bit_length()} bits, degrees {d} and {e}, factor bits "
              f"{first.bit_length()} and {second.bit_length()}")
