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


def lift_value(m, value, parity):
    """Lift an integer to a monic polynomial with the prescribed parity."""
    degree = len(parity)-1
    remainder = m**degree-value
    coefficients = []
    for _ in range(degree):
        remainder, digit = divmod(remainder, m)
        coefficients.append(-digit)
    assert remainder == 0
    coefficients.append(1)
    for i in range(degree-1, 0, -1):
        if coefficients[i] % 2 != parity[i]:
            coefficients[i] += 1
            coefficients[i-1] -= m
    assert coefficients[0] % 2 == parity[0]
    return coefficients


def evaluate(coefficients, m):
    value = 0
    for coefficient in reversed(coefficients):
        value = value*m+coefficient
    return value


def multiply(left, right):
    coefficients = [0]*(len(left)+len(right)-1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            coefficients[i+j] += a*b
    return coefficients


def check_eisenstein(coefficients):
    assert coefficients[-1] == 1 and coefficients[0] % 4 == 2
    assert all(coefficient % 2 == 0 for coefficient in coefficients[:-1])


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
        root = lift_value(m, value, [1]+[0]*(size-1)+[1])
        polynomial = multiply(root, root)
        for i, coefficient in enumerate((-3, 4, 4)):
            polynomial[i] += coefficient
        assert evaluate(root, m) == value and max(map(abs, root)) <= 2*m
        check_eisenstein(polynomial)
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


def check_exact_pair(m, j):
    y = (m+1)//2
    c = 4*(y*y-1)
    a = 2*y*y-1
    u = quotient = 1
    for _ in range(j//2):
        u, quotient = a*u+y*c*quotient, a*quotient+y*u
    v = c*quotient
    n = u*u+c
    assert u % 2 == 1 and gcd(u*v, n) == 1
    assert v*v+c == c*n and 0 < v-u < v+u < n
    first, second = gcd(v-u, n), gcd(v+u, n)
    assert 1 < first < n and first*second == n

    k = 2
    while m**k <= u:
        k += 1
    degree = k+(quotient-k-1) % 2
    assert m**degree > quotient
    p = lift_value(m, u, [1, 1]+[0]*(k-2)+[1])
    q = lift_value(m, quotient, [1]*(degree+1))
    assert max(map(abs, p+q)) <= 2*m
    c_poly = [-3, 2, 1]
    f = multiply(p, p)
    for i, coefficient in enumerate(c_poly):
        f[i] += coefficient
    g = multiply(c_poly, multiply(q, q))
    g[0] += 1
    check_eisenstein(f)
    check_eisenstein(g)
    assert len(f) < len(g) and evaluate(f, m) == evaluate(g, m) == n
    assert evaluate(p, m) == u and evaluate(multiply(c_poly, q), m) == v
    return n, first, second, len(f)-1, len(g)-1


if __name__ == "__main__":
    assert check(3, 1) == (721, 7, 103, 6, 10)
    assert recover(721) == 7 and recover(723) is None
    for m, j in ((3, 1), (17, 4), (1+(1 << 100), 7), (1+(1 << 521), 13)):
        n, first, second, d, e = check(m, j)
        if n.bit_length() <= 50:
            assert recover(n) in (first, second)
        print(f"{n.bit_length()} bits, degrees {d} and {e}, factor bits "
              f"{first.bit_length()} and {second.bit_length()}")
    assert check_exact_pair(5, 2) == (12801, 17, 753, 6, 8)
    for m, j in ((5, 2), (17, 4), (1+(1 << 80), 8), (1+(1 << 521), 14)):
        n, first, second, d, e = check_exact_pair(m, j)
        print(f"exact shared value, {n.bit_length()} bits, degrees {d} and {e}, "
              f"factor bits {first.bit_length()} and {second.bit_length()}")
