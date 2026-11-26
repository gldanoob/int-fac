"""Find and verify a mixed-field square certificate at N=209."""

from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


def is_square(value):
    return value >= 0 and isqrt(value)**2 == value


def find_cycle(n, anchor):
    candidates = [k for k in range(0, 2*isqrt(n)+1, 2) if gcd(k, n) == 1]
    for choices in combinations(candidates, 4):
        if anchor not in choices:
            continue
        radicands = [k*k-n for k in choices]
        total = prod(radicands)
        if not is_square(total) or any(is_square(a*b) for a, b in combinations(radicands, 2)):
            continue
        ratio = prod(choices) * pow(isqrt(total), -1, n) % n
        divisor = gcd(ratio-1, n)
        if 1 < divisor < n:
            return choices, ratio, divisor
    raise AssertionError("no splitting cycle in the fixed pencil")


def run():
    n = 209
    constructor = run_path(str(Path(__file__).with_name("cogentic-monic-pair.py")))
    degree = constructor["scheduled_degree"](n)
    m, f, g = constructor["check_pair"](n, degree)
    assert degree == 2
    derivative = sum(i*c*m**(i-1) for i, c in enumerate(g) if i)
    assert gcd(derivative, n) == 1
    choices, ratio, divisor = find_cycle(n, m + f[1]//2)
    assert choices == (12, 14, 18, 28)

    columns = (2, -130, 10, 46)
    denominators = (1, 13, 5, 115)
    assert all(gcd(value, n) == 1 for value in (*columns, *denominators))
    products = [prod(value for j, value in enumerate(columns) if mask >> j & 1)
                for mask in range(1 << len(columns))]
    assert [mask for mask, value in enumerate(products) if is_square(value)] == [0]
    root_residues = []
    for i, (k, denominator) in enumerate(zip(choices, denominators, strict=True)):
        constant = m*m - 2*k*m + n
        linear = 2*(k-m)
        assert constant % 4 == 2 and linear % 2 == 0 and gcd(2*k, n) == 1
        if k == m + f[1]//2:
            assert f == (constant, linear, 1)
        delta = k*k-n
        adjacent = (i+1) % len(columns)
        assert Fraction(delta, denominator**2) == Fraction(columns[adjacent], columns[i])
        kernel = [mask for mask, value in enumerate(products)
                  if is_square(value) or is_square(delta*value)]
        assert kernel == [0, (1 << i) | (1 << adjacent)]
        root_residues.append(k * pow(denominator, -1, n) % n)

    assert prod(root_residues) % n == ratio == 153
    assert ratio**2 % n == 1 and n % divisor == 0
    print(f"Found mixed cycle {choices}, root residue {ratio}, factors {divisor} and {n//divisor}")


if __name__ == "__main__":
    run()
