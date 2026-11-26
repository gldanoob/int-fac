"""Plant two independent signed global squares at a growing-degree Pell center."""

from math import gcd
from pathlib import Path
from runpy import run_path

HERE = Path(__file__).resolve().parent
PLANTS = run_path(str(HERE / "cogentic-planted-norm-two.py"))
evaluate, multiply = (PLANTS[name] for name in ("evaluate", "multiply"))
scheduled_degree = PLANTS["BASE"]["scheduled_degree"]


def pell_center(threshold):
    y = u = 1
    while u < threshold:
        y, u = 3 * y + 4 * u, 2 * y + 3 * u
    return u, y


def planted_field(n, u, y, degree):
    residue = (y - pow(u, degree, n)) * pow(y, -2, n) % n
    value = (residue + 1) * pow(2 * u * (u - 1), -1, n) % n
    digits = []
    while value:
        value, digit = divmod(value, u)
        digits.append(digit)
    assert len(digits) <= degree - 4
    a = [-1] + [0] * (degree - 3)
    for j, digit in enumerate(digits):
        a[j + 1] -= 2 * digit
        a[j + 2] += 2 * digit
    assert evaluate(a, 1) == -1 and evaluate(a, u) % n == residue

    for s in range(4):
        shifted = a.copy()
        shifted[1] += 2 * s * u
        shifted[2] -= 2 * s * (u + 1)
        shifted[3] += 2 * s
        q = multiply((-1, 0, 2), shifted) + [1]
        h = multiply(q, q)
        h[0] += 1
        h[2] -= 2
        derivative = [j * coefficient for j, coefficient in enumerate(h) if j]
        tests = (evaluate(q, -u) - y, evaluate(q, -u) + y, evaluate(derivative, u))
        gcds = [gcd(test, n) for test in tests]
        for divisor in gcds:
            if 1 < divisor < n:
                return divisor
        if gcds == [1, 1, 1]:
            even, odd = h[::2], h[1::2]
            field = multiply(even, even)
            for j, coefficient in enumerate(multiply(odd, odd), 1):
                field[j] -= coefficient
            return q, h, field, s
    raise AssertionError("four shifts exhausted")


def plant(n):
    """Return a proper divisor or the Pell center and a pair of planted fields."""
    if n < 9 or n % 2 == 0:
        raise ValueError("expected an odd integer at least nine")
    h = scheduled_degree(n)
    u, y = pell_center(1 << max(1, (n.bit_length() - 1) // (2 * h)))
    assert 1 < u - 1 < u + 1 < n and 1 < y < n and y * y - 2 * u * u == -1
    for value in (u, y, u - 1, u + 1):
        divisor = gcd(value, n)
        if divisor > 1:
            return divisor
    degree, power = 7, u**3
    while power < n:
        degree += 2
        power *= u**2
    fields = []
    for k in (degree, degree + 2):
        result = planted_field(n, u, y, k)
        if isinstance(result, int):
            return result
        fields.append(result)
    return u, y, tuple(fields)


def verify(n, result):
    if isinstance(result, int):
        assert 1 < result < n and n % result == 0
        return
    u, y, fields = result
    m = u * u
    assert len(fields[0][2]) + 4 == len(fields[1][2])
    for q, h, field, _ in fields:
        assert q[-1] == h[-1] == field[-1] == 1
        assert q[0] == 1 and h[0] == 2 and field[0] == 4
        assert all(coefficient % 2 == 0 for coefficient in h[:-1])
        assert evaluate(q, 1) == 0 and evaluate(h, 1) == -1
        assert evaluate(q, u) % n == y and evaluate(h, u) % n == 0
        assert sum(c * 2**(len(field) - 1 - j) for j, c in enumerate(field)) == 1
        assert evaluate(field, m) % n == 0
        derivative = [j * coefficient for j, coefficient in enumerate(field) if j]
        assert gcd(evaluate(derivative, m), n) == 1
        even, odd = h[::2], h[1::2]
        inverse = pow(evaluate(odd, m), -1, n)
        root = -evaluate(even, m) * inverse % n
        assert root == u and evaluate(q, root) % n == y
        assert root**2 % n == m % n and y**2 % n == (2 * m - 1) % n


def replay():
    count = factors = repairs = 0
    inputs = (*range(9, 400, 2), (2**61 - 1) * (2**89 - 1),
              (2**521 - 1) * (2**607 - 1), (2**4423 - 1) * (2**9689 - 1))
    for n in inputs:
        result = plant(n)
        verify(n, result)
        if isinstance(result, int):
            factors += 1
        else:
            count += 1
            _, _, fields = result
            repairs += any(s for _, _, _, s in fields)
    assert count and factors and repairs
    print(f"{count} planted pairs, {factors} proper gcds, {repairs} pairs with a derivative repair")


if __name__ == "__main__":
    replay()
