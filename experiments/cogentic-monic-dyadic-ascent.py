"""Recover exact joint squares using the Eisenstein field's dyadic completion."""

from math import gcd, isqrt, prod
from subprocess import TimeoutExpired
from time import monotonic


def evaluate(coefficients, x):
    value = 0
    for coefficient in reversed(coefficients):
        value = value*x+coefficient
    return value


def multiply(field, left, right, modulus=None):
    degree = len(field)-1
    out = [0]*(2*degree-1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i+j] += a*b
    for i in range(2*degree-2, degree-1, -1):
        for j in range(degree):
            out[i-degree+j] -= out[i]*field[j]
    out = out[:degree]
    return out if modulus is None else [c % modulus for c in out]


def multiply_mark(field, value, a, b):
    top = -b*value[-1]
    return [a*c-b*(value[j-1] if j else 0)-top*field[j] for j, c in enumerate(value)]


def valuation(value):
    degree = len(value)
    return min((degree*((c & -c).bit_length()-1)+j for j, c in enumerate(value) if c),
               default=float("inf"))


def local_root_mod_eight(field, target):
    degree = len(field)-1
    target = [c % 8 for c in target]
    root = [1]+[0]*(degree-1)
    power = multiply_mark(field, root, 0, -1)
    for k in range(1, 2*degree):
        square = multiply(field, root, root, 8)
        residual = valuation([(a-b) % 8 for a, b in zip(target, square)])
        threshold = 2*k if k < degree else k+degree
        if k == degree:
            threshold += 1
        if residual < threshold:
            return None
        if k != degree and residual == threshold:
            root = [(a+b) % 8 for a, b in zip(root, power)]
        power = [c % 8 for c in multiply_mark(field, power, 0, -1)]
    if multiply(field, root, root, 8) != target:
        raise ArithmeticError("invalid dyadic root modulo eight")
    return root


def inverse_unit(field, unit, bits):
    degree = len(field)-1
    inverse = [1]+[0]*(degree-1)
    for i in range(1, degree):
        inverse[i] = sum(unit[j]*inverse[i-j] for j in range(1, i+1)) % 2
    precision = 1
    while precision < bits:
        precision = min(2*precision, bits)
        modulus = 1 << precision
        correction = [-c for c in multiply(field, unit, inverse, modulus)]
        correction[0] += 2
        inverse = multiply(field, inverse, correction, modulus)
    return inverse


def check_deadline(deadline):
    if deadline is not None and monotonic() >= deadline:
        raise TimeoutExpired("dyadic square oracle", 0)


def square_numerator(field, value, *, deadline=None):
    """Recover the derivative-cleared numerator of a reduced field element."""
    check_deadline(deadline)
    if len(value) != len(field)-1:
        raise ValueError("require a full reduced power-basis coefficient vector")
    if not any(value):
        return value
    exponent = valuation(value)
    if exponent % 2:
        return None
    radius = 1+max(map(abs, field))
    bound = (len(value)*(1+isqrt(evaluate(tuple(map(abs, value)), radius)))
             *(1+radius)**(len(value)-1))
    precision = max(2, (2*bound).bit_length())
    modulus = 1 << (precision+1+exponent)
    target = [c % modulus for c in value]
    odd_inverse = pow(field[0]//2, -1, modulus)
    # Division by the uniformizer via its defining equation consumes one precision bit.
    for _ in range(exponent):
        check_deadline(deadline)
        modulus //= 2
        top = -(target[0]//2)*odd_inverse % modulus
        target = [(target[j]+top*field[j]) % modulus for j in range(1, len(field)-1)]+[top]
    root = local_root_mod_eight(field, target)
    if root is None:
        return None

    # Residual precision j becomes at least 2j-2 after one Newton step.
    bits = 3
    while bits < precision+1:
        check_deadline(deadline)
        bits = min(2*bits-2, precision+1)
        modulus = 1 << bits
        square = multiply(field, root, root, modulus)
        half_error = [((a-b) % modulus)//2 for a, b in zip(target, square)]
        correction = multiply(field, half_error, inverse_unit(field, root, bits-1), modulus//2)
        root = [(a+b) % (modulus//2) for a, b in zip(root, correction)]
    if multiply(field, root, root, 1 << (precision+1)) != target:
        raise ArithmeticError("invalid lifted dyadic square root")

    modulus = 1 << precision
    for _ in range(exponent//2):
        check_deadline(deadline)
        root = [c % modulus for c in multiply_mark(field, root, 0, -1)]
    derivative = [j*c for j, c in enumerate(field) if j]
    numerator = multiply(field, root, derivative, modulus)
    numerator = [(c+modulus//2) % modulus-modulus//2 for c in numerator]
    left = multiply(field, numerator, numerator)
    right = multiply(field, value, multiply(field, derivative, derivative))
    check_deadline(deadline)
    return numerator if left == right else None


def joint_roots(n, m, fields, points, sign, *, deadline=None):
    """Return exact joint root residues, or None when a field product is nonsquare."""
    check_deadline(deadline)
    fields, points = tuple(tuple(p) for p in fields), tuple(points)
    if n <= 1 or n % 2 == 0 or len(fields) != 2 or sign not in (-1, 1):
        raise ValueError("require odd N > 1, two fields and a common sign")
    divisors = []
    common = sign*prod((a-b*m) % n for a, b in points) % n
    if gcd(common, n) != 1:
        raise ValueError("require a modular unit mark product")
    for field in fields:
        if (len(field) < 3 or field[-1] != 1 or field[0] % 4 != 2
                or any(c % 2 for c in field[:-1]) or evaluate(field, m) % n):
            raise ValueError("require monic Eisenstein polynomials with the given root modulo N")
        divisor = evaluate([j*c for j, c in enumerate(field) if j], m)
        if gcd(divisor, n) != 1:
            raise ValueError("require derivatives invertible modulo N")
        divisors.append(divisor)
    residues = []
    for field, divisor in zip(fields, divisors, strict=True):
        value = [sign]+[0]*(len(field)-2)
        for a, b in points:
            check_deadline(deadline)
            value = multiply_mark(field, value, a, b)
        numerator = square_numerator(field, value, deadline=deadline)
        if numerator is None:
            return None
        residue = evaluate(numerator, m)*pow(divisor, -1, n) % n
        if residue*residue % n != common:
            raise ArithmeticError("exact root failed modular verification")
        residues.append(residue)
    return tuple(residues)


def main():
    from ast import literal_eval
    from json import loads
    from pathlib import Path
    from runpy import run_path

    here = Path(__file__).resolve().parent
    grid = run_path(str(here / "cogentic-monic-large-primes.py"))
    marks_895 = run_path(str(here / "cogentic-all-ideal-reference.py"))["NEW_SQUARE"]
    fixtures = [
        (895, grid["CHECK_PAIR"](895, 2), marks_895, -1, 5),
        (247, grid["CHECK_PAIR"](247, 3), [(-31, 3), (-1, 1)], -1, 13),
        (247, grid["CHECK_PAIR"](247, 3), [(-31, 3), (-1, 1)], 1, None),
        (247, grid["CHECK_PAIR"](247, 3), [], 1, None),
    ]
    for n, (m, *fields), points, sign, factor in fixtures:
        coefficients = [list(field) for field in fields]
        expression = f"kernel_roots({n},{m},apply(Polrev,{coefficients}),{[list(p) for p in points]},{sign})"
        line, = grid["gp"](f'read("cogentic-monic-kernel-driver.gp");\n'
                           f'iferr(print({expression}),err,print(err);quit(1));\n')
        expected = literal_eval(line)
        actual = joint_roots(n, m, fields, points, sign)
        assert bool(actual) == bool(expected)
        if actual is not None:
            assert all((a-b) % n == 0 or (a+b) % n == 0 for a, b in zip(actual, expected, strict=True))
            if factor is not None:
                divisor = gcd(actual[0]-actual[1], n)
                assert min(divisor, n//divisor) == factor

    # The local square is not a global square in the cubic field.
    pell_cubic = (18, 0, -36, 1)
    assert local_root_mod_eight(pell_cubic, [-287, 8, 0]) is not None
    assert square_numerator(pell_cubic, [-144, 0, 1]) is None
    assert square_numerator((54, 0, -28, 1), [-12, 2, 8]) in ([252, 78, -82], [-252, -78, 82])
    try:
        m, *fields = fixtures[-1][1]
        joint_roots(247, m, fields, [], 1, deadline=0)
    except TimeoutExpired:
        pass
    else:
        raise AssertionError("expired deadline did not interrupt square recovery")
    print(f"Dyadic square classification and root residues match PARI on {len(fixtures)} cases")

    certificates = loads((here / "cogentic-monic-degree-certificates.json").read_text())
    for case in certificates:
        n, m, fields, points, sign = (case[key] for key in ("n", "m", "fields", "points", "sign"))
        start = monotonic()
        actual = joint_roots(n, m, fields, points, sign, deadline=start+10)
        assert actual is not None
        assert all((a-b) % n == 0 or (a+b) % n == 0
                   for a, b in zip(actual, case["residues"], strict=True))
        divisor = gcd(actual[0]-actual[1], n)
        assert min(divisor, n//divisor) == min(case["divisor"], case["cofactor"])
        print(f"{len(points)}-mark certificate recovered in {monotonic()-start:.3f} s")


if __name__ == "__main__":
    main()
