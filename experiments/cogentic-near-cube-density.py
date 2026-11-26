"""Check the frozen-digit identities and quartic resolvent reconstruction."""

from itertools import product
from math import isqrt
from pathlib import Path
import runpy

PLANTS = runpy.run_path(str(Path(__file__).with_name("cogentic-planted-norm-two.py")))
evaluate = PLANTS["evaluate"]
multiply = PLANTS["multiply"]
integer_root = PLANTS["BASE"]["integer_root"]


def defining_polynomial(m, digits, perturbation):
    poly = [*digits, 1]
    if len(perturbation) == 3:
        poly[3] -= m
        poly.append(1)
    for i, coefficient in enumerate(multiply([-m, 1], perturbation)):
        poly[i] += coefficient
    return poly


def homogeneous(poly, a, b):
    degree = len(poly)-1
    return sum(coefficient*a**i*b**(degree-i) for i, coefficient in enumerate(poly))


def derivative(poly, m):
    return evaluate([i*c for i, c in enumerate(poly) if i], m)


def resolvent_roots(poly):
    constant, linear, quadratic, cubic, _ = poly
    linear_term = cubic*linear-4*constant
    constant_term = 4*quadratic*constant-cubic**2*constant-linear**2
    resolvent = [constant_term, linear_term, -quadratic, 1]
    bound = max(1, 3*abs(quadratic), isqrt(3*abs(linear_term))+1,
                integer_root(3*abs(constant_term), 3)+1)
    return {z for z in range(-bound, bound+1) if evaluate(resolvent, z) == 0}, bound


if __name__ == "__main__":
    marks = [(0, 1), (1, 1), (-1, 2), (3, 2), (-5, 4)]
    constant_digits = (0, 1, 4, 9, 17)
    checked = root_cases = 0
    for m, c1, c2, p0, p1, p2 in product((101, 137, 209), (0, 20), (-3, 0, 3),
                                        (0, 1), (0, 2), (0, 1)):
        perturbation = (p0, p1, p2)
        base = defining_polynomial(m, (0, c1, c2), perturbation)
        _, linear, quadratic, cubic, _ = base
        offset = 4*quadratic-cubic**2
        dividend = offset**3-4*quadratic*offset**2+16*cubic*linear*offset-64*linear**2
        assert dividend != 0
        observed = set()
        largest_bound = 0
        for c0 in constant_digits:
            n = m**3+c2*m*m+c1*m+c0
            for p in (perturbation[:2], perturbation):
                poly = defining_polynomial(m, (c0, c1, c2), p)
                assert evaluate(poly, m) == n
                changed_constant = defining_polynomial(m, (c0+1, c1, c2), p)
                changed_linear = defining_polynomial(m, (c0, c1+1, c2), p)
                core_derivative = 3*m*m+2*c2*m+c1+evaluate(p, m)
                expected = core_derivative + (m**3 if len(p) == 3 else 0)
                assert derivative(poly, m) == expected == derivative(changed_constant, m)
                degree = len(poly)-1
                for a, b in marks:
                    value = homogeneous(poly, a, b)
                    assert homogeneous(changed_constant, a, b)-value == b**degree
                    assert homogeneous(changed_linear, a, b)-value == a*b**(degree-1)
                checked += 1
            quartic = defining_polynomial(m, (c0, c1, c2), perturbation)
            roots, bound = resolvent_roots(quartic)
            observed.update((c0, z) for z in roots)
            largest_bound = max(largest_bound, bound)
        recovered = set()
        for z in range(-largest_bound, largest_bound+1):
            divisor = 4*z-offset
            if divisor and dividend % divisor == 0:
                numerator = z**3-quadratic*z*z+cubic*linear*z-linear**2
                a0, remainder = divmod(numerator, divisor)
                c0 = a0-base[0]
                if not remainder and c0 in constant_digits:
                    recovered.add((c0, z))
        assert recovered == observed
        root_cases += len(observed)
    assert root_cases > 0
    print(f"{checked} exact cubic/quartic carry checks, {root_cases} reconstructed resolvent roots")
