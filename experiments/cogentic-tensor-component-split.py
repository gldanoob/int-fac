"""Split an odd modulus from supplied polynomial roots in different tensor components."""

from math import gcd
from operator import index
from typing import NamedTuple

from sympy import Dummy, Poly, ZZ, resultant


class Result(NamedTuple):
    reason: str
    factor: int | None = None
    t: int | None = None
    component: Poly | None = None


def evaluate_mod(polynomial, value, modulus):
    result = 0
    for coefficient in polynomial.all_coeffs():
        result = (result * value + int(coefficient)) % modulus
    return result


def integralize(polynomial, x):
    leading = polynomial.LC()
    coefficients = [1] + [
        coefficient * leading**j for j, coefficient in enumerate(polynomial.all_coeffs()[1:])
    ]
    return Poly.from_list(coefficients, x, domain=ZZ)


def split_components(modulus, p, q, u, v, *, max_t=16):
    """Use supplied roots u and v of integral SymPy polynomials p and q.

    Try slopes 1 through max_t. A good discriminant certifies either a
    component split or that all local roots choose the same Q-component.
    A proper leading-coefficient or discriminant gcd is reported separately.
    Exhausting the slope budget gives an inconclusive result.
    """
    modulus, u, v, max_t = map(index, (modulus, u, v, max_t))
    if modulus <= 1 or modulus % 2 == 0 or max_t < 1:
        raise ValueError("expected an odd modulus greater than one and a positive slope budget")
    p, q = p.set_domain(ZZ), q.set_domain(ZZ)
    if not p.is_univariate or not q.is_univariate or p.degree() < 1 or q.degree() < 1:
        raise ValueError("expected two nonconstant univariate polynomials")
    if evaluate_mod(p, u, modulus) or evaluate_mod(q, v, modulus):
        raise ValueError("the supplied values must be roots modulo the modulus")

    leading_gcds = [gcd(polynomial.LC(), modulus) for polynomial in (p, q)]
    for divisor in leading_gcds:
        if 1 < divisor < modulus:
            return Result("leading coefficient", divisor)
    if modulus in leading_gcds:
        return Result("inconclusive leading coefficient")

    x, z = Dummy("x"), Dummy("z")
    integral_p, integral_q = integralize(p, x), integralize(q, x)
    a, b = int(p.LC()) * u % modulus, int(q.LC()) * v % modulus
    degree = p.degree() * q.degree()
    for t in range(1, max_t + 1):
        shifted = integral_p.as_expr().subs(x, z - t * x)
        phi = Poly(resultant(integral_q.as_expr(), shifted, x), z, domain=ZZ)
        if phi.degree() != degree or phi.LC() != 1:
            continue
        discriminant = phi.discriminant()
        if discriminant == 0:
            continue
        divisor = gcd(discriminant, modulus)
        if 1 < divisor < modulus:
            return Result("discriminant", divisor, t)
        if divisor == modulus:
            continue

        value = (a + t * b) % modulus
        assert evaluate_mod(phi, value, modulus) == 0
        for component, _ in phi.factor_list()[1]:
            divisor = gcd(evaluate_mod(component, value, modulus), modulus)
            if 1 < divisor < modulus:
                return Result("component", divisor, t, component)
        return Result("same component", t=t)
    return Result("inconclusive discriminant")


def replay():
    x = Dummy("x")
    f = Poly(x**4 - 10*x**2 + 1, x)
    modulus, u, v = 1161359, 1072857, 119483
    # The supplied pairing is v = 1/u at 1009 and v = -1/u at 1151.
    assert gcd(u - v, modulus) == gcd(u + v, modulus) == 1
    monic = split_components(modulus, f, f, u, v)
    assert monic.reason == "component" and monic.t == 2 and monic.factor in (1009, 1151)

    p = Poly(f.as_expr().subs(x, 2*x), x)
    q = Poly(f.as_expr().subs(x, 3*x), x)
    nonmonic = split_components(modulus, p, q, 1117108, 814067)
    assert nonmonic.reason == "component" and nonmonic.t == 1 and nonmonic.factor in (1009, 1151)
    assert split_components(modulus, f, f, u, 279914).reason == "same component"

    quadratic = Poly(x**2 - 1, x)
    assert split_components(15, quadratic, quadratic, 1, 1, max_t=2) == Result("discriminant", 3, 2)
    assert split_components(9, quadratic, quadratic, 1, 1, max_t=2).reason == "inconclusive discriminant"
    assert split_components(15, Poly(3*x - 3, x), quadratic, 1, 1) == Result("leading coefficient", 3)
    print(f"Verified component splits {monic.factor} and {nonmonic.factor}, with good discriminants.")


if __name__ == "__main__":
    replay()
