"""Exact Sage checks for the three units in the reciprocal quartic tower."""
from itertools import product
from math import gcd, isqrt

from sage.all import EllipticCurve, NumberField, PolynomialRing, QQ, prod

x = PolynomialRing(QQ, "x").gen()


def quartic(n):
    return x**4 + 2*n*x**3 - (5*n + 4)*x**2 + 2*n*x + 1


for n in range(5, 75, 3):
    field = NumberField(quartic(n), "h")
    h = field.gen()
    units = [-h, 2-h, 1-2*h]
    masks = [mask for mask in product(range(2), repeat=3)
             if field(prod(u**bit for u, bit in zip(units, mask))).is_square()]
    a = isqrt(n + 2)
    if a*a == n+2:
        assert (1, 1, 1) in masks
        assert ((h-1)**2/a)**2 == prod(units)
    else:
        assert masks == [(0, 0, 0)]

N = 323
roots = [r for r in range(N) if (r*r+15) % N == 0]
for r in roots:
    a = 4*pow(r, -1, N) % N
    while a % 3 != 1 or a*a-2 < N:
        a += N
    n = a*a-2
    f = quartic(n)
    assert n % 3 == 2 and f(3) % N == 0
    assert gcd(int(f.derivative()(3)), N) == 1
    assert 4*pow(a, -1, N) % N == r
assert roots == [40, 74, 249, 283]
assert gcd(roots[0]-roots[1], N) == 17

m = x
delta = m*(2*m-1)*(m-2)
assert quartic(0) - 2*delta == (m-1)**4
assert quartic(0) - 3*delta == (m**2-3*m+1)**2
curve = EllipticCurve([0, 5, 0, 4, 0])
assert curve.rank(proof=True) == 0
assert {(int(P[0]), int(P[1])) for P in curve.torsion_points() if P[2]} == {
    (0, 0), (-1, 0), (-4, 0), (-2, 2), (-2, -2), (2, 6), (2, -6)}
print("192 exact square masks, four roots modulo 323, rank zero and eight rational points")
