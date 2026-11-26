"""Check the chordal product identities over Sage's exact algebraic numbers."""
from itertools import combinations, product

from sage.all import AA, QQbar, ZZ, PolynomialRing, prod

x = PolynomialRing(ZZ, "x").gen()
marks = [2*x-3, x*x+1, x*x-2, x*x+x+1, x**4+1]


def radius(a):
    return AA(1+abs(a)**2).sqrt()


def separation(a, b):
    return abs(a-b)/(radius(a)*radius(b))


data = []
for g in marks:
    roots = g.roots(QQbar, multiplicities=False)
    measure = abs(g.leading_coefficient())*prod(radius(a) for a in roots)
    distances = prod(separation(a, b)**2 for a, b in combinations(roots, 2))
    assert distances*measure**(2*g.degree()-2) == abs(g.discriminant())
    data.append((g, roots, measure))

for (g, roots, M), (h, others, H) in combinations(data, 2):
    distances = prod(separation(a, b) for a, b in product(roots, others))
    assert distances*M**h.degree()*H**g.degree() == abs(g.resultant(h))

for degree in range(1, 6):
    polynomial = (7*x-5)**degree+3
    for g, roots, measure in data:
        values = prod(abs(polynomial(a))/radius(a)**degree for a in roots)
        assert values*measure**degree == abs(g.resultant(polynomial))
print("5 exact discriminants, 10 pairwise resultants, 25 normalized value products")
