"""Replay short-representative square kernels in a nonnormal quadratic tower."""

from collections import Counter
from fractions import Fraction
from math import isqrt, prod
from pathlib import Path
from runpy import run_path

from sage.all import PolynomialRing, QQ


MASKS = run_path(str(Path(__file__).with_name("cogentic-multiquadratic-square-kernel.py")))
combine, rational_kernel, support = (MASKS[name] for name in ("combine", "rational_kernel", "support"))


class Tower:
    def __init__(self, lower=None, radicand=None, name=None):
        self.lower = lower
        if lower is None:
            self.field = QQ
        else:
            self.radicand = lower.field(radicand)
            ring = PolynomialRing(lower.field, "x")
            self.field = lower.field.extension(ring([-self.radicand, 0, 1]), name)

    def parts(self, value):
        a, b = self.field(value).list()
        return a, b

    def norm(self, value):
        a, b = self.parts(value)
        return a*a - self.radicand*b*b

    def square_root(self, value):
        if self.lower is None:
            if value < 0:
                return None
            a, b = isqrt(value.numerator()), isqrt(value.denominator())
            return QQ(a)/b if a*a == value.numerator() and b*b == value.denominator() else None

        a, b = self.parts(value)
        if not b:
            root = self.lower.square_root(a)
            if root is not None:
                return self.field(root)
            root = self.lower.square_root(a/self.radicand)
            return None if root is None else self.field(root)*self.field.gen()

        t = self.lower.square_root(self.norm(value))
        if t is not None:
            for sign in (1, -1):
                root = self.lower.square_root((a + sign*t)/2)
                if root:
                    return self.field(root) + self.field(b/(2*root))*self.field.gen()
        return None

    def descend(self, value):
        a, _ = self.parts(value)
        t = self.lower.square_root(self.norm(value))
        if t is None:
            raise ArithmeticError("the norm-kernel representative has nonsquare norm")
        return 2*(a+t) or 2*(a-t)

    def product(self, columns, mask):
        return prod((columns[i] for i in support(mask)), start=self.field.one())

    def square_kernel(self, columns, representative, stats):
        """Return masks of square products using a squareclass-preserving oracle."""
        if self.lower is None:
            rationals = [Fraction(int(v.numerator()), int(v.denominator())) for v in columns]
            return rational_kernel(rationals)

        def norm_rep(mask):
            stats["norm representatives"] += 1
            return self.norm(representative(mask))

        norms = [self.norm(v) for v in columns]
        basis = self.lower.square_kernel(norms, norm_rep, stats)
        if not basis:
            return []
        scalar_columns = [self.descend(representative(mask)) for mask in basis] + [self.radicand]
        basis_bits = (1 << len(basis)) - 1

        def scalar_rep(mask):
            original = combine(mask & basis_bits, basis)
            short = self.descend(representative(original))
            # Equality upstairs leaves only the radicand ambiguity downstairs.
            quotient = self.lower.product(scalar_columns, mask)/short
            if self.lower.square_root(quotient) is not None:
                stats["unchanged representatives"] += 1
                return short
            if self.lower.square_root(quotient/self.radicand) is None:
                raise ArithmeticError("the scalar correction changed the squareclass")
            stats["radicand corrections"] += 1
            if original and mask <= basis_bits:
                stats["corrections without the appended column"] += 1
            return short*self.radicand

        masks = self.lower.square_kernel(scalar_columns, scalar_rep, stats)
        return [combine(mask & basis_bits, basis) for mask in masks]


def replay():
    base = Tower()
    quadratic = Tower(base, 2, "a")
    quartic = Tower(quadratic, quadratic.field.gen(), "b")
    octic = Tower(quartic, quartic.field.gen(), "c")
    c = octic.field.gen()
    absolute = octic.field.absolute_field("z")
    assert absolute.degree() == 8 and absolute.signature() == (2, 3)
    to_absolute = absolute.structure()[1]

    def check(columns):
        stats = Counter()
        masks = octic.square_kernel(columns, lambda mask: octic.product(columns, mask), stats)
        span = {0}
        for mask in masks:
            assert mask not in span
            span |= {word ^ mask for word in span}
            value = octic.product(columns, mask)
            root = octic.square_root(value)
            assert root is not None and root**2 == value
        exact = [to_absolute(value) for value in columns]
        for mask in range(1 << len(columns)):
            value = prod((exact[i] for i in support(mask)), start=absolute.one())
            assert (mask in span) == value.is_square()
        print(f"All {1 << len(columns)} masks agree in the nonnormal octic field")
        print(f"Basis masks {masks}, short-representative checks {dict(stats)}")
        return stats

    columns = [c, c*c, c**4, c+1, 7*octic.field.one(), 7*(c+1)**2, (c-1)/3, (c*c+c+1)**2]
    stats = check(columns)
    assert stats["norm representatives"]

    b = c*c
    seed = (2*b+2)*c-b-2
    stats = check([seed**2, c**4, 7*(c+1)**2])
    assert stats["corrections without the appended column"]


if __name__ == "__main__":
    replay()
