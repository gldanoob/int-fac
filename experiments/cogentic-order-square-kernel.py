"""Recover signed field-square kernels and exact roots from explicit orders."""

from pathlib import Path
from runpy import run_path

from sage.all import PolynomialRing, QQ, ZZ, vector

HERE = Path(__file__).resolve().parent
PARITY = run_path(str(HERE / "cogentic-order-ideal-parity.py"))
PowerBasis, ideal_kernel, primitive_cover = (
    PARITY[name] for name in ("PowerBasis", "ideal_kernel", "primitive_cover")
)
support = PARITY["CUBIC"]["support"]
adaptive = run_path(str(HERE / "cogentic-monic-kernel-driver.py"))["adaptive"]


def square_root(polynomial, algebra, coordinates):
    """Return one root in rational coordinates, or None for a nonsquare."""
    if coordinates.is_zero():
        return coordinates
    degree = polynomial.degree()
    denominator = coordinates.denominator()
    integral = denominator**2 * coordinates
    primitive, operator = primitive_cover(polynomial, algebra, integral)
    factors = list(primitive.factor())
    if len(factors) == 1:
        return None
    (first, e1), (second, e2) = factors
    assert e1 == e2 == 1 and first.degree() == second.degree() == degree
    gcd, inverse, _ = first.xgcd(second)
    assert gcd == 1
    orientation = (2 * inverse * first - 1) % primitive

    one = vector(QQ, [1] + [0] * (2 * degree - 1))
    value = 0 * one
    for coefficient in reversed(orientation.list()):
        value = value * operator + coefficient * one
    # Multiplication by the adjoined root has diagonal value in the split algebra.
    assert value[:degree].is_zero()
    root = value[degree:] * algebra.multiplication(integral) / denominator
    assert root * algebra.multiplication(root) == coordinates
    return root


def square_kernel(polynomial, elements, *, query_cap=None):
    """Return completion, basis masks and roots, residual rank, tests and first dimension."""
    polynomial = polynomial.change_ring(ZZ).change_ring(QQ)
    if query_cap is not None and query_cap < 0:
        raise ValueError("expected a nonnegative query cap")
    elements = [polynomial.parent()(z) % polynomial for z in elements]
    first = ideal_kernel(polynomial, elements, norm_sign=True)
    algebra = PowerBasis(polynomial)
    degree = polynomial.degree()
    operators = [algebra.multiplication(vector(QQ, z.padded_list(degree))) for z in elements]

    def oracle(mask):
        value = algebra.identity[0]
        for slot in support(mask):
            value = value * operators[slot]
        root = square_root(polynomial, algebra, value)
        return polynomial.parent()(root.list()) if root is not None else None

    status, tests, rank, roots = adaptive(first, oracle, query_cap)
    return status == "complete", roots, rank, tests, len(first)


def replay():
    from sage.all import NumberField

    x = PolynomialRing(QQ, "x").gen()
    fixtures = [
        (x - 3, [-1, 2, 3, 6, QQ(1)/49, -9, 7**2]),
        (x*x + 1, [-1, 2, x, 1 + x, x/2, (1 + x)**2, (x/5)**2]),
        (x**4 - 2, [-1, x*x - 1, 1 - x*x, x, x*x, (1 + x)**2, ((1 + x)/17)**2, 2]),
        (x**6 - 2, [-1, x, x**3 + 1, 31, 31*x, 31*x**3, (1 + x)**2, ((1 + x)/31)**2]),
    ]
    parity_columns, atom_defect = (PARITY[name] for name in ("parity_columns", "atom_defect"))
    span = PARITY["span"]
    count = 0
    for polynomial, values in fixtures:
        complete, roots, rank, tests, first = square_kernel(polynomial, values)
        assert complete and len(roots) + rank == first and tests <= first * (1 << rank)
        field = NumberField(polynomial, "alpha")
        columns, atoms = parity_columns(polynomial, values, norm_sign=True)
        r1, r2 = field.signature()
        assert rank <= r1 + r2 - (polynomial.degree() % 2) + atom_defect(columns, atoms)
        words = span(mask for mask, _ in roots)
        elements = [x.parent()(value)(field.gen()) for value in values]
        for word in range(1 << len(values)):
            product = field.one()
            for i in support(word):
                product *= elements[i]
            assert product.is_square() == (word in words)
        for word, root in roots:
            product = x.parent().one()
            for i in support(word):
                product = product * values[i] % polynomial
            assert root**2 % polynomial == product
        count += 1 << len(values)

    polynomial = x**4 - 2
    assert square_kernel(polynomial, [-1, x*x - 1, 1 - x*x])[2] == 2
    complete, [(mask, root)], rank, tests, first = square_kernel(polynomial, [x*x, -1], query_cap=1)
    assert not complete and (mask, rank, tests, first) == (1, 0, 1, 2)
    assert root**2 % polynomial == x*x

    q = ZZ(2**61 - 1) * (2**89 - 1)
    scaled = x**4 - 2*q**4
    values = [q, x, q*q, x*x, (q + x)**2, x/q, (x/q + 1)**2]
    reduced = [x.parent()(value)(q*x) for value in values]
    result = square_kernel(scaled, values)
    reference = square_kernel(polynomial, reduced)
    assert result[0] and reference[0]
    assert span(word for word, _ in result[1]) == span(word for word, _ in reference[1])
    for word, root in result[1]:
        product = x.parent().one()
        for i in support(word):
            product = product * values[i] % scaled
        assert root**2 % scaled == product

    print(f"{count} signed masks matched independent square decisions in degrees 1, 2, 4 and 6")
    print("partial certificates and full kernel verified on explicit orders, including a 150-bit index base")


if __name__ == "__main__":
    replay()
