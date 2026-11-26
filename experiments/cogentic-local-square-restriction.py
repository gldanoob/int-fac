"""Restrict an ideal-square kernel at real places and named rational primes."""

from pathlib import Path
from runpy import run_path

from sage.all import GF, QQ, ZZ, PolynomialRing, identity_matrix, matrix, vector

HERE = Path(__file__).resolve().parent
SQUARES = run_path(str(HERE / "cogentic-order-square-kernel.py"))
PowerBasis, ideal_kernel, support, adaptive = (
    SQUARES[name] for name in ("PowerBasis", "ideal_kernel", "support", "adaptive")
)
PARITY = SQUARES["PARITY"]
cover_polynomial, span = (PARITY[name] for name in ("cover_polynomial", "span"))
lattice = PARITY["CUBIC"]["lattice"]


def prime_count(polynomial, p):
    """Count primes above p using only p-maximal order arithmetic."""
    algebra = PowerBasis(polynomial)
    order = algebra.identity
    degree = int(polynomial.degree())
    field = GF(p)
    identity = identity_matrix(field, degree)
    p_lattice = (p * algebra.identity).rows()
    while True:
        inverse = order.inverse()
        # Each row of the identity already represents its basis element a.
        frobenius = matrix(field, [
            row * (order * algebra.multiplication(a) * inverse).change_ring(field)**(p - 1)
            for row, a in zip(identity, order, strict=True)
        ])
        nilpotents = (frobenius**degree.bit_length()).left_kernel().basis()
        radical = lattice(p_lattice + [vector(ZZ, row) for row in nilpotents]) * order
        overorder = algebra.colon(radical, radical)
        if overorder == order:
            # Frobenius-fixed elements map bijectively to those of the reduced algebra.
            return degree - (frobenius - identity).rank()
        order = overorder


def local_square_kernel(polynomial, elements, primes=(), *, real=True):
    """Return original-coordinate kernel masks and (place, rank, queries) statistics."""
    polynomial = polynomial.change_ring(ZZ).change_ring(QQ)
    primes = tuple(ZZ(p) for p in primes)
    if any(not p.is_prime() for p in primes):
        raise ValueError("expected named rational primes")
    elements = [polynomial.parent()(z) % polynomial for z in elements]
    masks = ideal_kernel(polynomial, elements)
    algebra = PowerBasis(polynomial)
    degree = polynomial.degree()
    operators = [algebra.multiplication(vector(QQ, z.padded_list(degree))) for z in elements]
    stats = []
    for place in ((None,) if real else ()) + primes:
        if not masks:
            break
        branches = polynomial.number_of_real_roots() if place is None else prime_count(polynomial, place)

        def oracle(mask):
            value = algebra.identity[0]
            for slot in support(mask):
                value = value * operators[slot]
            integral = value.denominator()**2 * value
            cover = cover_polynomial(polynomial, algebra, integral)
            if place is None:
                return cover.number_of_real_roots() == 2 * branches
            if not cover.is_irreducible():
                return True
            return prime_count(cover, place) == 2 * branches

        status, queries, rank, relations = adaptive(masks, oracle, query_cap=None)
        limit = degree + branches if place == 2 else branches
        assert status == "complete" and rank <= limit and queries <= len(masks) * (1 << rank)
        masks = [mask for mask, _ in relations]
        stats.append((place, rank, queries))
    return masks, stats


def replay():
    from sage.all import AA, NumberField, pari

    x = PolynomialRing(QQ, "x").gen()
    fixtures = [
        (x-1, [-1, 17, QQ(-1)/4, 9, 17**2, 27, 3], (2, 3)),
        (x*x-10, [-1, 3+x, 3-x, x, 2, 5, (x+2)**2/9, (3+x)/49], (2, 3, 5)),
        (x**4-2, [-1, x, x*x, 1+x*x, (1+x*x)/49, ((1+x)/5)**2, 31, 31*x*x], (2, 3, 7)),
        (x*x+51, [-1, 17, QQ(17)/49, 3, 51, (x+2)**2/9], (2, 13, 3)),
    ]
    checked = 0
    for polynomial, values, primes in fixtures:
        field = NumberField(polynomial, "alpha")
        embeddings = field.embeddings(AA)
        base = pari(polynomial).nfinit()
        places = {p: base.idealprimedec(p) for p in primes}
        for p, branches in places.items():
            assert prime_count(polynomial, p) == len(branches)
        even = span(ideal_kernel(polynomial, values))
        products = {}
        for mask in even:
            value = x.parent().one()
            for slot in support(mask):
                value = value * values[slot] % polynomial
            products[mask] = value
        for length in range(len(primes) + 1):
            used = primes[:length]
            basis, _ = local_square_kernel(polynomial, values, used)
            expected = {
                mask for mask, value in products.items()
                if all(embedding(value(field.gen())) > 0 for embedding in embeddings)
                and all(base.nfislocalpower(branch, pari(value), 2) for p in used for branch in places[p])
            }
            assert span(basis) == expected
            checked += len(even)

    polynomial = x*x+51
    field = NumberField(polynomial, "alpha")
    cover = cover_polynomial(polynomial, PowerBasis(polynomial), vector(QQ, [17, 0]))
    extension = NumberField(cover, "beta")
    assert not field(17).is_square() and extension.discriminant() == field.discriminant()**2
    assert local_square_kernel(polynomial, [17], (2, 13))[0] == [1]
    assert local_square_kernel(polynomial, [17], (2, 13, 3))[0] == []
    p = ZZ(2**61 - 1)
    assert prime_count(x*x-10, p) == 1 + ZZ(10).kronecker(p)
    print(f"{checked} prefix-mask decisions matched real embeddings and independent PARI local powers")
    print("Unramified nonsquare survived at 2 and 13 and failed at 3")


if __name__ == "__main__":
    replay()
