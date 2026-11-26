"""Signed square kernels in explicit cubic orders without maximal-order input."""

from itertools import combinations
from pathlib import Path
from runpy import run_path

from sage.all import QQ, ZZ, PolynomialRing, vector

HERE = Path(__file__).resolve().parent
GRID = run_path(str(HERE / "cogentic-monic-exact-grid.py"))
COMPOSITE = GRID["COMPOSITE"]
PowerBasis, lattice, NamedPrime = (GRID[name] for name in ("PowerBasis", "lattice", "NamedPrime"))
coprime_basis, tame_profiles, square_depth, weight_sum = (
    COMPOSITE[name] for name in ("coprime_basis", "tame_profiles", "square_depth", "weight_sum")
)
eliminate, combine, support = (GRID["GRID"][name] for name in ("eliminate", "combine", "support"))


def coprime_part(value, excluded):
    while (common := value.gcd(excluded)) > 1:
        value //= common
    return value


def index(larger, smaller):
    return ZZ(abs((smaller * larger.inverse()).det()))


def distinct_proper(order, ideals):
    result = []
    for ideal in ideals:
        if ideal != order and ideal not in result:
            result.append(ideal)
    return result


def atom_step(algebra, order, columns):
    principals = [lattice(order * algebra.multiplication(z)) for z in columns]
    atoms = distinct_proper(order, principals)
    while True:
        for left, right in combinations(atoms, 2):
            common = lattice(left.stack(right))
            if common == order:
                continue
            inverse = algebra.colon(order, common)
            # Buchmann–Lenstra 2.5 tests invertibility and supplies the next overorder.
            overorder = algebra.colon(inverse, inverse)
            if overorder != order:
                return overorder, None
            others = [ideal for ideal in atoms if ideal != left and ideal != right]
            refinements = [common, algebra.colon(left, common), algebra.colon(right, common)]
            atoms = distinct_proper(order, others + refinements)
            break
        else:
            return order, (atoms, principals)


def atomize(algebra, columns):
    order = algebra.identity
    while True:
        order, result = atom_step(algebra, order, columns)
        if result is not None:
            return order, result


def named_even(local, atom, bound):
    weighted = 0
    even = True
    for ideal, residue_degree, powers in local.ideals:
        exponent = 0
        for k in range(bound // residue_degree):
            if k == len(powers):
                previous = local.order if k == 0 else powers[-1][0]
                power = lattice([row for x in ideal for row in previous * local.algebra.multiplication(x)])
                powers.append((power, power.inverse()))
            if (atom * powers[k][1]).denominator() % local.p == 0:
                break
            exponent += 1
        weighted += residue_degree * exponent
        even &= exponent % 2 == 0
    assert weighted == bound
    return even


def kummer_even(polynomial, operator, z, modulus):
    assert modulus.gcd(30) == 1 and ZZ(abs(operator.det())) % modulus == 0
    if not z[1] and not z[2]:
        scalar = ZZ(abs(z[0]))
        return (scalar // coprime_part(scalar, modulus)).is_square()
    minimum = polynomial.parent()(operator.charpoly().list())
    extension = minimum(polynomial.parent().gen() ** 2)
    if not extension.is_irreducible():
        return True
    _, base = tame_profiles(polynomial, modulus)
    _, cover = tame_profiles(extension, modulus)
    for number in coprime_basis([modulus, *base, *cover]):
        depth = square_depth(number)
        if weight_sum(cover, number, depth) != 2 * weight_sum(base, number, depth):
            return False
    return True


def atom_even(polynomial, algebra, order, atom, local_orders):
    norm = index(order, atom)
    remaining = norm
    for p in (2, 3, 5):
        exponent = norm.valuation(p)
        if not exponent:
            continue
        if p not in local_orders:
            local_orders[p] = NamedPrime(polynomial, p)
        if not named_even(local_orders[p], atom, exponent):
            return False
        remaining //= p**exponent

    x, y, z = atom
    for t in range(7):
        if remaining == 1:
            return True
        generator = x + t * y + t * t * z
        operator = algebra.multiplication(generator)
        principal_norm = ZZ(abs(operator.det()))
        assert principal_norm % norm == 0
        modulus = coprime_part(remaining, principal_norm // norm)
        if modulus > 1 and not kummer_even(polynomial, operator, generator, modulus):
            return False
        remaining //= modulus
    assert remaining == 1
    return True


def first_kernel(polynomial, algebra, columns):
    scaled = [z.denominator()**2 * z for z in columns]
    order, (atoms, principals) = atomize(algebra, scaled)
    local_orders = {}
    data = [(atom, atom.inverse(), not atom_even(polynomial, algebra, order, atom, local_orders))
            for atom in atoms]
    encoded = []
    for z, remaining in zip(columns, principals, strict=True):
        bits = int(algebra.multiplication(z).det() < 0)
        for j, (atom, inverse, bad) in enumerate(data, 1):
            exponent = 0
            while (remaining * inverse).denominator() == 1:
                remaining = algebra.colon(remaining, atom)
                exponent += 1
            if bad and exponent % 2:
                bits |= 1 << j
        assert remaining == order
        encoded.append(bits)
    return eliminate(encoded, (1 << j for j in range(len(columns))))


def square_root(polynomial, algebra, z):
    if not z[1] and not z[2]:
        return vector(QQ, [z[0].sqrt(), 0, 0]) if z[0].is_square() else None
    minimum = algebra.multiplication(z).charpoly()
    s1, s2, t = -minimum[2], minimum[1], (-minimum[0]).sqrt()
    assert t in QQ
    t = QQ(t)
    x = polynomial.parent().gen()
    resolvent = x**4 - 2*s1*x**2 - 8*t*x + s1**2 - 4*s2
    for w in resolvent.roots(multiplicities=False):
        divisor = vector(QQ, [w**2 - s1, 0, 0]) + 2*z
        numerator = vector(QQ, [2*t, 0, 0]) + 2*w*z
        root = numerator * algebra.multiplication(divisor).inverse()
        assert root * algebra.multiplication(root) == z
        return root
    return None


def square_kernel(polynomial, elements, *, query_cap=None):
    """Return completion, square masks/roots, residual rank, tests and first dimension."""
    polynomial = polynomial.change_ring(ZZ).change_ring(QQ)
    if polynomial.degree() != 3 or not polynomial.is_monic() or not polynomial.is_irreducible():
        raise ValueError("expected a monic irreducible integer cubic")
    if query_cap is not None and query_cap < 0:
        raise ValueError("expected a nonnegative query cap")
    columns = [vector(QQ, (polynomial.parent()(z) % polynomial).padded_list(3)) for z in elements]
    if any(z.is_zero() for z in columns):
        raise ValueError("expected nonzero elements")
    algebra = PowerBasis(polynomial)
    first = first_kernel(polynomial, algebra, columns)
    pivots, roots, tests = [], [], 0
    for word in first:
        for selection in range(1 << len(pivots)):
            if tests == query_cap:
                return False, roots, len(pivots), tests, len(first)
            candidate = word ^ combine(selection, pivots)
            product = algebra.identity[0]
            for i in support(candidate):
                product = product * algebra.multiplication(columns[i])
            tests += 1
            root = square_root(polynomial, algebra, product)
            if root is not None:
                roots.append((candidate, polynomial.parent()(root.list())))
                break
        else:
            pivots.append(word)
    return True, roots, len(pivots), tests, len(first)


def span(masks):
    words = {0}
    for mask in masks:
        assert mask not in words
        words.update(word ^ mask for word in tuple(words))
    return words


def replay():
    from sage.all import NumberField

    t = PolynomialRing(QQ, "t").gen()
    values = [-1, 2, t, t - 1, 1 - t, 1 + t, 1 + t + t*t, t/3, (t - 1)**2, (t + 1)**2]
    for polynomial in (t**3 - 2, t**3 - 5*t*t - 8*t - 12, t**3 - 28*t*t + 54):
        field = NumberField(polynomial, "alpha")
        elements = [polynomial.parent()(z)(field.gen()) for z in values]
        primes = set()
        for z in elements:
            norm = z.norm()
            primes.update(norm.numerator().prime_divisors())
            primes.update(norm.denominator().prime_divisors())
        places = [place for p in sorted(primes) for place in field.primes_above(p)]
        oracle_rows = [
            int(z.norm() < 0) | sum((z.valuation(place) % 2) << j for j, place in enumerate(places, 1))
            for z in elements
        ]
        columns = [vector(QQ, polynomial.parent()(z).padded_list(3)) for z in values]
        basis = first_kernel(polynomial, PowerBasis(polynomial), columns)
        assert span(basis) == {word for word in range(1 << len(values)) if not combine(word, oracle_rows)}
        complete, roots, _, _, _ = square_kernel(polynomial, values)
        assert complete
        for word, root in roots:
            product = field.one()
            for j in support(word):
                product *= elements[j]
            assert root(field.gen())**2 == product
        words = span(word for word, _ in roots)
        for word in range(1 << len(values)):
            product = field.one()
            for j in support(word):
                product *= elements[j]
            assert product.is_square() == (word in words)

    q = ZZ(2**61 - 1) * (2**89 - 1)
    scaled = t**3 - 2*q**3
    algebra = PowerBasis(scaled)
    alpha = algebra.identity[1]
    rational = q * algebra.identity[0]
    order, _ = atomize(algebra, [alpha, rational])
    assert index(order, algebra.identity) == q**3
    order, _ = atomize(algebra, [alpha])
    assert order == algebra.identity
    assert not kummer_even(scaled, algebra.multiplication(rational), rational, q)
    scalar = -11*q * rational
    assert kummer_even(scaled, algebra.multiplication(scalar), scalar, q)
    assert not kummer_even(scaled, algebra.multiplication(scalar), scalar, 11*q)
    squared = alpha * algebra.multiplication(alpha)
    assert kummer_even(scaled, algebra.multiplication(squared), squared, q)

    completed, roots, rank, _, first_dimension = square_kernel(
        scaled, [-1, 2, t, q, q*q, t*t, (t - q) / q]
    )
    assert completed and rank == 1 and first_dimension == 4
    assert span(word for word, _ in roots) == span([14, 16, 32])

    a = 7 + 11**2 * (2**128 - 1)
    eta = alpha / q - a * algebra.identity[0]
    gamma = algebra.multiplication(eta).det() * eta
    assert algebra.multiplication(gamma).det().is_square()
    assert first_kernel(scaled, algebra, [gamma]) == []
    assert square_kernel(scaled, [q*q], query_cap=0) == (False, [], 0, 0, 1)
    print("3,072 signed masks matched the maximal-order oracle in three small cubics")
    print("150-bit composite index growth, scalar branches and a square norm with odd parity passed")


if __name__ == "__main__":
    replay()
