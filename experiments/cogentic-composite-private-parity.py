"""Factor-free private ideal parity via the Buchmann–Lenstra tame-order criterion."""

from itertools import combinations

from sage.all import QQ, ZZ, PolynomialRing, factorial, identity_matrix, matrix, vector


def lattice(rows):
    basis = matrix(QQ, rows)
    denominator = basis.denominator()
    return (denominator * basis).change_ring(ZZ).hermite_form(include_zero_rows=False) / denominator


def dual(basis):
    return basis.inverse().transpose()


def invariants(larger, smaller):
    inclusion = (smaller * larger.inverse()).change_ring(ZZ)
    return inclusion.smith_form(transformation=False).diagonal()


def proper_invariant(values, q):
    return next((value for value in values if value not in (1, q)), None)


def coprime_basis(numbers):
    bases = set(numbers) - {ZZ.one()}
    while True:
        overlap = next(
            ((x, y, g) for x, y in combinations(sorted(bases), 2) if (g := x.gcd(y)) > 1),
            None,
        )
        if overlap is None:
            return sorted(bases)
        x, y, g = overlap
        bases.difference_update((x, y))
        bases.update((x // g, y // g, g))
        bases.discard(1)


class PowerBasis:
    def __init__(self, polynomial):
        d = polynomial.degree()
        t = polynomial.parent().gen()
        self.identity = identity_matrix(QQ, d)
        powers = [vector(QQ, (t**i % polynomial).padded_list(d)) for i in range(2 * d - 1)]
        self.multiplications = [matrix(QQ, powers[i:i + d]) for i in range(d)]
        traces = vector(QQ, [operator.trace() for operator in self.multiplications])
        self.trace_form = matrix(QQ, [
            [powers[i + j].dot_product(traces) for j in range(d)] for i in range(d)
        ])

    def multiplication(self, x):
        return sum(coefficient * operator for coefficient, operator in zip(x, self.multiplications))

    def trace_ideal(self, order, q):
        traces = order * self.trace_form * order.transpose()
        return lattice(dual(lattice(self.identity.stack(traces / q))) * order)

    def colon(self, target, source):
        target_inverse = target.inverse()
        constraints = [column for x in source
                       for column in (self.multiplication(x) * target_inverse).columns()]
        return lattice(dual(lattice(constraints)))

    def profile(self, order, q):
        # BL 3.7 recognizes tameness before Algorithm 6.3's extra ramification checks.
        while True:
            ideal = self.trace_ideal(order, q)
            split = proper_invariant(invariants(order, ideal), q)
            if split is not None:
                return order, split, None
            overorder = self.colon(ideal, ideal)
            if overorder == order:
                break
            order = overorder
        colon = self.colon(order, ideal)
        split = proper_invariant(invariants(colon, order), q)
        if split is not None:
            return order, split, None

        q_order = q * order
        power = order
        multiplications = [self.multiplication(x) for x in ideal]
        ranks = [0]
        degree = order.nrows()
        for _ in range(degree):
            power = lattice(q_order.rows() + [row for operator in multiplications for row in power * operator])
            values = invariants(order, power)
            split = proper_invariant(values, q)
            if split is not None:
                return order, split, None
            ranks.append(values.count(q))
        ranks.append(degree)
        layers = [after - before for before, after in zip(ranks, ranks[1:])]
        profile = [(h, left - right) for h, (left, right) in enumerate(zip(layers, layers[1:]), 1)
                   if left > right]
        assert sum(h * f for h, f in profile) == degree
        return order, None, profile


def tame_profiles(polynomial, modulus):
    algebra = PowerBasis(polynomial)
    order = algebra.identity
    pending = [modulus]
    profiles = {}
    while pending:
        q = pending.pop()
        order, split, profile = algebra.profile(order, q)
        if split is None:
            profiles[q] = profile
        else:
            pending.extend(coprime_basis([split, q // split]))
    return order, profiles


def weight_sum(profiles, atom, depth):
    q = next(q for q in profiles if q % atom == 0)
    scale = q.valuation(atom)
    assert scale > 0 and (q // atom**scale).gcd(atom) == 1
    return sum(
        QQ(h * f) / 2**max(0, ZZ(h).valuation(2) - scale.valuation(2) - depth)
        for h, f in profiles[q]
    )


def square_depth(n):
    depth = 0
    while True:
        root, remainder = n.sqrtrem()
        if remainder:
            return depth
        depth += 1
        n = root


def private_ideal_even(polynomial, a, b, modulus):
    """Test ideals over a supplied norm residual in an integral monic field."""
    polynomial = polynomial.change_ring(ZZ).change_ring(QQ)
    a, b = ZZ(a), ZZ(b)
    d = polynomial.degree()
    modulus = ZZ(modulus)
    if not polynomial.is_monic() or d < 1 or b <= 0 or not polynomial.is_irreducible():
        raise ValueError("expected a monic field polynomial and positive denominator")
    if modulus < 1 or modulus.gcd(factorial(2 * d)) != 1:
        raise ValueError("expected a positive residual supported above twice the degree")
    t = polynomial.parent().gen()
    mark = (-b)**d * polynomial((a - t) / b)
    if not mark[0] or mark[0] % modulus:
        raise ValueError("residual must divide the nonzero absolute mark norm")
    if modulus == 1:
        return True
    extension = mark(t**2)
    if not extension.is_irreducible():
        return True
    _, downstairs = tame_profiles(mark, modulus)
    _, upstairs = tame_profiles(extension, modulus)
    for atom in coprime_basis([modulus, *downstairs, *upstairs]):
        depth = square_depth(atom)
        if weight_sum(upstairs, atom, depth) != 2 * weight_sum(downstairs, atom, depth):
            return False
    return True


def replay():
    t = PolynomialRing(QQ, "t").gen()
    p, q = ZZ(2**61 - 1), ZZ(2**89 - 1)
    composite = p * q**2
    for j in range(3):
        scale = composite**(2**j)
        residual = scale**2
        polynomial = t**2 + residual
        assert private_ideal_even(polynomial, 0, 1, residual) == (j > 0)
        order, profiles = tame_profiles(t**4 + residual, residual)
        assert profiles == {residual: [(4, 1)]}
        assert order.det() == 1
    residual = composite**2
    order, profiles = tame_profiles(t**4 + residual, composite)
    assert profiles == {composite: [(2, 2)]}
    assert order.det() == 1 / residual
    assert not private_ideal_even(t**2 + residual, 0, 1, composite)
    _, profiles = tame_profiles(t**4 + residual, p**2 * q)
    assert profiles == {p**2: [(4, 1)], q: [(1, 4)]}
    assert private_ideal_even(t**2 - 2, 19, 6, 17**2)
    print(f"{residual.nbits()}-bit mixed residual rejected, its two even-valuation powers accepted")
    print("composite overorder enlargement and gcd refinement verified")


if __name__ == "__main__":
    replay()
