"""Exact two-field extraction on primitive homogeneous marks a-b*theta.

Run with DOT_SAGE=/tmp/rsa-sage-rank python3 -B experiments/cogentic-real-extractor-sage.py.
The small quadratic fields and smoothness bound are selected for this example.
"""

from sage.all import GF, QQ, ZZ, Mod, NumberField, PolynomialRing, gcd, matrix, prod


def fixture():
    N, m, ell = 15, 4, 7
    x = PolynomialRing(QQ, "x").gen()
    polys = [x**2 + 7*x - 29, x**2 + 7*x + 1]
    fields = [NumberField(f, f"t{i}") for i, f in enumerate(polys)]
    assert [K.discriminant() for K in fields] == [165, 5]
    assert all(f(m) % N == 0 for f in polys)
    assert [len(f.change_ring(GF(ell)).roots()) for f in polys] == [2, 0]

    return N, m, ell, fields


def collect_marks(N, m, ell, fields, candidates):
    marks, columns = [], []
    for a, b in candidates:
        if gcd(a, b) != 1 or gcd(a - b*m, N) != 1:
            continue
        elements = [a - b*K.gen() for K in fields]
        norms = [ZZ(abs(v.norm())) for v in elements]
        if gcd(*norms) != 1 or gcd(prod(norms), N*(2*a + 7*b)) != 1:
            continue
        if any(not n.is_squarefree() or any(p > 137 for p in n.prime_factors())
               for n in norms):
            continue
        column = {}
        for i, (K, v) in enumerate(zip(fields, elements)):
            for ideal, exponent in K.ideal(v).factor():
                assert exponent == 1 and ideal.residue_class_degree() == 1
                column[i, ideal] = exponent
        marks.append((a, b))
        columns.append(column)

    # The last column represents multiplication by ell in the first field.
    target = {(0, ideal): e for ideal, e in fields[0].ideal(ell).factor()}
    assert len(target) == 2 and all(e == 1 for e in target.values())
    columns.append(target)
    rows = list(dict.fromkeys(row for col in columns for row in col))
    incidence = matrix(ZZ, [[1]*len(marks) + [0]] +
                       [[col.get(row, 0) for col in columns] for row in rows])
    return marks, incidence


def split_from_relations(N, m, ell, fields, marks, incidence, relations):
    assert incidence * relations.transpose() == 0
    if relations.nrows() < 3:
        return None
    relations = relations.LLL()

    def field_product(i, relation):
        K = fields[i]
        v = prod((a - b*K.gen())**e for (a, b), e in zip(marks, relation) if e)
        return v * (K(ell)**relation[-1] if i == 0 else K.one())

    groups = [K.unit_group(proof=True) for K in fields]
    coordinates = []
    for relation in relations:
        row = [relation[-1]]
        for i, group in enumerate(groups):
            v = field_product(i, relation)
            assert fields[i].ideal(v) == fields[i].ideal(1)
            torsion, free = group.log(v)
            sign, fundamental = group.gens_values()
            assert sign**torsion * fundamental**free == v
            row.append(free)
        coordinates.append(row)
    coordinates = matrix(ZZ, coordinates)
    # Rank three certifies both unit directions on relations of target exponent zero.
    if coordinates.rank() != 3:
        return None
    multipliers = next(row for row in coordinates[:, 1:].transpose().right_kernel_matrix().rows()
                       if row.dot_product(coordinates.column(0)))
    combined = multipliers * relations
    if combined[-1] < 0:
        combined = -combined
    E = combined[-1]
    assert E > 0 and incidence * combined == 0
    signs = [field_product(i, combined) for i in range(2)]
    assert all(s in (-1, 1) for s in signs)
    common = prod(Mod(a - b*m, N)**e for (a, b), e in zip(marks, combined) if e)
    assert Mod(ell, N)**E * common == ZZ(signs[0]) and common == ZZ(signs[1])

    exponent = 2*E
    assert pow(ell, exponent, N) == 1
    odd_part = exponent.odd_part()
    residue = Mod(ell, N)**odd_part
    while residue**2 != 1:
        residue = residue**2
    divisor = gcd(ZZ(residue) - 1, N)
    return exponent, int(divisor) if 1 < divisor < N else None, signs, residue


def check_extraction():
    N, m, ell, fields = fixture()
    candidates = [(a, b) for b in range(1, 13) for a in range(-35, 36)]
    marks, incidence = collect_marks(N, m, ell, fields, candidates)
    assert incidence.dimensions() == (51, 54) and incidence[:, :-1].rank() == 51
    relations = incidence.right_kernel_matrix()
    assert relations.nrows() == 3
    exponent, divisor, signs, residue = split_from_relations(
        N, m, ell, fields, marks, incidence, relations
    )
    assert exponent == 88 and divisor is not None and N % divisor == 0
    print(f"{len(marks)} marks, valuation rank 51, joint exponent/unit rank 3")
    print(f"units {signs}, verified 7^{exponent} = 1 (mod 15), gcd({residue}-1, 15) = {divisor}")


if __name__ == "__main__":
    check_extraction()
