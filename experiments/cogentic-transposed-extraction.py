"""Check lifted transpose projections on the engineered two-field fixture."""

from pathlib import Path
from runpy import run_path

from sage.all import GF, QQ, ZZ, RealField, lcm, matrix, rational_reconstruction, vector


HERE = Path(__file__).parent
EXACT = run_path(str(HERE / "cogentic-real-extractor-sage.py"))
pivot_lists = run_path(str(HERE / "cogentic-randomized-extraction.py"))["pivot_lists"]


def lifted_rows(system, right_sides, prime):
    """Solve square integral systems using one modular inverse and exact lifting."""
    ring = GF(prime)
    inverse = system.change_ring(ring).inverse()
    dimension = system.nrows()
    matrix_bound = (dimension * max(1, max(map(abs, system.list()))))**dimension
    answers = []
    for right_side in right_sides:
        bound = matrix_bound * max(1, max(map(abs, right_side)))
        residual = vector(ZZ, right_side)
        solution = vector(ZZ, dimension)
        modulus = 1
        while modulus <= 2*bound**2:
            digit = vector(ZZ, inverse * residual.change_ring(ring))
            difference = residual - system*digit
            assert all(value % prime == 0 for value in difference)
            residual = vector(ZZ, (value // prime for value in difference))
            solution += modulus*digit
            modulus *= prime
        answer = vector(QQ, [rational_reconstruction(value, modulus) for value in solution])
        assert system*answer == right_side
        answers.append(answer)
    return answers


def dyadic_logs(fields, marks, ell, bits):
    real = RealField(bits + 32)
    scale = 1 << bits
    rows = []
    for i, field in enumerate(fields):
        root = max(field.polynomial().roots(real, multiplicities=False))
        values = [abs(a - b*root).log() for a, b in marks]
        values.append(real(ell).log() if i == 0 else real(0))
        rows.append(vector(ZZ, [ZZ((scale*value).round()) for value in values]))
    return rows


def replay():
    n, m, ell, fields = EXACT["fixture"]()
    grid = [(a, b) for b in range(1, 19) for a in range(-55, 56)]
    marks, incidence = EXACT["collect_marks"](n, m, ell, fields, grid)
    target_index = incidence.ncols() - 1
    columns = [list(map(int, column)) for column in incidence.columns()]
    prime = 11
    rows, pivots = pivot_lists(columns[:-1], prime)
    minor = incidence.matrix_from_rows_and_columns(rows, pivots)
    free = [j for j in range(target_index) if j not in pivots]
    assert len(free) >= 2

    projected_checks = 0
    for bits in (64, 192):
        logs = dyadic_logs(fields, marks, ell, bits)
        right_sides = [vector(ZZ, [row[j] for j in pivots]) for row in logs]
        lifted = lifted_rows(minor.transpose(), right_sides, prime)
        exact = [minor.transpose().change_ring(QQ).solve_right(rhs) for rhs in right_sides]
        assert lifted == exact
        denominator = lcm(entry.denominator() for row in lifted for entry in row)
        assert minor.det() % denominator == 0
        numerators = [vector(ZZ, denominator*row) for row in lifted]
        projected = {}
        for j in [*free, target_index]:
            column = vector(ZZ, [columns[j][i] for i in rows])
            projected[j] = tuple(denominator*row[j] - sum(lam[k]*entry for k, entry in column.items())
                                 for row, lam in zip(logs, numerators, strict=True))
            primal = minor.change_ring(QQ).solve_right(column)
            assert projected[j] == tuple(denominator*(row[j] - rhs.dot_product(primal))
                                         for row, rhs in zip(logs, right_sides, strict=True))
            projected_checks += 1

        first = max(free, key=lambda j: sum(v*v for v in projected[j]))
        x, y = projected[first]
        second = max(free, key=lambda j: abs(x*projected[j][1] - y*projected[j][0]))
        assert x*projected[second][1] != y*projected[second][0]

        selected = [first, second, target_index]
        finite = incidence.matrix_from_rows_and_columns(rows, selected)
        coefficients = lifted_rows(minor, (-finite).columns(), prime)
        relations = []
        for j, column in zip(selected, coefficients, strict=True):
            denominator = lcm(entry.denominator() for entry in column)
            relation = [0]*incidence.ncols()
            for index, entry in zip(pivots, column, strict=True):
                relation[index] = denominator*entry
            relation[j] = denominator
            relations.append(relation)
        result = EXACT["split_from_relations"](n, m, ell, fields, marks, incidence,
                                             matrix(ZZ, relations))
        assert result is not None
        exponent, divisor, _, _ = result
        assert pow(ell, exponent, n) == 1 and 1 < divisor < n and n % divisor == 0
    print(f"Checked {projected_checks} projected columns at two precisions; verified a split of {n}.")


if __name__ == "__main__":
    replay()
