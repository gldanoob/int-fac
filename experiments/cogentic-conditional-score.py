"""Compare direct and separated conditional Gram energies using exact integers."""

from itertools import combinations_with_replacement, product


MARKS = tuple(range(1, 20))
SMOOTH = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
ROWS = (None, (0, 3, 1), (0, 5, 2), (1, 5, 3), (1, 7, 2), (1, 11, 5))


def polynomial(field, pair, mark):
    intercept, slope = pair
    baseline = mark**2 + (2 * field + 1) * mark + 2 + field
    return baseline + (mark - 23) * (intercept + mark * slope)


def squarefree_smooth(value):
    value = abs(value)
    for p in SMOOTH:
        if value % p == 0:
            value //= p
            if value % p == 0:
                return False
    return value == 1


def row_value(row, mark):
    if row is None:
        return 1
    _, prime, residue = row
    return prime if mark % prime == residue else 0


def field_record(field, pair, row_pairs):
    hits = [squarefree_smooth(polynomial(field, pair, mark)) for mark in MARKS]
    conditions = [
        all(r is None or r[0] != field or polynomial(field, pair, r[2]) % r[1] == 0
            for r in rows)
        for rows in row_pairs
    ]
    return hits, conditions


def energy(first, second, coefficients):
    first_hits, first_conditions = first
    second_hits, second_conditions = second
    both = [i for i in range(len(MARKS)) if first_hits[i] and second_hits[i]]
    return sum(
        sum(row[i] for i in both) ** 2
        for row, keep1, keep2 in zip(coefficients, first_conditions, second_conditions)
        if keep1 and keep2
    )


def main():
    row_pairs = list(combinations_with_replacement(ROWS, 2))
    # Mark weights and centering constants are intentionally integral in this replay.
    coefficients = [
        [(1 + a % 4) * (row_value(r, a) * row_value(s, a) - 1 - t % 3) for a in MARKS]
        for t, (r, s) in enumerate(row_pairs)
    ]
    first_fields = [field_record(0, pair, row_pairs) for pair in product(range(9), range(5))]
    second_fields = [field_record(1, pair, row_pairs) for pair in product(range(8), range(6))]
    marks = range(len(MARKS))
    second_moments = [
        [[sum(ok[t] and h[i] and h[j] for h, ok in second_fields) for j in marks] for i in marks]
        for t in range(len(coefficients))
    ]
    conditional = []
    for first in first_fields:
        hits, conditions = first
        separated = sum(
            row[i] * row[j] * second_moments[t][i][j]
            for t, row in enumerate(coefficients) if conditions[t]
            for i in marks if hits[i] for j in marks if hits[j]
        )
        direct = sum(energy(first, second, coefficients) for second in second_fields)
        assert separated == direct
        conditional.append(separated)
    winner = min(range(len(conditional)), key=conditional.__getitem__)
    minimum = min(energy(first_fields[winner], second, coefficients) for second in second_fields)
    assert 0 < sum(conditional)
    assert minimum * len(second_fields) <= conditional[winner]
    assert conditional[winner] * len(first_fields) <= sum(conditional)
    print(f"{len(row_pairs)} row pairs, {len(MARKS)} marks, {len(conditional)} exact conditional sums")
    print(f"{len(first_fields)*len(second_fields)} joint boxes, total centered energy {sum(conditional)}")


if __name__ == '__main__':
    main()
