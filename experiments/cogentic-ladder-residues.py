#!/usr/bin/env python3
"""Exact interval counts and conditional selection for modular degree-ladder terms."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd, prod


def state_index(state, modulus):
    index = 0
    for coordinate in state:
        index = modulus * index + coordinate % modulus
    return index


def residue_counts(modulus, offset, columns, intervals):
    """Count offset + sum(t_j column_j), for t_j in [start_j, start_j+length_j)."""
    if modulus < 1 or len(columns) != len(intervals):
        raise ValueError("expected a positive modulus and one interval per column")
    dimension = len(offset)
    size = modulus ** dimension
    counts = [0] * size
    counts[state_index(offset, modulus)] = 1
    for column, (start, length) in zip(columns, intervals):
        if len(column) != dimension or length < 1:
            raise ValueError("expected equal state dimensions and nonempty intervals")
        period = modulus // gcd(modulus, *column)
        cycles, tail = divmod(length, period)
        seen = bytearray(size)
        updated = [0] * size
        for seed in product(range(modulus), repeat=dimension):
            index = state_index(seed, modulus)
            if seen[index]:
                continue
            orbit = []
            state = seed
            for _ in range(period):
                seen[index] = 1
                orbit.append(index)
                state = tuple((x + step) % modulus for x, step in zip(state, column))
                index = state_index(state, modulus)
            whole = cycles * sum(counts[i] for i in orbit)
            end = -start % period
            window = sum(counts[orbit[(end - j) % period]] for j in range(tail))
            for i in orbit:
                updated[i] = whole + window
                end = (end + 1) % period
                window += counts[orbit[end]] - counts[orbit[(end - tail) % period]]
        counts = updated
    return counts


def score_sum(terms, intervals):
    total = 0
    for modulus, offset, columns, values in terms:
        counts = residue_counts(modulus, offset, columns, intervals)
        if len(values) != len(counts):
            raise ValueError("expected one score per residue state")
        total += sum(count * value for count, value in zip(counts, values))
    return total


def select(terms, intervals):
    """Choose a tuple scoring at most its box average, including for signed scores."""
    intervals = list(intervals)
    total = score_sum(terms, intervals)
    for axis, (start, length) in enumerate(intervals):
        while length > 1:
            left = length // 2
            intervals[axis] = (start, left)
            left_total = score_sum(terms, intervals)
            if left_total * length <= total * left:
                length, total = left, left_total
            else:
                start, length = start + left, length - left
                total -= left_total
            intervals[axis] = (start, length)
    return tuple(start for start, _ in intervals), total


def ladder_columns(m, shift, marks, level, degrees, evaluation, derivative):
    first, second = marks
    columns = []
    for j in degrees:
        if j < level or second == first:
            raise ValueError("expected distinct marks and a ladder suffix")
        h1, h2 = ((shift + mark) ** (j - level) for mark in marks)
        at_derivative = shift + derivative
        slope = -at_derivative ** j
        if j:
            slope += (m - derivative) * j * at_derivative ** (j - 1)
        columns.append(((m - evaluation) * (shift + evaluation) ** j, slope,
                        h1, (h2 - h1) // (second - first)))
    return columns


def direct_state(modulus, offset, columns, word):
    return tuple((x + sum(t * column[i] for t, column in zip(word, columns))) % modulus
                 for i, x in enumerate(offset))


def check():
    intervals = [(1, 4), (2, 6), (3, 4), (4, 5), (1, 7)]
    columns = ladder_columns(23, 5, (2, 5), 1, range(1, 6), 4, 7)
    words = list(product(*(range(x, x + n) for x, n in intervals)))
    terms = []
    for modulus, offset in [(7, (0, 0, 0, 0)), (6, (-9, 1, 3, 5))]:
        counts = residue_counts(modulus, offset, columns, intervals)
        direct = Counter(state_index(direct_state(modulus, offset, columns, word), modulus)
                         for word in words)
        assert counts == [direct[i] for i in range(modulus ** 4)]
        if modulus == 7:
            assert Counter(direct.values()) == {2: 168, 3: 1008}
        values = [Fraction((-3 if x == 0 else int(y == z)) + int(w == 1), modulus)
                  for x, y, z, w in product(range(modulus), repeat=4)]
        terms.append((modulus, offset, columns, values))

    word, score = select(terms, intervals)
    def evaluate(word):
        return sum(values[state_index(direct_state(mod, off, cols, word), mod)]
                   for mod, off, cols, values in terms)
    assert score == evaluate(word)
    assert score * len(words) <= sum(map(evaluate, words))
    # Signed origins, a zero column, and a nonprimitive nonzero column of order three.
    length = 10 ** 50 + 2
    counts = residue_counts(6, (1, -3), [(0, 0), (-2, 2)], [(-49, 9), (-5, length)])
    expected = [0] * 36
    for residue in range(3):
        weight = (length + 2 - residue) // 3
        index = state_index((1 - 2 * (-5 + residue), -3 + 2 * (-5 + residue)), 6)
        expected[index] = 9 * weight
    assert counts == expected
    assert residue_counts(1, (0,), [(5,)], [(-12, length)]) == [length]
    assert residue_counts(4, (2,), [], []) == [0, 0, 1, 0]
    assert prod(n for _, n in intervals) == len(words)
    print(f"degree ladder: {len(words)} tuples at both moduli, 1176 occupied states mod 7;"
          f" exact modular selection {word} with score {score}; long interval passed")


if __name__ == "__main__":
    check()
