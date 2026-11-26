#!/usr/bin/env python3
"""Replay stratified interval, box, and mixed smoothness bounds exactly."""

from collections import defaultdict
from fractions import Fraction
from itertools import product


def stratified(lower, length, strata, samples):
    count = min(strata, length)
    for index in range(count):
        start = lower + index * length // count
        stop = lower + (index + 1) * length // count
        taken = min(samples, stop - start)
        weight = Fraction(stop - start, length * taken)
        for value in range(start, start + taken):
            yield value, weight


def uniform(lower, length):
    return [(value, Fraction(1, length)) for value in range(lower, lower + length)]


def box_law(coordinates):
    for weighted_tuple in product(*coordinates):
        values, weights = zip(*weighted_tuple)
        mass = Fraction(1)
        for weight in weights:
            mass *= weight
        yield values, mass


def mass(law, predicate):
    return sum((weight for value, weight in law if predicate(value)), Fraction())


def interval_residue_count(lower, upper, modulus, residue):
    return (upper - 1 - residue) // modulus - (lower - 1 - residue) // modulus


def check_intervals():
    checked = 0
    lower = -17
    for length, strata, samples in product((1, 2, 11, 31, 137, 307),
                                           (1, 5, 19), (1, 3, 13)):
        sample = dict(stratified(lower, length, strata, samples))
        assert len(sample) <= strata * samples
        assert sum(sample.values()) == 1
        assert all(abs(sample.get(point, 0) - Fraction(1, length))
                   <= Fraction(1, strata * samples)
                   for point in range(lower, lower + length))
        ends = sorted({lower - 2, lower, lower + 1, lower + length // 3,
                       lower + length // 2, lower + length - 1,
                       lower + length, lower + length + 2})
        error = Fraction(2, samples) + Fraction(4, strata)
        for left, right in product(ends, repeat=2):
            if left > right:
                continue
            start, stop = max(left, lower), min(right, lower + length)
            for modulus in (1, 2, 3, 6, 19, 401):
                for residue in {0, 1 % modulus, (modulus - 1) % modulus}:
                    exact = Fraction(max(0, interval_residue_count(start, stop, modulus, residue)), length)
                    sampled = mass(sample.items(), lambda x: left <= x < right
                                   and x % modulus == residue)
                    assert abs(exact - sampled) <= error
                    checked += 1
    return checked


def mixed_affine_tests(point, bound, wanted):
    first, second, third, fourth = point
    linear = -2 * first + 5 * second - third + 7 * fourth
    modular = 6 * first + 4 * second - 8 * third + 10 * fourth
    return (-bound <= linear <= bound
            and modular % 12 == wanted
            and (2 * first - 3 * second + fourth) % 5 == 0
            and (-first + second - third) % 6 == 1)


def check_boxes():
    intervals = [(-5, 283), (2, 5), (-3, 3), (9, 2)]
    strata, samples = 16, 16
    original = [uniform(*interval) for interval in intervals]
    sampled = [list(stratified(*interval, strata, samples)) for interval in intervals]
    assert sampled[1:] == original[1:]
    original_law = list(box_law(original))
    sampled_law = list(box_law(sampled))
    error = Fraction(2, samples) + Fraction(4, strata)
    positive = 0
    for bound, wanted in product((20, 100, 500, 1000), range(12)):
        def test(point):
            return mixed_affine_tests(point, bound, wanted)
        exact = mass(original_law, test)
        approx = mass(sampled_law, test)
        assert abs(exact - approx) <= error
        if wanted % 2:
            assert exact == approx == 0
        if exact > 0:
            positive += 1
    assert positive > 0
    return 48


def check_two_replacements():
    intervals = [(-127, 267), (17, 271)]
    strata, samples = 16, 16
    original = [uniform(*interval) for interval in intervals]
    sampled = [list(stratified(*interval, strata, samples)) for interval in intervals]
    assert all(len(new) < len(old) for new, old in zip(sampled, original))
    laws = [
        list(box_law(original)),
        list(box_law([sampled[0], original[1]])),
        list(box_law(sampled)),
    ]
    error = Fraction(2, samples) + Fraction(4, strata)
    for residue in range(3):
        def test(point):
            x, y = point
            return -100 <= 5 * x - 2 * y <= 300 and (6 * x + 9 * y) % 15 == 3 * residue
        exact, intermediate, approximation = [mass(law, test) for law in laws]
        assert abs(exact - intermediate) <= error
        assert abs(intermediate - approximation) <= error
        assert abs(exact - approximation) <= 2 * error
    return 3


def smooth(value, primes, max_factors):
    value = abs(value)
    if value == 0:
        return False
    factors = 0
    for prime in primes:
        if value % prime == 0:
            value //= prime
            factors += 1
            if value % prime == 0 or factors > max_factors:
                return False
    return value == 1


def check_sparse_smoothness():
    lower, length, strata, samples = -389, 821, 19, 17
    original = uniform(lower, length)
    sampled = list(stratified(lower, length, strata, samples))
    checked = 0
    for constant, coefficient, max_factors in product((-22, 0, 14), (-7, 2, 3), (0, 1, 2)):
        def test(value):
            return (smooth(constant + coefficient * value, (3, 5, 7, 11), max_factors)
                    and (value % 5 == 2 or smooth(5 - 2 * value, (2, 3, 7), 3)))
        accepted = sum(test(value) for value, _ in original)
        bound = Fraction(accepted, strata * samples)
        assert abs(mass(original, test) - mass(sampled, test)) <= bound
        checked += 1
    test = lambda x: smooth(x + 1, (3, 5, 7), 3)
    assert mass(uniform(0, 16), test) == Fraction(5, 16)
    assert mass(stratified(0, 16, 4, 2), test) == Fraction(1, 4)
    return checked


def fixed_mark_law(intercepts, slopes, mark, strata, samples):
    u_min, u_length = intercepts
    v_min, v_length = slopes
    u_max, v_max = u_min + u_length - 1, v_min + v_length - 1
    for combined in range(u_min + mark * v_min, u_max + mark * v_max + 1):
        lower = max(v_min, -((u_max - combined) // mark))
        upper = min(v_max, (combined - u_min) // mark)
        if lower <= upper:
            length = upper - lower + 1
            weight = Fraction(length, u_length * v_length)
            for slope, conditional_weight in stratified(lower, length, strata, samples):
                yield (combined - mark * slope, slope), weight * conditional_weight


def check_fixed_mark():
    intercepts, slopes = (-53, 113), (-33, 89)
    strata, samples = 11, 5
    original = list(box_law([uniform(*intercepts), uniform(*slopes)]))
    checked = 0
    differences = 0
    for mark in (1, 2, 5):
        sampled = list(fixed_mark_law(intercepts, slopes, mark, strata, samples))
        exact_by_value = defaultdict(Fraction)
        sampled_by_value = defaultdict(Fraction)
        for law, totals in ((original, exact_by_value), (sampled, sampled_by_value)):
            for (intercept, slope), weight in law:
                totals[intercept + mark * slope] += weight
        assert exact_by_value == sampled_by_value
        for constant, residue in product((-4, 3, 12), range(6)):
            def test(point):
                intercept, slope = point
                return (smooth(constant + 2 * (intercept + mark * slope), (3, 5, 7, 11), 4)
                        and -50 <= intercept - 4 * slope <= 70
                        and (4 * intercept + 6 * slope) % 6 == residue)
            difference = abs(mass(original, test) - mass(sampled, test))
            assert difference <= Fraction(2, samples) + Fraction(4, strata)
            differences += difference > 0
            checked += 1
    assert differences > 0
    return checked


def main():
    print(f'{check_intervals()} interval-residue checks passed')
    print(f'{check_boxes()} four-coordinate affine checks passed')
    print(f'{check_two_replacements()} two-replacement hybrid checks passed')
    print(f'{check_sparse_smoothness()} sparse smoothness checks passed')
    print(f'{check_fixed_mark()} fixed-mark smoothness checks passed')


if __name__ == '__main__':
    main()
