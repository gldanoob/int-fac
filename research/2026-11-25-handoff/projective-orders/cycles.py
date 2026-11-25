"""Enumerate exact projective fibers of the Frobenius cycle-sum map."""

from collections import Counter
from itertools import product
from math import prod


def partitions(size, minimum=1):
    if not size:
        yield ()
    for part in range(minimum, size + 1):
        for rest in partitions(size - part, part):
            yield (part, *rest)


def valuation2(value):
    return (value & -value).bit_length() - 1


def check(shape, prime):
    moduli = tuple(1 << valuation2(prime**length - 1) for length in shape)
    scalar_modulus = 1 << valuation2(prime - 1)
    phase_modulus = max(moduli)
    cycle_weights = [tuple(prime**j for j in reversed(range(length))) for length in shape]
    scalar_weights = [sum(weights) for weights in cycle_weights]
    scalars = [
        tuple(scalar * weight % modulus for weight, modulus in zip(scalar_weights, moduli))
        for scalar in range(scalar_modulus)
    ]
    assert len(set(scalars)) == scalar_modulus

    counts = Counter()
    # Fix the first root phase at zero, which represents one projective phase tuple.
    for tail in product(range(phase_modulus), repeat=sum(shape) - 1):
        phases = iter((0, *tail))
        coordinates = tuple(
            sum(next(phases) * weight for weight in weights) % modulus
            for weights, modulus in zip(cycle_weights, moduli)
        )
        representative = min(
            tuple((x + s) % modulus for x, s, modulus in zip(coordinates, scalar, moduli))
            for scalar in scalars
        )
        counts[representative] += 1

    expected_size = prod(moduli) // scalar_modulus
    assert len(counts) == expected_size
    assert set(counts.values()) == {phase_modulus ** (sum(shape) - 1) // expected_size}


if __name__ == "__main__":
    count = 0
    for degree in (3, 4):
        for shape in partitions(degree):
            for prime in (3, 5, 7, 11, 17):
                check(shape, prime)
                count += 1
    print(f"Exact projective phase fibers checked for {count} splitting profiles")
