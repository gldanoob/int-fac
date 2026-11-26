"""Replay two finite sign tests with supplied relation or exponent data."""

from math import gcd, prod
from pathlib import Path
from runpy import run_path


GRID = run_path(str(Path(__file__).with_name("cogentic-monic-large-primes.py")))


def certified_signs(modulus, ratios, columns):
    """Yield signs and root exponents from columns certified to be mark relations."""
    ratios = (modulus - 1, *ratios)
    columns = [(0, *column) for column in columns]
    columns.append((2, *([0] * (len(ratios) - 1))))
    if any(len(column) != len(ratios) for column in columns):
        raise ValueError("relation dimensions do not match the generators")
    if any(gcd(ratio, modulus) != 1 for ratio in ratios):
        raise ValueError("generator ratios must be units")
    if any(prod(pow(ratio, exponent, modulus)
                for ratio, exponent in zip(ratios, column, strict=True)) % modulus != 1
           for column in columns):
        raise ValueError("relation ratios must reduce to one")

    parity = GRID["parity_words"]([
        [i for i, exponent in enumerate(column) if exponent % 2] for column in columns
    ])
    dependencies = GRID["eliminate"](parity, (1 << i for i in range(len(columns))))
    for dependency in dependencies:
        selected = list(GRID["support"](dependency))
        exponents = tuple(sum(columns[j][i] for j in selected) // 2 for i in range(len(ratios)))
        sign = prod(pow(ratio, exponent, modulus)
                    for ratio, exponent in zip(ratios, exponents, strict=True)) % modulus
        yield sign, exponents, selected


def exponent_split(modulus, ratios, exponent):
    """Find a mixed sign in the generated group, given a verified exponent multiple."""
    if exponent < 1:
        raise ValueError("the exponent multiple must be positive")
    if any(pow(ratio, exponent, modulus) != 1 for ratio in ratios):
        raise ValueError("the supplied exponent does not kill the generators")
    odd_part = exponent // (exponent & -exponent)

    def top(value):
        height = 0
        while value != 1:
            square = value * value % modulus
            height += 1
            if square == 1:
                return height, value
            value = square
        return 0, 1

    projected = [pow(ratio, odd_part, modulus) for ratio in (*ratios, modulus - 1)]
    levels = [top(value) for value in projected]
    for height, involution in levels:
        if height and involution != modulus - 1:
            return involution
    max_height = max(height for height, _ in levels)
    generator = projected[next(i for i, (height, _) in enumerate(levels) if height == max_height)]
    inverse_powers = [pow(generator, -1, modulus)]
    for _ in range(max_height - 1):
        inverse_powers.append(inverse_powers[-1] ** 2 % modulus)
    for value, (height, involution) in zip(projected, levels, strict=True):
        while height:
            if involution != modulus - 1:
                return involution
            value = value * inverse_powers[max_height - height] % modulus
            height, involution = top(value)
    return None


def replay():
    for parameter in (2, 3, 10, 100):
        m = 2 * parameter**2
        modulus = m*m + 1
        # With beta^2=-1, the product of the two pairs is (2v, 1+beta).
        # Its square equals (2m, 2beta), the ordinary mark 2X.
        ratios = (pow(m, -1, modulus), 2 * parameter * pow(1 - m, -1, modulus) % modulus)
        assert pow(ratios[0], 4, modulus) == 1
        assert (ratios[0] * ratios[1])**2 % modulus == 1
        signs = list(certified_signs(modulus, ratios, [(4, 0), (2, 2)]))
        split = next(gcd(sign - 1, modulus) for sign, _, _ in signs if sign not in (1, modulus - 1))
        assert split == m + 1 - 2 * parameter
        assert modulus // split == m + 1 + 2 * parameter

    assert exponent_split(65, (8,), 4) is None
    assert exponent_split(65, (64, 27), 4) == 14
    sign = exponent_split(65, (8, 18), 4)
    assert sign == 51 and gcd(sign - 1, 65) == 5

    # The two displayed relations are both odd vectors. Their sum gives the splitting root.
    signs = list(certified_signs(65, (51, 51), [(1, 1), (1, -1)]))
    assert (51, (0, 1, 0), [0, 1]) in signs
    print("Verified certified relation signs and exponent-only sign detection")


if __name__ == "__main__":
    replay()
