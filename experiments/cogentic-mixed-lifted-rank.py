"""Carry modular square roots through local-basis incidence elimination."""

from fractions import Fraction
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


GRID = run_path(str(Path(__file__).with_name("cogentic-monic-large-primes.py")))
support, eliminate = GRID["support"], GRID["eliminate"]


def lifted_dependencies(n, values, generators):
    """Yield dependency masks and normalized roots from local (mask, residue) pairs."""
    if n <= 1 or n % 2 == 0 or any(gcd(value, n) != 1 for value in values):
        raise ValueError("need an odd modulus and common unit column residues")
    pivots = {}
    for i, (word, root) in enumerate(generators):
        if word < 0 or word.bit_length() > len(values):
            raise ValueError("a local mask exceeds the supplied column set")
        assert root**2 % n == prod(values[j] for j in support(word)) % n
        history = 1 << i
        while word and (pivot := word.bit_length()) in pivots:
            earlier, earlier_root, earlier_history = pivots[pivot]
            overlap = prod(values[j] for j in support(word & earlier))
            root = root*earlier_root*pow(overlap, -1, n) % n
            history ^= earlier_history
            word ^= earlier
        if word:
            pivots[word.bit_length()] = word, root, history
        else:
            assert root**2 % n == 1
            yield history, root % n


def crt_rank(n, roots):
    """Rank of their sign classes, computed by gcd refinement of the modulus."""
    roots = tuple(roots)
    blocks = [n]
    for root in roots:
        assert root**2 % n == 1
        refined = []
        for block in blocks:
            positive = gcd(root-1, block)
            refined.extend(part for part in (positive, block//positive) if part > 1)
        blocks = refined
    rows = []
    for root in roots:
        base = root % blocks[0] == 1
        rows.append(sum(1 << j for j, block in enumerate(blocks[1:])
                        if (root % block == 1) != base))
    return len(rows)-len(eliminate(rows, (1 << j for j in range(len(rows)))))


def jacobi_bit(value, n):
    """Return zero for Jacobi +1 and one for Jacobi −1 on a unit."""
    a, bit = value % n, 0
    while a:
        while a % 2 == 0:
            a //= 2
            bit ^= n % 8 in (3, 5)
        bit ^= a % 4 == n % 4 == 3
        a, n = n % a, a
    if n != 1:
        raise ValueError("Jacobi sign requires a unit")
    return bit


def jacobi_gain(n, values, generators):
    """Rank gain after adding the Jacobi character of the lifted roots."""
    if n <= 1 or n % 4 != 1:
        raise ValueError("the Jacobi character must be trivial on the global sign")
    bits = [jacobi_bit(value, n) for value in values]
    original, augmented = [], []
    for word, root in generators:
        total = sum(bits[j] for j in support(word))
        assert total % 2 == 0 and root**2 % n == prod(values[j] for j in support(word)) % n
        row_bit = jacobi_bit(root, n) ^ (total//2 % 2)
        original.append(word)
        augmented.append(word | (row_bit << len(values)))
    basis = [1 << j for j in range(len(generators))]
    return len(eliminate(original, basis))-len(eliminate(augmented, basis))


def is_square(value):
    return value >= 0 and isqrt(value)**2 == value


def replay():
    # Canonical roots of the adjacent products from the existing N=209 cycle.
    n, m = 209, 13
    values = (2, -130, 10, 46)
    masks = (0b0011, 0b0110, 0b1100, 0b1001)
    products = [prod(values[j] for j in support(word)) for word in range(1 << len(values))]
    for k, scale in ((28, 5), (64, 13)):
        assert k*k-n == 23*scale**2
        multiples = (Fraction(2), Fraction(-10), Fraction(2), Fraction(2, scale))
        generators = []
        for mark, parameter, multiplier in zip(masks, (12, 14, 18, k), multiples, strict=True):
            delta = parameter**2-n
            assert ((m-parameter)**2-delta) % 4 == 2 and gcd(2*parameter, n) == 1
            assert multiplier**2 * delta == prod(values[j] for j in support(mark))
            assert [word for word, value in enumerate(products)
                    if is_square(value) or is_square(value*delta)] == [0, mark]
            root = parameter*multiplier.numerator*pow(multiplier.denominator, -1, n) % n
            generators.append((mark, root))
        (history, ratio), = lifted_dependencies(n, values, generators)
        assert history == 0b1111
        expected = int(k == 28)
        assert crt_rank(n, [ratio]) == jacobi_gain(n, values, generators) == expected
        assert ratio == (153 if expected else n-1)
        divisor = gcd(ratio-1, n)
        assert divisor == (19 if expected else 1)
        print(f"k={k}: four-way mark dependency, CRT rank {expected}, ratio {ratio}")
    assert crt_rank(105, (104, 71, 64, 71*64 % 105)) == 2
    assert jacobi_bit(3, n) == 1
    repeated = ((0b011, 3), (0b110, 3), (0b101, 3))
    assert jacobi_gain(n, (3, 3, 3), repeated) == 0
    assert jacobi_gain(n, (3, 3, 3), (*repeated[:2], (0b101, 3*153 % n))) == 1


if __name__ == "__main__":
    replay()
