"""Match certified modular roots through rational square classes and integer lifts."""

from fractions import Fraction
from math import gcd, isqrt, prod
from pathlib import Path
from runpy import run_path


SQUARES = run_path(str(Path(__file__).with_name("cogentic-quadratic-square-kernel.py")))
GRID = SQUARES["GRID"]


def matched_basis(n, witnesses):
    """Return (mask, normalized residue) for a basis of rationally square products."""
    if n <= 1 or n % 2 == 0:
        raise ValueError("expected an odd modulus greater than one")
    values, residues = [], []
    for value, root in witnesses:
        value = Fraction(value)
        if (gcd(value.numerator, n) != 1 or gcd(value.denominator, n) != 1
                or (root*root*value.denominator - value.numerator) % n):
            raise ValueError("each rational label needs a verified modular unit root")
        values.append(value)
        residues.append(root)
    size = len(values)
    basis = GRID["eliminate"](SQUARES["rational_words"](values), (1 << i for i in range(size)))
    matched = []
    for mask in basis:
        indices = list(GRID["support"](mask))
        value = prod(values[i] for i in indices)
        scale = SQUARES["rational_sqrt"](value)
        assert scale is not None and scale**2 == value
        numerator = prod(residues[i] % n for i in indices) * scale.denominator
        root = numerator * pow(scale.numerator, -1, n) % n
        assert root*root % n == 1
        matched.append((mask, root))
    return matched


def replay():
    n = 93
    fields = [(1, (72, 20, 1), (9, 2)), (2, (51, 19, 1), (30, 1))]
    witnesses = []
    for m, (constant, linear, leading), (a, b) in fields:
        assert leading == 1 and m*m + linear*m + constant == n
        disc = linear*linear - 4*constant
        assert disc > 0 and isqrt(disc)**2 != disc and gcd(2*m+linear, n) == 1
        assert (constant, linear) == (81-a, 18+b)  # (X+9)^2 - (a-bX)
        witness = (a-b*m, m+9)
        assert matched_basis(n, [witness]) == []
        witnesses.append(witness)
    assert witnesses == [(7, 10), (28, 11)]
    first, = matched_basis(n, witnesses)
    assert first == (3, 61) and gcd(first[1]-1, n) == 3
    ceil_sqrt = isqrt(n-1)+1
    lift = (ceil_sqrt**2 - n, ceil_sqrt)
    assert matched_basis(n, [witnesses[1], lift]) == [first]
    # Replacing 7 by 7/4 changes its root by the same rational factor.
    assert matched_basis(n, [(Fraction(7, 4), 5), witnesses[1]]) == [first]
    for nonunit in (Fraction(7, 3), Fraction(31, 4)):
        try:
            matched_basis(n, [(nonunit, 2)])
        except ValueError:
            pass
        else:
            raise AssertionError("a numerator or denominator shares a prime with the modulus")

    # A different representative of the same modular unit can introduce a match.
    assert matched_basis(65, [(56, 11), (79, 12)]) == []
    lifted, = matched_basis(65, [(56, 11), (79-65, 12)])
    assert lifted == (3, 14) and gcd(lifted[1]-1, 65) == 13

    # Compare the generated kernel and its sign map with every compatible subset.
    tested = 0
    for modulus in (15, 45, 65, 77, 93, 105, 221, 437):
        menu = [(r*r-k*modulus, r) for r, k in ((2, 0), (2, 1), (4, 1), (7, 1),
                                                 (8, 1), (11, 1), (13, 2), (16, 2))
                if gcd(r, modulus) == 1]
        menu += [(4*value, 2*root) for value, root in menu[1:3]]
        span = {0: 1}
        for mask, root in matched_basis(modulus, menu):
            span.update({v ^ mask: z*root % modulus for v, z in span.items()})
        for mask in range(1 << len(menu)):
            selected = [menu[i] for i in GRID["support"](mask)]
            value = prod(v for v, _ in selected)
            ok = value > 0 and isqrt(value)**2 == value
            assert (mask in span) == ok
            if ok:
                z = prod(r for _, r in selected) * pow(isqrt(value), -1, modulus) % modulus
                assert (z-span[mask]) % modulus == 0 or (z+span[mask]) % modulus == 0
            tested += 1
    bounded = run_path(str(Path(__file__).with_name("cogentic-quadratic-grid-norms.py")))["bounded_words"]
    large = [101*103, 107**2*109, (113*127)**2, -131*137]
    grid_values = [1, -1, 2*large[0], *large, -large[1], large[0]]
    # Squares, repeated and signed tails, partial gcds, and new public-only primes.
    for extras in ([], [103*107], [103*131, 101*137, 2*109, 139],
                   [-101*109, 107, 137*113, 139*149, 139, 149, 151**2]):
        raw = [*grid_values, *extras]
        encoded = bounded(grid_values, 13, extra_values=extras)
        exact = SQUARES["rational_words"](raw)
        masks = [1 << j for j in range(len(raw))]
        assert GRID["eliminate"](encoded, masks) == GRID["eliminate"](exact, masks)
    print(f"independent bases and a canonical lift split 93; {tested} subset matches checked; "
          "four auxiliary-label kernels agree with unrestricted gcd refinement")


if __name__ == "__main__":
    replay()
