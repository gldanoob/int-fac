"""Restrict quadratic-grid square descent to rational classes on the discriminant support."""

from ast import literal_eval
from fractions import Fraction
from math import gcd, isqrt
from pathlib import Path
from runpy import run_path
from time import perf_counter


HERE = Path(__file__).resolve().parent
LATTICE = run_path(str(HERE / "cogentic-monic-lattice-sieve.py"))
GRID = LATTICE["GRID"]
QUADRATIC = run_path(str(HERE / "cogentic-quadratic-square-kernel.py"))


def split_support(value, modulus):
    """Split a positive integer into its supported and coprime parts by gcd."""
    if value < 1 or modulus < 1:
        raise ValueError("support splitting requires positive integers")
    inside = gcd(value, modulus)
    outside = value // inside
    while (common := gcd(inside, outside)) != 1:
        inside *= common
        outside //= common
    return inside, outside


def away_basis(field, points, height, *, include_sign=True):
    """Original-coordinate kernel of norm and ideal-parity constraints away from 2D."""
    v, u, leading = field
    d = u*u-4*v
    if leading != 1 or not d or QUADRATIC["rational_sqrt"](d) is not None or height < 1:
        raise ValueError("expected an irreducible monic quadratic and positive height")
    points = tuple(points)
    indices = {point: i for i, point in enumerate(points)}
    if len(indices) != len(points) or any(not 1 <= b <= height or abs(a) > height or gcd(a, b) != 1
                                          for a, b in points):
        raise ValueError("expected distinct primitive grid marks")

    modulus = abs(2*d)
    supported, residuals = [], []
    for a, b in points:
        value = a*a+u*a*b+v*b*b
        inside, outside = split_support(abs(value), modulus)
        supported.append(inside if value > 0 else -inside)
        residuals.append(outside)

    primes = [p for p in GRID["primes_through"](2*height*height) if modulus % p]
    columns = [[] for _ in points]
    code = LATTICE["ROOTS"] + f"iferr(emit_roots({[list(field)]},{primes}),err,print(err);quit(1));\n"
    for line in GRID["gp"](code, timeout=None):
        _, p, roots = literal_eval(line)
        for root in roots:
            for point in LATTICE["lattice_marks"](p, root, height):
                i = indices.get(point)
                if i is None:
                    continue
                odd, value = False, residuals[i]
                assert value % p == 0
                while value % p == 0:
                    value //= p
                    odd = not odd
                residuals[i] = value
                if odd:
                    columns[i].append((0, p, root))

    eligible = [i for i, tail in enumerate(residuals) if isqrt(tail)**2 == tail]
    rows = [columns[i] for i in eligible]
    for column, word in zip(rows, QUADRATIC["rational_words"](supported[i] for i in eligible), strict=True):
        column.extend((1, bit) for bit in GRID["support"](word))
    count = len(eligible)
    if include_sign:
        eligible.append(len(points))
        rows.append([])
    core, basis = GRID["parity_basis"](rows)
    lift = [1 << eligible[j] for j in core]
    return [GRID["combine"](mask, lift) for mask in basis], count, len(core)


def marked_elements(field, points, *, include_sign=True):
    v, u, _ = field
    d = u*u-4*v
    elements = [(Fraction(2*a+u*b, 2), Fraction(-b, 2)) for a, b in points]
    if include_sign:
        elements.append((-1, 0))
    return d, elements


def descent_scalars(d, elements, basis):
    return [QUADRATIC["descent"](d, QUADRATIC["masked_product"](d, elements, mask))[0] for mask in basis]


def supported_scalars(d, scalars):
    """Remove square cofactors away from 2D after the away-parity filter."""
    d = Fraction(d)
    modulus = 2*abs(d.numerator)*d.denominator
    reduced = []
    for scalar in scalars:
        num, other_num = split_support(abs(scalar.numerator), modulus)
        den, other_den = split_support(scalar.denominator, modulus)
        if isqrt(other_num)**2 != other_num or isqrt(other_den)**2 != other_den:
            raise ValueError("descended scalar violates the away-parity precondition")
        reduced.append(Fraction(num if scalar > 0 else -num, den))
    return reduced


def descent_masks(d, basis, scalars):
    words = QUADRATIC["rational_words"]([*scalars, d])
    return GRID["eliminate"](words, [*basis, 0])


def solve_descent(d, elements, basis, scalars):
    result = []
    for mask in descent_masks(d, basis, scalars):
        product = QUADRATIC["masked_product"](d, elements, mask)
        root = QUADRATIC["square_root"](d, product)
        assert root is not None and QUADRATIC["multiply"](d, root, root) == product
        result.append((mask, root))
    return result


def marked_square_kernel(field, points, height, *, include_sign=True):
    points = tuple(points)
    basis, _, _ = away_basis(field, points, height, include_sign=include_sign)
    d, elements = marked_elements(field, points, include_sign=include_sign)
    scalars = supported_scalars(d, descent_scalars(d, elements, basis))
    return solve_descent(d, elements, basis, scalars)


def grid_square_masks(field, points, height, *, packed_roots):
    """Full field square space, including the sign coordinate, on a primitive grid."""
    d, elements = marked_elements(field, points)
    if QUADRATIC["rational_sqrt"](d) is not None:
        raise ValueError("expected an irreducible quadratic")
    if packed_roots:
        basis, _, _ = away_basis(field, points, height)
        scalars = supported_scalars(d, descent_scalars(d, elements, basis))
    elif field[1] in (0, -1, -2):
        norm_basis = run_path(str(HERE / "cogentic-quadratic-grid-norms.py"))["norm_basis"]
        basis = norm_basis(field, points, height)
        scalars = descent_scalars(d, elements, basis)
    else:
        return QUADRATIC["square_masks"](d, elements)
    return descent_masks(d, basis, scalars)


def replay():
    points = ((1, 1), (-1, 1))
    assert not marked_square_kernel((12, 0, 1), points, 1, include_sign=False)
    assert away_basis((12, 0, 1), points, 1, include_sign=False) == ([], 0, 0)
    assert split_support(2**31*3**27*5**22, 6) == (2**31*3**27, 5**22)
    assert supported_scalars(-5, [Fraction(-10*7**2, 11**2)]) == [-10]
    try:
        supported_scalars(-5, [Fraction(77)])
    except ValueError:
        pass
    else:
        raise AssertionError("accepted a nonsquare scalar cofactor")

    print("N H marks nonprivate core descent square scalar-bits before/after generic/supported seconds")
    for n, height in ((77, 12), (221, 16), (895, 24), (10403, 32), (895, 64)):
        m, field, _ = GRID["CHECK_PAIR"](n, 2)
        points = [(a, b) for a in range(-height, height+1) for b in range(1, height+1)
                  if gcd(a, b) == 1 and gcd(a-b*m, n) == 1]
        d, elements = marked_elements(field, points)
        start = perf_counter()
        basis, eligible, core = away_basis(field, points, height)
        scalars = descent_scalars(d, elements, basis)
        reduced = supported_scalars(d, scalars)
        fast = solve_descent(d, elements, basis, reduced)
        elapsed = perf_counter()-start
        baseline = "-"
        if height <= 32:
            assert [mask for mask, _ in fast] == descent_masks(d, basis, scalars)
            start = perf_counter()
            slow = QUADRATIC["square_kernel"](d, elements)
            baseline = f"{perf_counter()-start:.3f}"
            masks = [mask for mask, _ in fast+slow]
            rank = len(masks)-len(GRID["eliminate"](masks, (1 << j for j in range(len(masks)))))
            assert rank == len(fast) == len(slow)
        bit_lengths = [sum(abs(s.numerator).bit_length()+s.denominator.bit_length() for s in group)
                       for group in (scalars, reduced)]
        print(n, height, len(points), eligible, core, len(basis), len(fast),
              f"{bit_lengths[0]}/{bit_lengths[1]}", f"{baseline}/{elapsed:.3f}", flush=True)


if __name__ == "__main__":
    replay()
