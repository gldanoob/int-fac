"""Find every quadratic-field square dependency by two rational squareclass kernels."""

from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt
from pathlib import Path
from runpy import run_path


GRID = run_path(str(Path(__file__).with_name("cogentic-monic-large-primes.py")))


def rational_sqrt(value):
    value = Fraction(value)
    if value < 0:
        return None
    a, b = isqrt(value.numerator), isqrt(value.denominator)
    if a*a == value.numerator and b*b == value.denominator:
        return Fraction(a, b)
    return None


def rational_words(values):
    """Give exact binary squareclass columns for an explicit nonzero rational list."""
    values = [Fraction(value) for value in values]
    integers = [value.numerator*value.denominator for value in values]
    if not all(integers):
        raise ValueError("rational squareclasses require nonzero inputs")
    atoms = {abs(value) for value in integers} - {1}
    while True:
        for a, b in combinations(sorted(atoms), 2):
            common = gcd(a, b)
            if common != 1:
                atoms.difference_update((a, b))
                atoms.update((common, a//common, b//common))
                atoms.discard(1)
                break
        else:
            break
    rows = [(a, 0 if isqrt(a)**2 == a else 1 << j) for j, a in enumerate(sorted(atoms), 1)]
    words = []
    for value in integers:
        word, remaining = int(value < 0), abs(value)
        for atom, bit in rows:
            while remaining % atom == 0:
                remaining //= atom
                word ^= bit
        assert remaining == 1
        words.append(word)
    return words


def multiply(d, left, right):
    a, b = left
    c, e = right
    return a*c+d*b*e, a*e+b*c


def norm(d, value):
    a, b = value
    return a*a-d*b*b


def masked_product(d, elements, mask):
    result = (Fraction(1), Fraction(0))
    for k in GRID["support"](mask):
        result = multiply(d, result, elements[k])
    return result


def descent(d, value):
    a, b = value
    t = rational_sqrt(norm(d, value))
    if t is None:
        return None
    if not a+t:
        t = -t
    return 2*(a+t), (a+t, b)


def square_root(d, value):
    """Return an exact root in Q(sqrt(d)), or None, for a nonsquare radicand d."""
    d, value = Fraction(d), tuple(map(Fraction, value))
    if not any(value):
        return value
    descended = descent(d, value)
    if descended is None:
        return None
    scalar, (a, b) = descended
    root = rational_sqrt(scalar)
    if root is not None:
        return a/root, b/root
    root = rational_sqrt(scalar/d)
    if root is not None:
        return b/root, a/(d*root)
    return None


def square_masks(d, elements):
    """Return original masks spanning all square dependencies."""
    d = Fraction(d)
    elements = [tuple(map(Fraction, value)) for value in elements]
    if not d or rational_sqrt(d) is not None or any(not any(value) for value in elements):
        raise ValueError("expected a nonsquare radicand and nonzero field elements")
    norm_words = rational_words(norm(d, value) for value in elements)
    norm_basis = GRID["eliminate"](norm_words, (1 << k for k in range(len(elements))))
    scalars = [descent(d, masked_product(d, elements, mask))[0] for mask in norm_basis]
    return GRID["eliminate"](rational_words([*scalars, d]), [*norm_basis, 0])


def square_kernel(d, elements):
    """Return (original mask, exact root) pairs for a basis of square dependencies."""
    d = Fraction(d)
    elements = [tuple(map(Fraction, value)) for value in elements]
    result = []
    for mask in square_masks(d, elements):
        product = masked_product(d, elements, mask)
        root = square_root(d, product)
        assert root is not None and multiply(d, root, root) == product
        result.append((mask, root))
    return result


def exhaustive_gp(d, elements, expected):
    d = Fraction(d)
    pairs = [f"[{Fraction(a)},{Fraction(b)/d.denominator}]" for a, b in elements]
    gp = r'''
check_square_subsets(d, pairs, expected) = {
  my(P=x^2-d, nf=nfinit(P), elements=apply(pair->Mod(pair[1]+pair[2]*x,P),pairs));
  for(mask=0,#expected-1,
    my(value=prod(j=1,#elements,if(bittest(mask,j-1),elements[j],1)));
    if(nfeltissquare(nf,value)!=expected[mask+1],error("wrong square kernel mask ",mask));
  );
  #expected;
};
'''
    call = f"check_square_subsets({d.numerator*d.denominator},[{','.join(pairs)}],{expected})"
    line, = GRID["gp"](gp + f"iferr(print({call}),err,print(err);quit(1));\n")
    assert int(line) == len(expected)


def replay():
    values = ((-1, 0), (6, 0), (-3, 0), (0, 1), (1, 1), (2, 1), (3, 2),
              (1, -1), (-3, -2), (Fraction(3, 2), Fraction(5, 7)), (Fraction(25, 18), 0))
    checks = 0
    for d in (2, 18, -1, -5, -20, Fraction(3, 2), Fraction(-3, 2)):
        basis = square_kernel(d, values)
        span = {0}
        for mask, _ in basis:
            assert mask not in span
            span.update(old ^ mask for old in tuple(span))
        expected = [int(mask in span) for mask in range(1 << len(values))]
        exhaustive_gp(d, values, expected)
        checks += len(expected)
        print(f"D={d} square nullity {len(basis)}")

    # The shared opaque factor is never resolved into primes.
    shared = ((1 << 127)-1)*((1 << 107)-1)
    left, right = shared*((1 << 61)-1), shared*((1 << 89)-1)
    first, second, quotient, square = rational_words([left, right, Fraction(left, right), shared**2])
    assert first and second and first != second and first ^ second == quotient and square == 0
    assert square_root(-5, (2, 1)) is None and square_root(-1, (-1, 0)) == (0, 1)
    assert not square_kernel(-1, [])
    for d, values in ((4, [(1, 1)]), (0, [(1, 1)]), (-1, [(0, 0)])):
        try:
            square_kernel(d, values)
        except ValueError:
            pass
        else:
            raise AssertionError((d, values))
    print(f"Verified {checks:,} subset products against PARI")


if __name__ == "__main__":
    replay()
