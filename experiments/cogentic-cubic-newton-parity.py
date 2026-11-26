"""Test cubic principal-ideal parity over a composite residual by Newton slopes."""

from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt
from pathlib import Path
from runpy import run_path


GRID = run_path(str(Path(__file__).with_name("cogentic-monic-large-primes.py")))


def mark_polynomial(field, a, b):
    w, v, u, leading = field
    if leading != 1 or not b:
        raise ValueError("expected a monic cubic and a nonconstant mark")
    return (-a**3-u*a*a*b-v*a*b*b-w*b**3, 3*a*a+2*u*a*b+v*b*b, -3*a-u*b, 1)


def discriminant(coefficients):
    c, b, a, leading = coefficients
    if leading != 1 or not c:
        raise ValueError("expected a nonzero generator of a monic cubic algebra")
    disc = a*a*b*b-4*b**3-4*a**3*c-27*c*c+18*a*b*c
    if not disc:
        raise ValueError("expected a separable cubic")
    return disc


def valuation(value, base):
    if not value:
        return None
    exponent = 0
    while value % base == 0:
        value //= base
        exponent += 1
    return exponent


def slope_groups(exponents):
    hull = []
    for i, val in enumerate(exponents):
        if val is None:
            continue
        while len(hull) >= 2:
            j, old = hull[-1]
            k, previous = hull[-2]
            if (old-previous)*(i-j) < (val-old)*(j-k):
                break
            hull.pop()
        hull.append((i, val))
    return [(b-a, Fraction(h-k, b-a)) for (a, h), (b, k) in zip(hull, hull[1:])]


def named_even(coefficients, prime):
    """Exact local test, given a rational prime and a separable monic cubic."""
    if prime < 2:
        raise ValueError("expected a rational prime")
    disc = discriminant(coefficients)
    groups = slope_groups([valuation(value, prime) for value in coefficients])
    for length, slope in groups:
        if length != 2:
            if slope.numerator % 2:
                return False
            continue
        if slope.denominator == 2:
            return False
        if slope.numerator % 2:
            exponent = valuation(disc, prime)
            if exponent % 2 == 0 and (prime != 2 or (disc >> exponent) % 4 != 3):
                return False
    return True


def coprime_atoms(values):
    atoms = {abs(v) for v in values if abs(v) > 1}
    while True:
        for a, b in combinations(sorted(atoms), 2):
            common = gcd(a, b)
            if common == 1:
                continue
            atoms.difference_update((a, b))
            atoms.update((common, a//common, b//common))
            atoms.discard(1)
            break
        else:
            return sorted(atoms)


def odd_residual_even(coefficients, residual):
    """Test every prime ideal above the primes of an unfactored odd norm divisor."""
    disc = discriminant(coefficients)
    if residual < 1 or residual % 2 == 0 or coefficients[0] % residual:
        raise ValueError("expected a positive odd divisor of the absolute norm")
    if residual == 1:
        return True
    for atom in coprime_atoms([residual, disc, *coefficients]):
        if residual % atom:
            continue
        groups = slope_groups([valuation(value, atom) for value in coefficients])
        exponent = valuation(disc, atom)
        root = isqrt(atom)
        for length, slope in groups:
            if length == 2 and slope.denominator == 2:
                if root*root != atom or isqrt(root)**2 != root:
                    return False
            elif slope.numerator % 2 and (length != 2 or exponent % 2 == 0):
                if root*root != atom:
                    return False
    return True


def ideal_even(coefficients):
    norm = abs(coefficients[0])
    if not norm:
        raise ValueError("expected nonzero norm")
    if norm % 2 == 0 and not named_even(coefficients, 2):
        return False
    return odd_residual_even(coefficients, norm >> valuation(norm, 2))


def verify(field, fixtures):
    rows = []
    for a, b, residual in fixtures:
        coefficients = mark_polynomial(field, a, b)
        rows.append([a, b, residual, list(coefficients), int(odd_residual_even(coefficients, residual)),
                     int(ideal_even(coefficients)), int(named_even(coefficients, 2))])
    setup = r'''
newton_verify(c, rows) = {
  my(P=Polrev(c), nf=nfinit(P));
  for(k=1,#rows,
    my(row=rows[k], z=Mod(row[1]-row[2]*x,P), residual=row[3]);
    if(charpoly(z,y)!=Polrev(row[4],y),error("wrong marked characteristic polynomial"));
    my(ids=idealfactor(nf,z), all_even=1, odd_even=1, two_even=1);
    for(j=1,matsize(ids)[1],
      if(ids[j,2]%2,
        all_even=0;
        if(residual%ids[j,1].p==0,odd_even=0);
        if(ids[j,1].p==2,two_even=0);
      );
    );
    if([odd_even,all_even,two_even]!=row[5..7],error("different Newton ideal parity ",row));
  );
  #rows;
};
'''
    line, = GRID["gp"](setup + f"iferr(print(newton_verify({list(field)},{rows})),err,print(err);quit(1));\n")
    assert int(line) == len(fixtures)


def replay():
    checks = 0
    for field in ((54, 0, -28, 1), (-12, -8, -5, 1), (-12, -6, -3, 1), (-2, 0, 0, 1)):
        y = 2*12**2
        primes = tuple(GRID["primes_through"](y))
        fixtures = []
        for a in range(-12, 13):
            for b in range(1, 13):
                coefficients = mark_polynomial(field, a, b)
                norm = abs(coefficients[0])
                residual = norm
                for p in primes:
                    power = p**valuation(residual, p)
                    residual //= power
                    if 2 < p <= 11 and power > 1:
                        assert named_even(coefficients, p) == odd_residual_even(coefficients, power)
                        fixtures.append((a, b, power))
                fixtures.append((a, b, residual))
        verify(field, fixtures)
        checks += len(fixtures)

    for field, expected in (((-12, -12, -9, 1), False), ((28, -16, -9, 1), True),
                            ((-4, -16, -9, 1), False), ((-4, -12, -9, 1), True)):
        assert named_even(mark_polynomial(field, 0, 1), 2) == expected
        verify(field, [(0, 1, 1)])
        checks += 1

    for q in (247, 247**2, 247**3, 247**4, 13**4*19**2):
        field = (2*q, 0, 2, 1)
        assert odd_residual_even(mark_polynomial(field, 0, 1), q) == (q == 247**4)
        verify(field, [(0, 1, q)])
        checks += 1

    for s in (13*19**2, (13*19**2)**2):
        field = (2*s*s, 2*s, 2, 1)
        assert odd_residual_even(mark_polynomial(field, 0, 1), s*s) == (s % 13**2 == 0)
        verify(field, [(0, 1, s*s)])
        checks += 1
    field = (2*5**2*(1+2*5), 4*5, 2, 1)
    assert odd_residual_even(mark_polynomial(field, 0, 1), 5**2)
    verify(field, [(0, 1, 5**2)])
    atom = ((1 << 61)-1)*((1 << 89)-1)
    for exponent in (2, 4):
        tail = atom**exponent
        field = (2*tail, 0, 2, 1)
        assert odd_residual_even(mark_polynomial(field, 0, 1), tail) == (exponent == 4)
    print(f"Verified cubic Newton ideal parity with PARI on {checks+1:,} marked elements")


if __name__ == "__main__":
    replay()
