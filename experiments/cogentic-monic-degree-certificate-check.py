"""Verify the saved degree-grid certificates without running the search."""

import json
from math import gcd, prod
from pathlib import Path
from runpy import run_path


GP_CHECK = r"""
check_square(P, points, sign, m, n) = {
  if(!polisirreducible(P) || subst(P,x,m) != n, error("invalid defining polynomial"));
  my(D=deriv(P), derivative=subst(D,x,m));
  if(gcd(derivative,n) != 1, error("nonunit derivative"));
  my(K=nfinit(P), value=sign*prod(i=1,#points,Mod(points[i][1]-points[i][2]*x,P)), root);
  if(!nfeltissquare(K,value,&root), error("not a field square"));
  root=nfbasistoalg(K,root);
  if(root^2 != value, error("incorrect field root"));
  my(numerator=lift(D*root));
  if(denominator(numerator,1) != 1, error("derivative did not clear the denominator"));
  lift(Mod(subst(numerator,x,m),n)/derivative)
};
"""


def verify(certificate, pair, gp):
    n, m = certificate["n"], certificate["m"]
    degree, height = certificate["degree"], certificate["height"]
    assert degree == pair["scheduled_degree"](n) == 2
    assert height == 256 and certificate["shift"] == 0
    first, second = certificate["fields"]
    actual_m, actual_first, actual_second = pair["monic_pair"](n, degree)
    assert (m, first, second) == (actual_m, list(actual_first), list(actual_second))

    points = certificate["points"]
    sign = certificate["sign"]
    assert sign in (-1, 1) and len(set(map(tuple, points))) == len(points)
    assert all(abs(a) <= height and 1 <= b <= height and gcd(a, b) == 1
               and gcd(a-b*m, n) == 1 for a, b in points)
    result = gp(GP_CHECK + f"points={points};\n"
                + f"print([check_square(Polrev({first}),points,{sign},{m},{n}),"
                + f"check_square(Polrev({second}),points,{sign},{m},{n})]);\n")
    left, right = json.loads(result[0])
    square = sign * prod(a-b*m for a, b in points) % n
    assert left**2 % n == right**2 % n == square == certificate["square"]
    saved_left, saved_right = certificate["residues"]
    assert all(saved in (root, (-root) % n)
               for saved, root in ((saved_left, left), (saved_right, right)))
    divisor = gcd(saved_left-saved_right, n)
    assert 1 < divisor < n and divisor == certificate["divisor"]
    assert divisor * certificate["cofactor"] == n
    assert sorted((gcd(left-right, n), gcd(left+right, n))) == sorted((divisor, n//divisor))
    print(f"{n} = {divisor} * {n//divisor} verified with {len(points)} marks")


def main():
    directory = Path(__file__).resolve().parent
    pair = run_path(str(directory / "cogentic-monic-pair.py"))
    gp = run_path(str(directory / "cogentic-monic-large-primes.py"))["gp"]
    certificates = json.loads((directory / "cogentic-monic-degree-certificates.json").read_text())
    assert [certificate["n"] for certificate in certificates] == [824552227, 647911657]
    for certificate in certificates:
        verify(certificate, pair, gp)


if __name__ == "__main__":
    main()
