"""Compare the full primitive-grid kernels with and without the ramified row at two."""

from math import gcd
from pathlib import Path
from runpy import run_path

HERE = Path(__file__).resolve().parent
GRID = run_path(str(HERE / "cogentic-monic-large-primes.py"))
REPAIR = run_path(str(HERE / "cogentic-monic-index.py"))["repair"]
PLANT = run_path(str(HERE / "cogentic-planted-norm-two.py"))["monic_plants"]
HEIGHT = GRID["HEIGHT"]
CUTOFF = max(GRID["BASE"], 2*HEIGHT**2)
PRIMES = tuple(GRID["primes_through"](CUTOFF))
TWO_ROWS = [(1, 2, 0), (2, 2, 0)]

PARI = r'''
check_ramified_grid(coeffs, points, expected, cutoff) = {
  my(polys=apply(Polrev,coeffs), checks=0, excluded=prod(i=1,2,poldisc(polys[i])));
  excluded/=2^valuation(excluded,2);
  for(i=1,2,
    my(P=polys[i], nf=nfinit(P), two=idealprimedec(nf,2));
    if(poldisc(P)!=nf.disc*nf.index^2 || #two!=1 ||
       two[1].f!=1 || two[1].e!=poldegree(P) || idealval(nf,x,two[1])!=1,
       error("incorrect maximal-order decomposition at two"));
    for(k=1,#points,
      my(a=points[k][1], b=points[k][2], element=a-b*x, rows=List());
      my(value=nfeltnorm(nf,element));
      if(gcd(value,excluded)!=1, error("odd discriminant prime passed the filter"));
      if(idealval(nf,element,two[1])!=(a%2==0) || valuation(value,2)!=(a%2==0),
         error("wrong ramified valuation on a primitive mark"));
      my(ideals=idealfactor(nf,element));
      for(j=1,matsize(ideals)[1],
        my(pr=ideals[j,1], p=pr.p, exponent=ideals[j,2]);
        if(pr.f!=1 || (p!=2 && pr.e!=1) || gcd(b,p)!=1 || exponent!=valuation(value,p),
           error("wrong prime-ideal norm or exponent"));
        my(root=lift(Mod(a,p)/b));
        if(idealval(nf,x-root,pr)<=0, error("wrong residue root"));
        if(exponent%2,
          if(p>cutoff, error("odd prime-ideal valuation beyond the cutoff"));
          listput(rows,[i,p,root]);
        );
      );
      if(Set(Vec(rows))!=Set(select(row->row[1]==i,expected[k])),
         error("wrong complete ideal parity column"));
      checks++;
    );
  );
  checks;
};
'''


def kernel(relations):
    words = GRID["parity_words"]([small+large for _, small, large, _ in relations])
    basis = GRID["eliminate"](words, (1 << i for i in range(len(words))))
    assert all(GRID["combine"](mask, words) == 0 for mask in basis)
    return basis


def compare(family, n, m, fields, cuts=()):
    coeffs = [list(p) for p in fields]
    line, = GRID["gp"](f"print(prod(i=1,2,poldisc(Polrev({coeffs}[i]))));\n")
    excluded = int(line)
    assert excluded % 2 == 0
    args = (n, m, fields, excluded, PRIMES, CUTOFF)
    legacy = GRID["relations"](*args, complete_parity=True)
    ramified = GRID["relations"](*args, complete_parity=True, include_ramified_two=True)
    assert legacy == [entry for entry in ramified if entry[0][0] % 2]
    legacy_basis, ramified_basis = kernel(legacy), kernel(ramified)
    assert len(ramified_basis) >= len(legacy_basis)
    new_columns = [entry for entry in ramified if entry[0][0] % 2 == 0]
    assert all([row for row in small if row[1] == 2] == TWO_ROWS for _, small, _, _ in new_columns)
    for t in cuts:
        assert ((t, 1), TWO_ROWS, [], True) in new_columns
    assert len(ramified_basis)-len(legacy_basis) >= max(0, len(cuts)-1)

    points = [list(mark) for mark, _, _, _ in ramified]
    expected = [[list(row) for row in small+large] for _, small, large, _ in ramified]
    call = f"check_ramified_grid({coeffs},{points},{expected},{CUTOFF})"
    line, = GRID["gp"](PARI + f"iferr(print({call}),err,print(err);quit(1));\n", timeout=60)
    checks = int(line)
    assert checks == 2*len(ramified)
    return (n, family, len(cuts), len(legacy), len(legacy_basis),
            len(ramified), len(ramified_basis), checks)


def main():
    for fields, excluded in ((((4, 0, 1), (2, 0, 0, 1)), 8), (((2, 0, 1), (2, 0, 0, 1)), 0)):
        try:
            GRID["relations"](85, 3, fields, excluded, PRIMES, CUTOFF, include_ramified_two=True)
        except ValueError:
            pass
        else:
            raise AssertionError("accepted an invalid ramified row")

    print("N, family, planted cuts, legacy columns, legacy nullity, ramified columns, ramified nullity, PARI columns", flush=True)
    totals = []
    for n in (35, 77, 143, 221, 323, *GRID["INPUTS"]):
        m, f, g = GRID["CHECK_PAIR"](n, 3)
        totals.append(compare("raw", n, m, (f, g)))
        print(*totals[-1], flush=True)
    for n, degree in ((17, 2), (67, 2), (1787, 4), (391, 5), (247, 3)):
        m, f, g = GRID["CHECK_PAIR"](n, degree)
        shift, fields = REPAIR(n, m, f, g)
        assert shift or n == 247
        totals.append(compare("repaired", n, m, fields))
        print(*totals[-1], flush=True)
    for n, h in ((85, 4), (631, 4), (15629, 6), (5764807, 8)):
        m, cuts, f, g = PLANT(n, h)
        assert all(gcd(t-m, n) == 1 for t in cuts)
        totals.append(compare("planted", n, m, (f, g), cuts))
        print(*totals[-1], flush=True)
    print(f"Verified {sum(row[-1] for row in totals):,} field columns in PARI across {len(totals)} pairs")


if __name__ == "__main__":
    main()
