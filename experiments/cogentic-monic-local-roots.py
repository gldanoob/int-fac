"""Check mark-local odd-prime labels and complete parity against PARI."""

from ast import literal_eval
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).resolve().parent
GRID = run_path(str(HERE / "cogentic-monic-large-primes.py"))
REPAIR = run_path(str(HERE / "cogentic-monic-index.py"))["repair"]
PLANT = run_path(str(HERE / "cogentic-planted-norm-two.py"))["monic_plants"]
CUTOFF = max(GRID["BASE"], 2*GRID["HEIGHT"]**2)

PARI = r'''
local_root_check(coeffs, points, expected, cutoff) = {
  my(polys=apply(Polrev,coeffs), excluded=prod(i=1,2,poldisc(polys[i])));
  my(labels=Map(), pivots=Map(), words=vector(#points), rank=0, checks=0);
  my(simple_bad=0, once_bad=0, tail_bad=0);
  for(i=1,2,
    my(P=polys[i], D=deriv(P), nf=nfinit(P));
    for(k=1,#points,
      my(a=points[k][1], b=points[k][2], element=a-b*x, rows=List());
      my(value=nfeltnorm(nf,element), ideals=idealfactor(nf,element));
      if(value!=sum(j=0,poldegree(P),polcoef(P,j)*a^j*b^(poldegree(P)-j)), error("wrong norm"));
      for(j=1,matsize(ideals)[1],
        my(pr=ideals[j,1], p=pr.p, exponent=ideals[j,2], label);
        if(gcd(b,p)!=1 || pr.f!=1 || exponent!=valuation(value,p), error("wrong residue degree or valuation"));
        my(root=lift(Mod(a,p)/b), simple=subst(D,x,root)%p!=0);
        if(idealval(nf,x-root,pr)<=0, error("wrong residue root"));
        if(simple && pr.e!=1 || !simple && exponent!=1, error("wrong local prime-ideal type"));
        if(p==2 && (pr.e!=poldegree(P) || root!=0 || exponent!=1), error("wrong dyadic row"));
        if(p>cutoff && (!simple || exponent%2), error("tail contributed unresolved ideal parity"));
        if(p>2 && excluded%p==0,
          if(simple, simple_bad++; if(p>cutoff, tail_bad++), once_bad++));
        if(exponent%2,
          my(key=[i,p,root]);
          listput(rows,key);
          if(!mapisdefined(labels,key,&label), label=#labels; mapput(labels,key,label));
          words[k]=bitor(words[k],2^label);
        );
      );
      if(Set(Vec(rows))!=Set(select(row->row[1]==i,expected[k])), error("wrong parity column"));
      checks++;
    );
  );
  for(k=1,#words,
    my(word=words[k]);
    while(word,
      my(pivot=logint(word,2), previous);
      if(mapisdefined(pivots,pivot,&previous), word=bitxor(word,previous),
        mapput(pivots,pivot,word); rank++; break);
    );
  );
  [#points-rank,checks,simple_bad,once_bad,tail_bad];
};

check_unsafe_tail(coeffs,p) = {
  my(P=Polrev(coeffs), nf=nfinit(P), ideals=idealfactor(nf,x), odd=0);
  if(valuation(nfeltnorm(nf,x),p)!=2, error("wrong rational tail exponent"));
  for(j=1,matsize(ideals)[1],
    my(pr=ideals[j,1]);
    if(pr.p==p,
      if(pr.f!=1 || ideals[j,2]!=1 || idealval(nf,x,pr)!=1, error("wrong tail branch"));
      odd++;
    );
  );
  if(odd!=2, error("unresolved square tail did not have two odd ideal valuations"));
  1;
};
'''


def nullity(marks):
    words = GRID["parity_words"]([small + large for _, small, large, _ in marks])
    basis = GRID["eliminate"](words, (1 << i for i in range(len(words))))
    assert all(GRID["combine"](mask, words) == 0 for mask in basis)
    return len(basis)


def compare(family, n, m, fields, *, cutoff=CUTOFF, height=GRID["HEIGHT"]):
    coeffs = [list(p) for p in fields]
    line, = GRID["gp"](f"print(prod(i=1,2,poldisc(Polrev({coeffs}[i]))));\n")
    primes = tuple(GRID["primes_through"](cutoff))
    args = (n, m, fields, int(line), primes, cutoff)
    options = dict(complete_parity=True, height=height, include_ramified_two=True)
    old = GRID["relations"](*args, **options)
    new = GRID["relations"](*args, **options, mark_local=True)
    new_by_mark = {entry[0]: entry for entry in new}
    assert all(new_by_mark[entry[0]] == entry for entry in old)
    without_two = GRID["relations"](*args, complete_parity=True, height=height, mark_local=True)
    assert without_two == [entry for entry in new if entry[0][0] % 2]
    old_nullity, new_nullity = nullity(old), nullity(new)
    assert old_nullity <= new_nullity

    points = [list(mark) for mark, _, _, _ in new]
    expected = [[list(row) for row in small + large] for _, small, large, _ in new]
    call = f"local_root_check({coeffs},{points},{expected},{cutoff})"
    line, = GRID["gp"](PARI + f"iferr(print({call}),err,print(err);quit(1));\n", timeout=60)
    gp_nullity, checks, simple, once, tail = literal_eval(line)
    assert gp_nullity == new_nullity and checks == 2*len(new)
    print(n, family, len(old), old_nullity, len(new), new_nullity, simple, once, tail, flush=True)
    return new_by_mark, checks


def run():
    print("N, family, old columns, old nullity, local columns, local nullity,"
          " simple at global bad prime, valuation-one multiple roots, simple bad tail", flush=True)
    checks = 0
    for n in (35, 77, 143, 221, 323, *GRID["INPUTS"]):
        m, f, g = GRID["CHECK_PAIR"](n, 3)
        checks += compare("raw", n, m, (f, g))[1]
    for n, degree in ((17, 2), (67, 2), (1787, 4), (391, 5), (247, 3)):
        m, f, g = GRID["CHECK_PAIR"](n, degree)
        _, fields = REPAIR(n, m, f, g)
        checks += compare("repaired", n, m, fields)[1]
    for n, degree in ((85, 4), (631, 4), (15629, 6), (5764807, 8)):
        m, _, f, g = PLANT(n, degree)
        checks += compare("planted", n, m, (f, g))[1]

    m, p = 3, 8209
    assert p > CUTOFF and p in GRID["primes_through"](p)
    for name, f in (("simple-tail", (2*p*p, p+1, -2, 1)),
                    ("multiple-tail", (2*p*p, 2*p, 2, 1)),
                    ("multiple-once", (10, 10, 2, 1))):
        g = f[:-1] + (1-m, 1)
        n = GRID["homogeneous"](f, m, 1)
        marks, count = compare(name, n, m, (f, g), height=1)
        checks += count
        if name == "simple-tail":
            assert marks[0, 1] == ((0, 1), [(1, 2, 0), (2, 2, 0)], [], False)
        elif name == "multiple-tail":
            assert (0, 1) not in marks
            marks, count = compare("multiple-explicit", n, m, (f, g), cutoff=p, height=1)
            assert (0, 1) not in marks
            checks += count
            line, = GRID["gp"](PARI + f"iferr(print(check_unsafe_tail({list(f)},{p})),err,print(err);quit(1));\n")
            assert line == "1"
        else:
            assert marks[0, 1] == ((0, 1), [(1, 2, 0), (1, 5, 0), (2, 2, 0), (2, 5, 0)], [], True)
    print(f"Verified exact parity and nullity on {checks:,} field columns in PARI")


if __name__ == "__main__":
    run()
