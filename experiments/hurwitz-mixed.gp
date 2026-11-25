\\ Reconstruct R-n from residues of the positive three-square count.
\\ The callback supplies a residue modulo r. Only the fixture sees the exact count.
mixedHurwitzDifference(n, base, countResidue) = {
  my(value = 0, modulus = 1, r = 2);
  while(modulus < n,
    r = nextprime(r+1);
    if(base%r == 0, next);
    my(residue = lift(Mod(countResidue(r),r)/base - n));
    my(digit = lift(Mod(residue-value,r)/modulus));
    value += modulus*digit;
    modulus *= r
  );
  value
};

\\ Return the sorted prime factors with multiplicity. The supplied routine
\\ countResidue(ell,n,r) evaluates the positive three-square count modulo r.
factorHurwitzModPrimes(N, countResidue) = {
  if(type(N) != "t_INT" || N < 2, error("expected an integer at least two"));
  my(factors = List(), pending = List(), bits = logint(N,2)+1);
  forprime(p=2,8*bits,
    while(N%p == 0, listput(factors,p); N /= p)
  );
  if(N > 1, listput(pending,N));
  while(#pending,
    my(n = pending[#pending], root, e, ell = 3, d = 1);
    listpop(pending);
    if(isprime(n), listput(factors,n); next);
    e = ispower(n,,&root);
    if(e, for(i=1,e,listput(pending,root)); next);
    while(d == 1 || d == n,
      if(isprime(ell),
        d = gcd(n,ell);
        if(d == 1,
          my(base = 3*qfbhclassno(ell));
          my(delta = mixedHurwitzDifference(n,base,r->countResidue(ell,n,r)));
          d = gcd(n,delta)
        )
      );
      ell += 8
    );
    listput(pending,d);
    listput(pending,n/d)
  );
  vecsort(Vec(factors))
};

checkMixedHurwitz() = {
  my(checked = 0, mixed = 0, overlaps = 0, skippedBase = 0);
  foreach([257*263, 257*263*269, 1009^2*1013^3, 1019*1021*1031, 4001^2*4003*4007], n,
    my(factors = factor(n)[,1], bits = logint(n,2)+1, found = 0);
    if(vecmin(factors) <= 8*bits, error("small-prime preprocessing fixture"));
    forprime(ell=3,199,
      if(ell%8!=3 || n%ell==0, next);
      my(base = 3*qfbhclassno(ell), count = 3*qfbhclassno(ell*n^2));
      my(delta = mixedHurwitzDifference(n,base,r->count%r));
      if(delta != count/base-n || delta < 0 || delta >= n, error("CRT difference at ",[n,ell]));
      my(d = gcd(n,delta), splitPart = 1);
      foreach(factors,p, if(kronecker(-ell,p)==1, splitPart *= p^valuation(n,p)));
      if(splitPart > 1 && splitPart < n,
        if(d <= 1 || d >= n || d%splitPart, error("mixed gcd at ",[n,ell]));
        if(d != splitPart, overlaps++);
        found = 1;
        mixed++
      );
      if(base%3==0, skippedBase++);
      checked++
    );
    if(!found, error("no mixed twist for ",n))
  );
  if(!overlaps || !skippedBase, error("missing cross-divisibility or skipped CRT prime"));
  my(oracle = (ell,n,r)->(3*qfbhclassno(ell*n^2))%r);
  foreach([[2],[2,2,3,5],[1009,1009,1009],[1009,1009,1013,1013,1013],[1019,1021,1031]], expected,
    if(factorHurwitzModPrimes(vecprod(expected),oracle) != expected, error("complete CRT factorization at ",expected))
  );
  [checked,mixed,overlaps,skippedBase]
};
