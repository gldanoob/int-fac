\\ Reconstruct R-n from residues of the positive three-square count.
\\ The callback supplies a residue modulo r. Only the fixture sees the exact count.
mixedHurwitzDifference(n, base, countResidue, {skipPrime=0}) = {
  my(value = 0, modulus = 1, r = 2);
  while(modulus < n,
    r = nextprime(r+1);
    if(r == skipPrime || base%r == 0, next);
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
          my(delta = mixedHurwitzDifference(n,base,r->countResidue(ell,n,r),ell));
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

\\ Recover a residue from one bit per padded conductor. A prime s = 1 mod 2*ell
\\ splits at -ell, so its local factor scales the count by s even if s divides n.
hurwitzResidueFromBits(ell,n,r,bitAnswer) = {
  if(r == ell || r == 2 || !isprime(r), error("expected an odd prime distinct from the twist"));
  my(k = logint(r,2)+1, prefix = 0, step = 2*ell*r);
  for(j=1,k,
    my(s = lift(chinese(Mod(1,2*ell),Mod(2^j,r))));
    if(s != 1, while(!isprime(s), s += step));
    my(bit = bitAnswer(ell,n*s,r));
    if(bit != 0 && bit != 1, error("expected a remainder-parity bit"));
    prefix = 2*prefix + bit
  );
  ceil(r*prefix/2^k)
};

factorHurwitzRemainderBits(N,bitAnswer) = {
  factorHurwitzModPrimes(N,(ell,n,r)->hurwitzResidueFromBits(ell,n,r,bitAnswer))
};

checkHurwitzRemainderBits() = {
  my(count = 0, zeros = 0, bitAnswer = (ell,n,r)->((3*qfbhclassno(ell*n^2))%r)%2);
  foreach([3,11,19],ell,
    forstep(n=1,61,2,
      if(n%ell == 0,next);
      forprime(r=3,23,
        if(r == ell,next);
        my(expected = (3*qfbhclassno(ell*n^2))%r);
        if(hurwitzResidueFromBits(ell,n,r,bitAnswer) != expected, error("remainder bits at ",[ell,n,r]));
        count++;
        if(expected == 0,zeros++)
      )
    )
  );
  foreach([[1009,1009,1013,1013,1013],[1019,1021,1031]], primes,
    if(factorHurwitzRemainderBits(vecprod(primes),bitAnswer) != primes, error("one-bit factorization at ",primes))
  );
  if(!zeros,error("missing zero residue"));
  [count,zeros]
};

checkHurwitzSquareComparison() = {
  my(checked = 0, imprimitive = 0);
  forstep(n=3,43,2,
    my(squares = Set(vector(n,i,(i-1)^2%n)));
    for(a=1,n-1,
      if(gcd(a,n)!=1,next);
      my(d=lift(chinese(Mod(3,8),Mod(-a,n))));
      my(equal=(qfbhclassno(d*n^2) == n*qfbhclassno(d)));
      if(equal != (setsearch(squares,a)!=0), error("square comparison at ",[n,a,d]));
      checked++;
      if(!issquarefree(d),imprimitive++)
    )
  );
  [checked,imprimitive]
};
