\\ Finite ideal checks for the manual cubic/quartic fixtures.

monic_norm_data(F, a, b, excluded, primeset) = {
  my(e = poldegree(F), value = sum(i=0,e,polcoef(F,i)*a^i*b^(e-i)));
  if(!value || gcd(value,excluded)!=1, return(0));
  my(factors = smooth_factors(abs(value),primeset));
  if(type(factors)!="t_VEC", return(0));
  my(entries = vector(#factors,i,
    my(p = factors[i][1], v = factors[i][2]);
    if(gcd(b,p)!=1 || valuation(value,p)!=v, error("bad rational valuation"));
    my(root = lift(Mod(a,p)/b));
    if(subst(F,x,root)%p || subst(deriv(F),x,root)%p==0, error("bad degree-one root"));
    [p,v,root]));
  if(prod(i=1,#entries,entries[i][1]^entries[i][2])!=abs(value), error("incomplete factorization"));
  [value,entries];
}

monic_check_ideals(nf, a, b, data) = {
  my(element = a-b*x, entries = data[2]);
  if(nfeltnorm(nf,element)!=data[1], error("incorrect homogeneous norm"));
  my(ideals = idealfactor(nf,element));
  if(matsize(ideals)[1]!=#entries, error("incorrect number of prime ideals"));
  for(i=1,#entries,
    my(p = entries[i][1], v = entries[i][2], root = entries[i][3]);
    my(matches = sum(j=1,#entries,
      my(pr = ideals[j,1]);
      pr.p==p && pr.f==1 && pr.e==1 && ideals[j,2]==v && idealval(nf,x-root,pr)>0));
    if(matches!=1, error("incorrect prime-ideal valuation or residue"));
  );
}

monic_relation_replay(n,m,coefficients) = {
  my(fields = apply(Polrev,coefficients), orders = apply(nfinit,fields));
  my(discs = apply(poldisc,fields), primeset = primes([2,97]));
  for(i=1,2,
    if(discs[i]!=orders[i].disc*orders[i].index^2, error("discriminant/index mismatch"));
  );
  my(excluded = discs[1]*discs[2], count = 0, witness = []);
  for(a=-12,12,for(b=1,12,
    if(gcd(a,b)!=1 || gcd(a-b*m,n)!=1, next);
    my(left = monic_norm_data(fields[1],a,b,excluded,primeset));
    my(right = monic_norm_data(fields[2],a,b,excluded,primeset));
    if(type(left)!="t_VEC" || type(right)!="t_VEC", next);
    monic_check_ideals(orders[1],a,b,left);
    monic_check_ideals(orders[2],a,b,right);
    count++;
    if(!#witness, witness=[a,b,left,right]);
  ));
  if(!count, error("no simultaneous smooth marks for ",n));
  [n,m,discs,count,witness];
}
