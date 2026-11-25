\\ Two imaginary quadratic fields and a common evaluation point modulo n.
\\ Each certificate is produced from the smooth norms and exact integer rows.

smooth_factors(value, primeset) = {
  my(factors = List());
  for(i = 1, #primeset,
    my(p = primeset[i], v = valuation(value, p));
    if(v, listput(factors, [p,v]); value /= p^v);
    if(value == 1, return(Vec(factors)));
  );
  0;
}

certificate_split(n, base, exponent) = {
  if(exponent <= 0 || Mod(base,n)^exponent != 1, error("invalid exponent"));
  my(v = valuation(exponent,2), residue = Mod(base,n)^(exponent/2^v));
  for(i = 0, v,
    my(divisor = gcd(lift(residue) - 1, n));
    if(divisor > 1 && divisor < n, return(divisor));
    residue = residue^2;
  );
  1;
}

norm_entries(a,b,idx,slopes,constants,excluded,primeset) = {
  my(value = a^2 + slopes[idx]*a*b + constants[idx]*b^2);
  if(gcd(value,excluded[idx]) != 1, return(0));
  my(factors = smooth_factors(value,primeset));
  if(type(factors) != "t_VEC", return(0));
  vector(#factors,j,
    my(p = factors[j][1], root = lift(Mod(a,p)/b));
    [[idx,p,root], factors[j][2]]);
}

quadratic_certificate(n, slopes, height, bound, {join_residues=0}) = {
  my(m = sqrtint(n), primeset = primes([2,bound]));
  my(constants = vector(2,i,n - m^2 - slopes[i]*m));
  my(discs = vector(2,i,slopes[i]^2 - 4*constants[i]));
  if(vecmax(discs) >= 0, return([]));
  my(excluded = vector(2,i,prod(j=1,#primeset,
    if(discs[i] % (primeset[j]^2) == 0, primeset[j], 1))));
  my(columns = List(), seen = Map(), rows = Map(), rowcount = 0);
  for(a = 1, height, for(b = -height, height,
    if(b == 0 || gcd(a,b) != 1, next);
    my(label = lift(Mod(a-b*m,n)));
    if(gcd(label,n) != 1, next);
    my(left = norm_entries(a,b,1,slopes,constants,excluded,primeset));
    if(!join_residues && type(left) != "t_VEC", next);
    my(right = norm_entries(a,b,2,slopes,constants,excluded,primeset));
    if(!join_residues,
      if(type(right) == "t_VEC",listput(columns, concat(left,right))),
      \\ One reference per residue spans all differences in that residue class.
      label = min(label,n-label);
      for(i = 1, 2,
        my(entry = if(i==1,left,right));
        if(type(entry) != "t_VEC", next);
        my(reference);
        if(mapisdefined(seen,label,&reference),
          listput(columns,concat(entry,vector(#reference,k,[reference[k][1],-reference[k][2]]))),
          mapput(seen,label,entry));
      );
    );
  ));
  for(i = 1, #columns,
    my(col = columns[i]);
    for(j = 1, #col,
      my(key = col[j][1]);
      if(!mapisdefined(rows,key), rowcount++; mapput(rows,key,rowcount));
    );
  );
  if(!rowcount, return([]));
  my(M = matrix(rowcount,#columns));
  for(j = 1, #columns,
    my(col = columns[j]);
    for(k = 1, #col, M[mapget(rows,col[k][1]),j] += col[k][2]);
  );
  my(piv = matindexrank(M), pr = piv[1], pc = piv[2]);
  my(basis = vecextract(M,[1..rowcount],pc), inverse = vecextract(M,pr,pc)^-1);
  for(j = 1, #primeset,
    my(base = primeset[j], rhs = vector(rowcount)~, present = 1);
    if(base <= 2 || gcd(base,n*discs[1]) != 1, next);
    my(roots = polrootsmod(x^2 + slopes[1]*x + constants[1],base));
    if(#roots != 2, next);
    for(k = 1, 2,
      my(key = [1,base,lift(roots[k])]);
      if(!mapisdefined(rows,key), present = 0; break);
      rhs[mapget(rows,key)] = 1;
    );
    if(!present, next);
    my(sol = inverse * vecextract(rhs,pr));
    if(basis*sol != rhs, next);
    my(den = denominator(sol), exponent = 12*den);
    if(basis*(den*sol) != den*rhs, error("integral relation"));
    my(divisor = certificate_split(n,base,exponent));
    if(divisor > 1, return([base,exponent,divisor,#columns,#pc]));
  );
  [];
}

probe(n, height, bound, {join_residues=0}) = {
  for(i = 0, 2, for(j = i+1, 3,
    my(cert = quadratic_certificate(n,[-i,-j],height,bound,join_residues));
    if(#cert, return(concat([-i,-j],cert)));
  ));
  [];
}

survey(join_residues) = {
  my(ps=primes([79,149]), total=0, splits=0, cols=0);
  for(i=1,#ps, for(j=i+1,#ps,
    my(n=ps[i]*ps[j]);
    if(n==10403, next);
    total++;
    my(c=probe(n,220,71,join_residues));
    if(#c,
      if(c[5]!=ps[i] && c[5]!=ps[j], error("incorrect survey factor"));
      splits++; cols+=c[6]);
  ));
  [total,splits,cols];
}

replay() = {
  my(ns = [77,143,221,10001,10203,24997,15251], success = 0);
  for(i = 1, #ns,
    my(n = ns[i], cert = probe(n,220,71));
    if(!#cert, error("missing local certificate: ", n));
    my(base = cert[3], exponent = cert[4], divisor = cert[5]);
    if(n % divisor || divisor <= 1 || divisor >= n || Mod(base,n)^exponent != 1,
      error("invalid output: ",[n,cert]));
    print([n,base,exponent,divisor,cert[6],cert[7]]);
    success++;
  );
  if(#probe(10403,220,71), error("expected unresolved test input"));
  my(joined=probe(10403,220,71,1));
  if(!#joined || joined[5]!=103, error("missing matched-residue certificate"));
  print(success, " splits at identical marks; matched residues also split 10403");
}
if(type(cogentic_as_library) != "t_INT", iferr(replay(),err,print(err);quit(1)));
