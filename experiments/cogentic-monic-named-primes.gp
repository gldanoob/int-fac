\\ Named p-maximal bases and exact local ideal-power membership.

named_basis_matrix(basis) = {
  matrix(#basis,#basis,i,j,polcoef(basis[j],i-1));
};

named_valuations(P,p,points) = {
  if(!isprime(p),error("the named modulus must be prime"));
  my(d=poldegree(P), eye=matid(d));
  my(C=named_basis_matrix(nfbasis([P,[p]])), source_index=1/abs(matdet(C)));
  my(index=p^valuation(source_index,p), h=source_index/index);
  my(B=C*mathnf(matconcat([C^-1,h*eye])), Binv=B^-1);
  if(1/abs(matdet(B))!=index,error("incorrect p-primary overorder index"));
  my(loc=nfinit([P,[p]],4), coeffs=named_basis_matrix(loc.zk));
  my(scale=loc.index/p^valuation(loc.index,p), primes_above=idealprimedec(loc,p));
  my(types=apply(pr->[pr.e,pr.f],primes_above), lattices=vector(#primes_above));
  my(values=matrix(#points,#primes_above), norms=vector(#points), marks=vector(#points));
  for(k=1,#points,
    my(a=points[k][1], b=points[k][2]);
    norms[k]=valuation(sum(j=0,d,polcoef(P,j)*a^j*b^(d-j)),p);
    marks[k]=Binv*concat([a,-b],vector(d-2))~;
    if(denominator(marks[k])!=1,error("power-order mark left the local order"));
  );
  for(j=1,#primes_above,
    my(pr=primes_above[j], generator=Polrev(Vec(scale*coeffs*pr.gen[2]),x));
    my(images=vector(d,k,lift(Mod(generator*Polrev(Vec(B[,k]),x),P))));
    my(mult=Binv*matrix(d,d,r,s,polcoef(images[s],r-1)));
    if(denominator(mult)!=1,error("local generator did not preserve the order"));
    my(J=mathnf(matconcat([p*eye,mult])), power=eye);
    lattices[j]=J;
    my(inverses=vector(vecmax(norms)\pr.f,k,
      power=mathnf(matconcat([p*power,mult*power]));
      if(matdet(power)!=p^(k*pr.f),error("wrong ideal-power index"));
      power^-1));
    for(k=1,#points,
      for(l=1,norms[k]\pr.f,
        if(denominator(inverses[l]*marks[k])!=1,break);
        values[k,j]=l;
      );
    );
  );
  for(k=1,#points,
    if(sum(j=1,#primes_above,types[j][2]*values[k,j])!=norms[k],error("local exponents disagree with the norm"));
  );
  [B,source_index,index,types,lattices,values];
};

named_parity(coefficients,points,named) = {
  if(!#points,return([]));
  my(parts=vector(#points,k,List()));
  for(i=1,#coefficients,
    my(P=Polrev(coefficients[i]));
    for(t=1,#named,
      my(p=named[t],data=named_valuations(P,p,points));
      for(k=1,#points,for(j=1,#data[4],
        if(data[6][k,j]%2,listput(parts[k],[i,p,j]));
      ));
    );
  );
  apply(Vec,parts);
};

named_check(coefficients,points,named) = {
  my(ref=all_ideal_reference(coefficients,points,vecmax(named)), parity=vector(#points,k,List()));
  my(summaries=List(), count=0);
  for(i=1,#coefficients,
    my(P=Polrev(coefficients[i]), d=poldegree(P), full=nfinit(P), inv=named_basis_matrix(full.zk)^-1);
    for(t=1,#named,
      my(p=named[t], data=named_valuations(P,p,points), map=inv*data[1]);
      my(primes_above=idealprimedec(full,p), ideals=apply(pr->idealhnf(full,pr),primes_above));
      if(denominator(map)!=1 || valuation(abs(matdet(map)),p)!=0 || #primes_above!=#data[4],
        error("local order did not match the full order at the named prime"));
      listput(summaries,[i,p,data[2],data[3],full.index]);
      for(j=1,#data[4],
        my(extended=mathnf(matconcat([p*matid(d),map*data[5][j]])), target=0);
        for(k=1,#ideals,if(ideals[k]==extended,target=k;break));
        if(!target || data[4][j]!=[primes_above[target].e,primes_above[target].f],
          error("failed to match the exact local prime ideal"));
        for(k=1,#points,
          my(exponent=data[6][k,j], elt=points[k][1]-points[k][2]*x);
          if(exponent!=idealval(full,elt,primes_above[target]),error("incorrect local valuation"));
          if(exponent%2,listput(parity[k],[i,p,target]));
          count++;
        );
      );
    );
  );
  for(k=1,#points,
    if(Set(Vec(parity[k]))!=Set(select(row->setsearch(named,row[2]),ref[2][k])),
      error("named-prime parity differs from the all-ideal reference"));
  );
  [count,Vec(summaries)];
};

named_replay() = {
  my(points=List());
  for(a=-20,20,for(b=1,20,if(gcd(a,b)==1 && gcd(a-29*b,895)==1,listput(points,[a,b]))));
  if(#points!=425,error("wrong N=895 grid"));
  print([895,named_check([[54,0,1],[54,0,-28,1]],Vec(points),[2,3,5,7,11,13])]);
  print(["singular",named_check([[10,2,1],[10,10,2,1],[338,26,2,1]],
      [[-1,1],[0,1],[1,1],[2,1],[3,2],[13,1]],[2,3,5,13])]);
  my(quad=named_valuations(x^2+2*x+10,3,[[-1,1]]));
  if(quad[4]!=[[1,2]] || quad[6][1,1]!=1,error("missed the singular inert exponent"));
  my(cubic=named_valuations(x^3+2*x^2+26*x+338,13,[[0,1]]));
  if(vecsort(Vec(cubic[6][1,]))!=[0,1,1],error("merged singular cubic valuations"));
  my(raw=named_valuations(x^3-28*x^2+54,5,[[-3,1]]));
  if(raw[3]!=5 || vecsort(Vec(raw[6][1,]))!=[0,1,1],error("missed the two cubic ideals above five"));
  if(#named_parity([[54,0,-28,1]],[[-3,1]],[5])[1]!=2,error("wrong named-prime parity API"));

  my(q=1000000007, r=1000050017, P=x^2+2*r*q^2);
  if(!isprime(q) || !isprime(r),error("wrong analytic quadratic fixture"));
  my(control=named_valuations(P,2,[[0,1],[1,1]]));
  if(control[3]!=1 || control[4]!=[[2,1]] || Vec(control[6][,1])!=[1,0],
    error("named prime failed on strict local suborder"));
  print(["strict quadratic",control[2],control[3],q,control[4],Vec(control[6][,1])]);
};

if(type(cogentic_as_library)!="t_INT",iferr(read("cogentic-all-ideal-reference.gp");named_replay(),err,print(err);quit(1)));
