\\ Integer class polynomials, complete Gross-Zagier products and finite-field supersingular polynomials.
default(parisize,96000000);

ramCmClass(d) = {
  my(H);if(!mapisdefined(ramCmCache,d,&H),H=polclass(d);mapput(ramCmCache,d,H));H
};

ramCmHurwitz(n) = {
  my(H=1);for(f=1,sqrtint(n),if(n%(f^2)==0,H*=ramCmClass(-8*(n/f^2))));H
};

ramCmField(r) = ramCmClass(-r);
ramCmBlock(n,r,H) = gcd(n,lift(Mod(polresultant(H,ramCmField(r)),n)^(logint(n,2)+1)));

ramCmThreeSquares(m) = {
  my(count=0);
  for(a=0,sqrtint(m),for(b=0,sqrtint(m-a^2),
    my(z=m-a^2-b^2);if(issquare(z),count+=(1+(a>0))*(1+(b>0))*(1+(z>0)))
  ));count
};

ramCmGZTerm(m,r,n) = {
  my(F=factor(m),eps=vector(matsize(F)[1],i,kronecker(if(F[i,1]==r,-8*n,-r),F[i,1])));
  my(value=1);fordiv(m,d,value*=d^prod(i=1,#eps,eps[i]^valuation(m/d,F[i,1])));value
};

ramCmSupersingular(p) = {
  my(l='y,z='x,h=(p-1)/2,deuring=Mod(1,p)*sum(i=0,h,binomial(h,i)^2*l^i));
  my(image=polresultant(deuring,z*l^2*(1-l)^2-256*(1-l+l^2)^3,l));
  my(S=image/gcd(image,deriv(image,z)));S/pollead(S)
};

checkRamCm() = {
  local(ramCmCache=Map());
  my(composites=0,loc=0,mixed=0,forced=0,multiple=0,proper=0,highest=0);
  forstep(n=3,599,2,
    my(F=factor(n),k=matsize(F)[1]);if(k<2,next);
    my(H=ramCmHurwitz(n),got=0,support=prod(i=1,k,F[i,1]^(F[i,2]%2)));
    if(12*poldegree(H)!=ramCmThreeSquares(2*n),error("ternary degree",n));
    highest=max(highest,poldegree(H));composites++;
    forprime(r=7,151,if(r%8!=7 || n%r==0,next);
      my(block=ramCmBlock(n,r,H),inert=List());
      for(i=1,k,
        my(p=F[i,1],sgn=kronecker(-r,p));
        if(sgn==1 && block%p==0,error("ordinary root",[n,r,p]));
        if(support%p==0 && sgn==-1,listput(inert,p));loc++
      );
      if(#inert==1,
        if(block%inert[1],error("missing zero-trace factor",[n,r,inert[1]]));forced++;
        if(n!=support,multiple++);
        if(k==2 && n==support,mixed++)
      );
      if(block>1 && block<n,got=1)
    );
    proper+=got
  );
  if(proper!=composites,error("finite library missed an input",[proper,composites]));
  print(["composites",composites,"successful splits",proper,"local exclusions checked",loc,
    "forced inert divisibilities",forced,"mixed semiprime checks",mixed,"with repeated factors",multiple,
    "maximum Hurwitz polynomial degree",highest]);
  my(identities=0,terms=0);
  foreach([15,21,33,35,55,65,77,105],n,
    foreach([7,23,31,47],r,if(n%r,
      my(M=2*r*n,H=ramCmClass(-8*n),R=polresultant(H,ramCmField(r)));
      my(total=ramCmGZTerm(M,r,n));
      for(t=1,sqrtint(M-1),
        my(c=ramCmGZTerm(M-t^2,r,n));
        if(denominator(c)!=1 || c<1,error("invalid Gross-Zagier term"));
        if(gcd(t,n)==1 && gcd(c,n)>1,error("nonzero trace support"));
        total*=c^2;terms++
      );
      if(total!=R^2,error("Gross-Zagier product",[n,r]));identities++
    ))
  );
  if(ramCmBlock(65,23,ramCmHurwitz(65))!=5,error("nonprincipal split prime 13"));
  print(["independent Gross-Zagier identities",identities,"positive traces",terms,"nonprincipal case",[65,23,5]]);
  my(tests=0,full=0);
  forprime(p=7,41,
    my(S=ramCmSupersingular(p));
    forprime(q=5,53,if(p!=q,
      my(H=Mod(1,p)*ramCmClass(-8*p*q));
      if((H%S)==0,full++);tests++
    ))
  );
  print(["ramified supersingular coverage checks",tests,"full supersingular supports",full]);
};

iferr(checkRamCm(),err,print(err);quit(1));
