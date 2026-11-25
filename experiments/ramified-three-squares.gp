\\ Public algorithms take an exact count callback or a one-bit callback.
read("experiments/lucas-carmichael.gp");

ramifiedTwist(n) = (3*n) % 8;

\\ Build divisors from the supplied prime list, including multiplicities.
ramifiedDivisors(primes) = {
  my(ds=[1]);
  foreach(Set(primes),p,
    my(e=sum(i=1,#primes,primes[i]==p));
    ds=concat(vector(e+1,j,p^(j-1)*ds))
  );
  ds
};

ramifiedFactor(N,answer) = {
  if(type(N)!="t_INT" || N<1,error("expected a positive integer"));
  my(n=N,found=List());
  foreach([2,3,5,7],p,while(n%p==0,listput(found,p);n\=p));
  if(n==1,return(vecsort(Vec(found))));
  if(isprime(n),listput(found,n);return(vecsort(Vec(found))));
  my(base=answer(ramifiedTwist(n)*n),s=n);
  if(base^4>=n^3,
    for(k=11,sqrtint(n),while(s%k==0,listput(found,k);s\=k));
    if(s>1,listput(found,s));return(vecsort(Vec(found)))
  );
  my(baseFactors=ramifiedFactor(base,answer));
  foreach(ramifiedDivisors(baseFactors),d,
    for(h=1,logint(n,2)\2,
      my(root=sqrtnint(d,h));
      for(p=max(11,root-2),root,
        if(s%(p^2)==0 && isprime(p),
          while(s%p==0,listput(found,p);s\=p)
        )
      )
    )
  );
  if(s>1 && isprime(s),listput(found,s);s=1);
  if(s>1,
    my(a=ramifiedTwist(s),den=if(s==n,base,answer(a*s)));
    my(sig=answer(a*s^3)/den);
    if(type(sig)!="t_INT" || sig<1,error("nonintegral squarefree ratio"));
    my(v=valuation(sig,2),odd=sig>>v);
    if(2*odd>=s,error("odd divisor sum failed to shrink"));
    my(sigFactors=concat(vector(v,j,2),ramifiedFactor(odd,answer)));
    foreach(ramifiedDivisors(sigFactors),d,
      my(p=d-1);
      if(p>=11 && s%p==0 && isprime(p),listput(found,p);s\=p)
    );
    if(s!=1,error("incomplete squarefree factorization"))
  );
  vecsort(Vec(found))
};

\\ Find the first term in z=1+2^(i+1)t above the requested index size.
ramifiedDigitQuery(m,i,alpha) = {
  my(b=logint(m,2)+1,step=2^(i+1),k=i+2*ceil(b/2));
  while(1,
    my(height=ceil(k/alpha),goal=2^height);
    my(index=t->m*(1+m*2^(k-i)*(1+step*t)^2)^2);
    my(lo=-1,hi=0);
    if(index(hi)<goal,
      hi=1;while(index(hi)<goal,hi*=2);
      while(hi-lo>1,my(mid=(lo+hi)\2);if(index(mid)<goal,lo=mid,hi=mid))
    );
    my(M=index(hi));
    if(M<2*goal,return(M));
    k+=2
  )
};

ramifiedRecoverCount(m,alpha,bitAnswer) = {
  if(m<=0 || m%8!=3 || alpha<=0 || alpha>=1/2,error("invalid digit input"));
  my(b=logint(m,2)+1,mc=sum(i=0,b-1,2^i*bitAnswer(ramifiedDigitQuery(m,i,alpha))));
  lift(Mod(mc,2^b)/m)
};

\\ Independent test oracle for large indices. It factors the queried integer,
\\ evaluates its fundamental class number, and includes all local factors.
ramifiedFactoredCount(m) = {
  my(F=factor(m),d=prod(i=1,matsize(F)[1],F[i,1]^(F[i,2]%2)));
  if(m%8!=3,error("index outside progression"));
  my(v=if(d==3,1,3*qfbclassno(-d)));
  for(i=1,matsize(F)[1],
    my(p=F[i,1],h=F[i,2]\2);
    v*=p^h+(1-kronecker(-d,p))*(p^h-1)/(p-1)
  );
  v
};

ramifiedPosition(m,alpha) = logint(m^numerator(alpha),2)\denominator(alpha);

ramifiedPairMultiple(m) = {
  my(a=ramifiedTwist(m));listput(ramifiedRounds,m);
  ramifiedFactoredCount(a*m)*ramifiedFactoredCount(a*m^3)
};

checkRamifiedThreeSquares() = {
  my(ncounts=0,nqueries=0,peak=0,direct=0);
  forstep(m=3,507,8,
    my(literal=sum(x=1,sqrtint(m),sum(y=1,sqrtint(m-x^2),issquare(m-x^2-y^2))));
    if(literal!=ramifiedFactoredCount(m) || literal!=3*qfbhclassno(m),error("literal ",m));
    ncounts++
  );
  foreach([1/4,1/3,2/5],alpha,
    forstep(m=3,59,8,
      for(i=0,logint(m,2),
        my(M=ramifiedDigitQuery(m,i,alpha));nqueries++;peak=max(peak,logint(M,2)+1);
        if(M<=10^7,
          if(ramifiedFactoredCount(M)!=3*qfbhclassno(M),error("padded Hurwitz count ",M));direct++
        )
      );
      my(oracle=M->bittest(ramifiedFactoredCount(M),ramifiedPosition(M,alpha)));
      if(ramifiedRecoverCount(m,alpha,oracle)!=3*qfbhclassno(m),error("digit recovery ",[m,alpha]))
    )
  );
  my(literalOracle=m->3*qfbhclassno(m),cases=0);
  for(n=1,350,
    my(F=factor(n),want=if(n==1,[],concat(vector(matsize(F)[1],i,vector(F[i,2],j,F[i,1])))));
    if(ramifiedFactor(n,literalOracle)!=want,error("small factorization ",n));cases++
  );
  my(fixtures=[[11,11,13,17],[11,11,11,13,13,17],[11,13,17,19],[2,2,3,5,7,11,11,13,17,19],
    [13,13,17,17,17,17],[23,29,43,59,67],[11,11,13,13,17,17,19]]);
  foreach(fixtures,v,
    my(n=prod(i=1,#v,v[i]));
    if(ramifiedFactor(n,ramifiedFactoredCount)!=v,error("factorization fixture ",n));cases++
  );
  my(fixedBit=M->bittest(ramifiedFactoredCount(M),ramifiedPosition(M,1/4)));
  if(ramifiedFactor(11^2*13*17,m->ramifiedRecoverCount(m,1/4,fixedBit))!=[11,11,13,17],
     error("end to end fixed-digit factorization"));
  my(covered=0);
  for(n=11,3000,
    if(gcd(n,210)!=1,next);
    my(F=factor(n),a=ramifiedTwist(n),cube=ramifiedFactoredCount(a*n^3));
    for(i=1,matsize(F)[1],if(F[i,2]==1,
      if(cube%(F[i,1]+1),error("cyclotomic coverage ",n));covered++));
    if(issquarefree(n) && cube!=ramifiedFactoredCount(a*n)*sigma(n),error("squarefree ratio ",n))
  );
  local(ramifiedRounds=List());
  my(layered=11^3*13^6*17^4*19^8);
  if(factorWithSigma(layered,ramifiedPairMultiple)!=[[11,3],[13,6],[17,4],[19,8]] ||
     Vec(ramifiedRounds)!=[layered,13^3*17^2*19^4,17*19^2],error("paired-count rounds"));
  my(m=11^3*13^2,a=ramifiedTwist(m));
  if(ramifiedFactoredCount(a*m)%12 || ramifiedFactoredCount(a*m^3)%12==0,error("base-only multiple"));
  print(["literal counts",ncounts,"fixed-digit answers",nqueries,"largest queried bit length",peak,"direct padded checks",direct,"factorizations",cases+1,"multiplicity-one divisibilities",covered,"paired-count rounds",#ramifiedRounds]);
};

iferr(checkRamifiedThreeSquares(),err,print(err);quit(1));
