\\ Read experiments/lucas-carmichael.gp first for lcChain.
\\ This finite experiment tests the prime bases through 31 on each denominator.
sigmaDenominatorPrime(d,exponent) = {
  my(p);
  if(isprimepower(d,&p),return(p));
  forprime(a=2,31,
    if(d%a==0,return(a));
    my(g=lcChain(d,exponent,Mod(a,d)));
    if(g>1,
      p=sigmaDenominatorPrime(g,exponent);
      if(p,return(p));
      return(sigmaDenominatorPrime(d/g,exponent))
    )
  );
  0
};

\\ Return [certified prime, convergent] or [] if the bounded search misses.
sigmaTailPrime(m,s) = {
  if(type(m)!="t_INT" || type(s)!="t_INT" || m<2 || s<1,error("expected m>=2 and s>=1"));
  my(a=m,b=s,c0=0,c=1,d0=1,d=0);
  while(b,
    my(t=a\b);
    [a,b]=[b,a%b];
    [c0,c]=[c,c0+t*c];
    [d0,d]=[d,d0+t*d];
    if(d>1 && c>0 && m%d==0,
      my(p=sigmaDenominatorPrime(d,(m/d)*c));
      if(p,return([p,c/d]))
    )
  );
  []
};

\\ Only the fixture builder knows the prime powers. Decode the successive
\\ residuals using the prime and its valuation to update both inputs.
checkSigmaTailCase(primes,exponents,{first=0}) = {
  my(m=prod(i=1,#primes,primes[i]^exponents[i]));
  my(s=prod(i=1,#primes,(primes[i]^(exponents[i]+1)-1)/(primes[i]-1)));
  my(found=List());
  while(m>1,
    my(hit=sigmaTailPrime(m,s));
    if(!#hit,error("no convergent yielded a prime at ",[primes,exponents]));
    my(p=hit[1],d=denominator(hit[2]));
    if(first && !#found && first!=hit[2],error("unexpected first convergent ",hit));
    if(!isprime(p) || d%p || m%d,error("invalid denominator certificate ",hit));
    my(e=valuation(m,p),power=p^e,term=(p*power-1)/(p-1));
    if(s%term,error("residual divisor sum"));
    listput(found,[p,e]); m/=power; s/=term
  );
  if(s!=1 || vecsort(Vec(found))!=vector(#primes,i,[primes[i],exponents[i]]),
    error("factorization mismatch at ",[primes,exponents]));
  1
};

checkSigmaTail() = {
  \\ The factor 53 cancels in the full ratio; its denominator is 59*107.
  checkSigmaTailCase([53,59,107],[28,30,36],6032/6313);
  \\ The first denominator is the proper prefix 53*59.
  checkSigmaTailCase([53,59,2147483647],[28,30,36],3016/3127);
  checkSigmaTailCase([37,149],[10,12],144/149);
  if(sigmaTailPrime(35,35)!=[] || sigmaDenominatorPrime(59^3,1)!=59,
    error("empty convergent search or prime-power denominator"));
  3
};

\\ Optional 2,240 complete recoveries, with multiplicities up to 256.
checkSigmaTailSweep() = {
  my(pool=[53,59,67,107,149,257,2147483647],powers=[27,31,72,256],cases=0);
  for(i=1,#pool,for(j=i+1,#pool,for(k=j+1,#pool,
    foreach(powers,u,foreach(powers,v,foreach(powers,w,
      cases+=checkSigmaTailCase([pool[i],pool[j],pool[k]],[u,v,w])
    )))
  )));
  cases
};
