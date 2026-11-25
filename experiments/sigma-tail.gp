\\ Read experiments/lucas-carmichael.gp first for lcChain.
\\ This finite experiment tests the prime bases through 31 on each denominator.
sigmaDenominatorPrime(d,exponent,{bound=31}) = {
  my(p);
  if(isprimepower(d,&p),return(p));
  forprime(a=2,min(d-1,bound),
    if(d%a==0,return(a));
    my(g=lcChain(d,exponent,Mod(a,d)));
    if(g>1,
      p=sigmaDenominatorPrime(g,exponent,bound);
      if(p,return(p));
      return(sigmaDenominatorPrime(d/g,exponent,bound))
    )
  );
  0
};

sigmaOneExponent(N) = {
  if(type(N)!="t_INT" || N<2,error("expected an integer at least two"));
  my(b=logint(N,2)+1,L=max(16,b^2),t=8*b*N,k=logint(t,L+1));
  max(1,k-((L+1)^k==t))
};

\\ Given floor(N^(J+1)/sigma(N^J)) at the public exponent above, recover phi(N).
sigmaOneTotient(N,C) = {
  my(J=sigmaOneExponent(N),b=logint(N,2)+1,L=max(16,b^2),m=N,phi=1);
  if(type(C)!="t_INT" || C<0 || C>N,error("invalid reciprocal"));
  my(scale=1);
  forprime(p=2,L,
    if(m==1,break);
    my(e=valuation(m,p));
    if(e,
      my(B=p^e);
      scale*=B^(J+1)*(p-1)/(p*B^J-1);
      phi*=B/p*(p-1);m\=B
    )
  );
  if(m>1,
    my(v=2*ceil(((C-1/4)/scale-1/8)/2));
    if(v<1 || v>m || v>=(C+5/4)/scale,error("unusable reciprocal"));
    phi*=v
  );
  phi
};

\\ E also annihilates units modulo each divisor of the original input.
sigmaOnePowerFactors(N,C) = {
  my(E=sigmaOneTotient(N,C),m=N,found=List(),phi=1);
  while(m>1,
    my(p=sigmaDenominatorPrime(m,E,m));
    if(!p,error("no factor at the supplied reciprocal"));
    my(e=valuation(m,p),B=p^e);
    listput(found,[p,e]);m\=B;phi*=B/p*(p-1)
  );
  if(phi!=E,error("inconsistent reciprocal"));
  vecsort(Vec(found))
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
  my(n=43912157131979933002905882398568,C=14637732739448786428993195606914);
  if(sigmaOneExponent(n)!=8 || sigmaOneTotient(n,C)!=14636988629364742811360062153344 ||
     sigmaOnePowerFactors(n,C)!=[[2,3],[3,1],[110543,2],[110587,1],[110629,3]],
    error("one compressed divisor sum"));
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
