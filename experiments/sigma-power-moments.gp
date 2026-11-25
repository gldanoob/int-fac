sigmaPowerTrialLimit(b,shortBlock) = if(shortBlock,max(16,b^2),16);

\\ The returned list is the full nonadaptive query block for N.
sigmaPowerExponents(N,{shortBlock=0}) = {
  if(type(N)!="t_INT" || N<1,error("expected a positive integer"));
  my(b=logint(N,2)+1,h=1,f=1);
  while(f*(h+1)<=N,h++;f*=h);
  h=max(1,min(h,logint(N,sigmaPowerTrialLimit(b,shortBlock)+1)));
  my(J=32*b+32);
  if(shortBlock && b>1,J=ceil(32*b/logint(b,2))+32);
  vector(2*h,i,J+i-1)
};

\\ Recover the least full prime-power block of a residual with no prime <=16.
sigmaPowerSmallest(N,m,S,J,h) = {
  my(b=logint(N,2)+1,mJ=m^(J+1),ph=mJ\S[1],E=1-ph*S[1]/mJ);
  if(E<=0 || E>=1,error("invalid divisor sums"));
  \\ The Jth root of 1/(N*E) is a lower estimate of the least block B.
  my(T=max(8,sqrtnint(1/(N*E),J)),Q=2^(16*b+16));
  if(T>m,error("invalid moment scale"));
  h=min(h,logint(m,T));
  my(Y=vector(2*h,i,
    my(k=i-1,Ej=1-ph*S[i]/(mJ*m^k));
    floor(Q*T^k*Ej/E)
  ));
  \\ At scale Q, the subset terms cost h and moment rounding costs 2h.
  my(H0=matrix(h,h,i,k,Y[i+k-1]),H1=matrix(h,h,i,k,Y[i+k])-3*h*matid(h));
  my(lo=0,hi=1,delta=1/(64*N^2));
  \\ The signature test can have either answer within delta below T/B.
  while(hi-lo>delta,
    my(u=(lo+hi)/2,d=denominator(u));
    if(qfsign(d*H1-numerator(u)*H0)[1],lo=u,hi=u)
  );
  if(lo==0,error("invalid moment bracket"));
  round(T/lo)
};

\\ Use the geometric-series identity to update each supplied divisor sum.
sigmaPowerStrip(S,J,p,B) = {
  vector(#S,i,
    my(term=(p*B^(J+i-1)-1)/(p-1));
    if(S[i]%term,error("invalid residual divisor sum"));
    S[i]\term
  )
};

\\ S[i] is sigma(N^sigmaPowerExponents(N,shortBlock)[i]). Return sorted [prime, exponent] pairs.
sigmaPowerFactors(N,S,{shortBlock=0}) = {
  my(exponents=sigmaPowerExponents(N,shortBlock),J=exponents[1],h=#exponents\2);
  if(type(S)!="t_VEC" || #S!=#exponents,error("expected the full divisor-sum vector"));
  foreach(S,s,if(type(s)!="t_INT" || s<1,error("expected positive integer divisor sums")));
  my(m=N,found=List(),limit=sigmaPowerTrialLimit(logint(N,2)+1,shortBlock));
  for(p=2,limit,
    if(m==1,break());
    my(e=valuation(m,p));
    if(e,
      my(B=p^e);
      listput(found,[p,e]);m\=B;S=sigmaPowerStrip(S,J,p,B)
    )
  );
  while(m>1,
    if(h<1,error("too many prime factors"));
    my(B=sigmaPowerSmallest(N,m,S,J,h),p);
    if(B<2 || m%B,error("invalid recovered block"));
    \\ A promised block is a prime power, so its largest exact root exponent suffices.
    forstep(e=logint(B,2),1,-1,
      p=sqrtnint(B,e);
      if(p^e==B,
        if(!isprime(p),error("composite recovered base"));
        listput(found,[p,e]);break()
      )
    );
    m\=B;
    if(gcd(m,B)!=1,error("incomplete recovered block"));
    S=sigmaPowerStrip(S,J,p,B);
    h--
  );
  foreach(S,s,if(s!=1,error("invalid final divisor sum")));
  vecsort(Vec(found))
};

\\ Only the fixture builder sees the prime factorization before recovery.
checkSigmaPowerCase(P,{shortBlock=0}) = {
  my(N=prod(i=1,#P,P[i][1]^P[i][2]),exponents=sigmaPowerExponents(N,shortBlock));
  my(S=apply(j->prod(i=1,#P,(P[i][1]^(P[i][2]*j+1)-1)/(P[i][1]-1)),exponents));
  if(sigmaPowerFactors(N,S,shortBlock)!=vecsort(P),error("sigma power recovery failed at ",P));
  [logint(N,2)+1,exponents[1],#S,sum(i=1,#S,logint(S[i],2)+1)]
};

checkSigmaPowerMoments() = {
  [
    checkSigmaPowerCase([]),
    checkSigmaPowerCase([[2,5],[3,3],[13,2]]),
    checkSigmaPowerCase([[17,1],[19,1]]),
    checkSigmaPowerCase([[17,3]]),
    checkSigmaPowerCase([[7,2],[53,2],[2803,1],[2819,1],[2833,1]]),
    checkSigmaPowerCase([[2,2],[3,1],[5,1],[7,1],[11,1],[13,1],[17,1],[19,1],[29,1],[10007,1]],1),
    checkSigmaPowerCase([[7,2],[10007,2],[100140043,1],[100140059,1]],1)
  ]
};
