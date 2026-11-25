\\ Run at the repository root. Bit callbacks receive the queried index alone.
middleLocal(p,h,chi) = p^h+(1-chi)*(p^h-1)/(p-1);

middleAmplify(m,B) = {
  my(F=1,ratio=1);
  forprime(p=3,B,
    my(h=valuation(m,p)\2,chi=kronecker(-m/p^(2*h),p));
    F*=p;ratio*=middleLocal(p,h+1,chi)/middleLocal(p,h,chi)
  );
  [m*F^2,ratio]
};

middleUpper(m) = {
  my(b=logint(m,2)+1,upper=2*(b+2));
  forprime(p=3,4*b,
    my(h=valuation(m,p)\2);
    if(h,upper*=middleLocal(p,h,kronecker(-m/p^(2*h),p))/p^h)
  );
  ceil(upper)
};

\\ First j for which m(1+4mj^2)^2 >= 2^(2k).
middleStart(m,k) = {
  my(t=sqrtint((2^(2*k)-1)\m)+1);
  sqrtint((t-2)\(4*m))+1
};

middleScan(m,bitAnswer) = {
  if(m<3 || m%8!=3,error("expected an index 3 modulo 8"));
  my(b=logint(m,2)+1,k=8*b+16,S=j->1+4*m*j^2);
  my(lo=middleStart(m,k),hi=middleStart(m,k+1)-1,mesh=8*middleUpper(m)+1);
  my(first=bitAnswer(m*S(lo)^2),last=first,prev=lo,d=0,left=0,right=0);
  for(t=1,mesh,
    my(j=lo+(hi-lo)*t\mesh,bit=bitAnswer(m*S(j)^2));
    if(bit!=last,
      d++;if(d==1,left=prev;right=j)
    );
    last=bit;prev=j
  );
  if(!d,return(0));
  my(J=1+if(d%2==first,d,d-1));
  while(right-left>1,
    my(j=(left+right)\2);
    if(bitAnswer(m*S(j)^2)==first,left=j,right=j)
  );
  my(lower=ceil(J*2^k/S(right)),upper=ceil(J*2^k/S(left))-1);
  if(lower!=upper,error("middle-digit crossing width"));
  lower
};

middleThreeSquares(m,bitAnswer) = {
  my(count=middleScan(m,bitAnswer),B=logint(m,2)+1);
  while(!count,
    my(pair=middleAmplify(m,B),amplified=middleScan(pair[1],bitAnswer));
    if(amplified,count=amplified/pair[2]);B*=2
  );
  if(type(count)!="t_INT",error("nonintegral recovered count"));
  count
};

middleTwists(n) = {
  my(b=logint(n,2)+1,H=1,goal=logint(b,2)+1,r=1,A=[(3*n)%8]);
  while(H<goal,
    r=nextprime(r+1);while(r%8!=1,r=nextprime(r+1));
    if(n%r==0,error("remove the small library prime ",r));
    A=concat(A,r*A);H*=2
  );
  A
};

middleRamifiedPair(n,bitAnswer) = {
  if(n<=1 || gcd(n,210)!=1,error("expected a stripped cofactor"));
  my(B=logint(n,2)+1);
  foreach(middleTwists(n),a,
    my(nodes=[a*n,a*n^3],values=vector(2),good=1);
    for(i=1,2,
      my(pair=middleAmplify(nodes[i],B),v=middleScan(pair[1],bitAnswer));
      if(!v,good=0;break);
      values[i]=v/pair[2];
      if(type(values[i])!="t_INT",error("inexact ramified count"))
    );
    if(good,return(concat([a],values)))
  );
  []
};

middleFactoredCount(m) = {
  my(F=factor(m),d=prod(i=1,matsize(F)[1],F[i,1]^(F[i,2]%2)));
  my(C=if(d==3,1,3*qfbclassno(-d)));
  for(i=1,matsize(F)[1],my(p=F[i,1],h=F[i,2]\2); C*=middleLocal(p,h,kronecker(-d,p)));
  C
};

middleIndependentOracle(M) = {
  middleCalls++;middlePeak=max(middlePeak,logint(M,2)+1);
  bittest(middleFactoredCount(M),logint(M,2)\2)
};

\\ The larger end-to-end fixture checks its norm multipliers against known base counts.
middleFixtureOracle(M) = {
  foreach(middleSeeds,seed,
    if(M%seed[1],next);
    my(s,v);
    if(issquare(M/seed[1],&s) && (s-1)%(4*seed[1])==0 && issquare((s-1)/(4*seed[1]),&v),
      middleTransfers++;return(bittest(seed[2]*s,logint(M,2)\2))
    )
  );
  error("unrecognized split multiplier")
};

checkMiddleThreeSquares() = {
  local(middleCalls=0,middlePeak=0);
  my(exact=0,ramified=0,split=0,inert=0);
  forstep(m=3,299,8,
    my(c=3*qfbhclassno(m));
    foreach([3,7,17,29,61],B,
      my(pair=middleAmplify(m,B));
      if(middleFactoredCount(pair[1])!=c*pair[2],error("amplification ratio ",[m,B]));exact++
    );
    forprime(p=3,31,my(h=valuation(m,p)\2);if(h,
      my(chi=kronecker(-m/p^(2*h),p));if(chi==0,ramified++,if(chi==1,split++,inert++))
    ))
  );
  if(!ramified || !split || !inert,error("conductor coverage"));
  foreach([3,11,27,35,59,67],m,
    my(c=3*qfbhclassno(m),recovered=middleThreeSquares(m,middleIndependentOracle));
    if(c!=recovered,error("middle-bit recovery ",m))
  );
  my(n=11*13,T=middleTwists(n),b=logint(n,2)+1,orthogonal=0);
  local(middleSeeds=List(),middleTransfers=0);
  foreach(T,a,
    foreach([a*n,a*n^3],m,
      my(seed=middleAmplify(m,b)[1]);listput(middleSeeds,[seed,middleFactoredCount(seed)])
    )
  );
  my(pair=middleRamifiedPair(n,middleFixtureOracle));
  if(#pair!=3 || pair[3]/pair[2]-n-1!=24,error("semiprime from a character library",pair));
  my(primes=[17,41]);
  if(T!=[5,85,205,3485],error("twist family"));
  forprime(p=43,2000,
    my(total=sum(i=1,#T,kronecker(-T[i]*n,p)));
    my(want=kronecker(-5*n,p)*prod(i=1,#primes,1+kronecker(p,primes[i])));
    if(total!=want,error("quadratic character cancellation at ",p));orthogonal++
  );
  print(["amplification checks",exact,"old conductor cases",[ramified,split,inert],"complete count recoveries",6,
         "independent middle-digit queries",middleCalls,"maximum bit length",middlePeak,"library cancellations",orthogonal,
         "semiprime fixture bit transfers",middleTransfers,"decoded twist and counts",pair]);
};

iferr(checkMiddleThreeSquares(),err,print(err);quit(1));
