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

compactPadK(b) = (3*b+1)\2+2*(logint((b+2)^12,2)+1)+8;
compactCoprime(m,x,step) = {while(gcd(x,2*m)!=1,x+=step);x};
compactStart(m,k) = {
  my(s=sqrtint((2^(2*k)-1)\m)+1);
  sqrtint(s-4*m-1)+1
};

compactBracket(m,k,lo,hi,first,bitAnswer) = {
  while(hi-lo>1,
    my(mid=(lo+hi)\2,w=compactCoprime(m,mid,1));
    if(w>=hi,w=compactCoprime(m,mid,-1));
    if(w<=lo,break);
    if(bitAnswer(m*(w^2+4*m)^2)==first,lo=w,hi=w)
  );
  [lo^2+4*m,hi^2+4*m]
};

\\ Return the count or zero. The first two transitions determine the count without endpoint labels.
compactScan(m,bitAnswer) = {
  my(b=logint(m,2)+1,k=compactPadK(b),Q=2^k,U=middleUpper(m),mesh=16*U+1);
  my(lo=compactCoprime(m,compactStart(m,k),1),hi=compactCoprime(m,compactStart(m,k+1)-1,-1));
  my(prev=lo,first=bitAnswer(m*(lo^2+4*m)^2),last=first,changes=List());
  for(i=1,mesh,
    my(x=min(hi,compactCoprime(m,lo+(hi-lo)*i\mesh,1)));
    if((x^2-prev^2)^2*U^2*m>=Q^2,error("compact qualifying gap too large"));
    my(bit=bitAnswer(m*(x^2+4*m)^2));
    if(bit!=last,
      listput(changes,compactBracket(m,k,prev,x,last,bitAnswer));
      if(#changes==2,break)
    );
    prev=x;last=bit
  );
  if(!#changes,return(0));
  my(a=changes[1],bot=0,top=0);
  if(#changes==2,
    my(z=changes[2]);bot=ceil(Q/(z[2]-a[1]));top=floor(Q/(z[1]-a[2])),
    my(J=if(first,2,1));bot=ceil(J*Q/a[2]);top=ceil(J*Q/a[1])-1
  );
  if(bot==top,bot,0)
};

\\ On a possible endpoint ambiguity, only an exact value seen in two independent scans is accepted.
compactMajority(m,bitAnswer,markers,{inspect=0}) = {
  my(v=[compactScan(m,bitAnswer),0,0]);
  for(i=1,2,
    my(p=markers[i]);
    if(!isprime(p) || kronecker(-m,p)!=-1,error("invalid compact inert marker"));
    v[i+1]=compactScan(m*p^2,bitAnswer)/(p+2)
  );
  for(i=1,3,if(v[i]>0 && denominator(v[i])==1,
    for(j=i+1,3,if(v[j]==v[i],return(if(inspect,[v[i],v],v[i]))))
  ));
  if(inspect,[0,v],0)
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

compactFixtureOracle(M) = {
  foreach(compactSeeds,seed,
    if(M%seed[1],next);
    my(s,x);
    if(issquare(M/seed[1],&s) && s>=4*seed[1] && issquare(s-4*seed[1],&x) && gcd(x,2*seed[1])==1,
      compactCalls++;compactPeak=max(compactPeak,logint(M,2)+1);
      return(bittest(s*seed[2],logint(M,2)\2))
    )
  );
  error("unrecognized compact primitive norm")
};

compactMarkers(m) = {
  my(b=logint(m,2)+1,Y=max(16*middleUpper(m),b^8),p=Y,ret=List());
  while(#ret<2,p=nextprime(p+1);if(kronecker(-m,p)==-1,listput(ret,p)));
  if(p>2*Y,error("fixture missed its marker interval"));
  Vec(ret)
};

checkCompactPads() = {
  local(middleCalls=0,middlePeak=0,compactCalls=0,compactPeak=0,compactSeeds=[]);
  foreach([3,11,27,35,59],m,
    if(compactScan(m,middleIndependentOracle)!=middleFactoredCount(m),error("compact exact count ",m))
  );
  print(["compact independently evaluated answers",middleCalls,"peak index bits",middlePeak]);
  my(amp=middleAmplify(11,89),C=middleFactoredCount(11)*amp[2]);
  if(25*C^2<121*amp[1],error("fixture did not reach two transitions"));
  compactSeeds=[[amp[1],C]];
  if(compactScan(amp[1],compactFixtureOracle)!=C,error("two compact transitions"));
  my(r=9*(2^169+1),m=r^2+2,markers=compactMarkers(m),total=0,corrected=0);
  foreach([r\2+1,r,2*r,3*r,7*r+1],v,
    compactSeeds=concat([[m,v]],vector(2,i,[m*markers[i]^2,(markers[i]+2)*v]));
    my(response=compactMajority(m,compactFixtureOracle,markers,1));
    if(response[1]!=v,error("compact synthetic endpoint ",v));
    corrected+=(response[2][1]!=v);total++
  );
  if(!corrected,error("endpoint fixture did not exercise a correction"));
  print(["full-count two-transition input bits",logint(amp[1],2)+1,"synthetic endpoint tests",total,
         "unperturbed failures corrected",corrected,"norm-transfer answers",compactCalls,"peak index bits",compactPeak]);
  my(a=Mod(3,8),crtCases=0,gains=0);
  forprime(p=3,19,
    my(x=1);while(kronecker(-x,p)!=-1,x++);a=chinese(a,Mod(x,p));
    my(d=lift(a));while(!issquarefree(d),d+=a.mod);
    if(d%8!=3 || !prod(q=2,p,if(isprime(q) && q>2,kronecker(-d,q)==-1,1)),
      error("prescribed inert progression",[p,d]));
    my(C=middleFactoredCount(d));
    forprime(q=3,p,
      if(middleFactoredCount(d*q^4)!=C*middleLocal(q,2,-1),error("inert gain",[d,q]));gains++
    );crtCases++
  );
  print(["squarefree prescribed-character progressions",crtCases,"exact inert prime-square gains",gains]);
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

iferr({checkMiddleThreeSquares();checkCompactPads()},err,print(err);quit(1));
