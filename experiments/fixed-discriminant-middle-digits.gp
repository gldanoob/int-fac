\\ Exact quotient from M, fixed d and requested precision. No large-input count oracle is used.
fixedSmallCount(d) = {
  my(c=0);
  for(x=1,sqrtint(d-2),for(y=1,sqrtint(d-x^2-1),c+=issquare(d-x^2-y^2)));
  c
};

fixedLocal(p,e,d) = 1+(1-kronecker(-d,p))*(p^e-1)/(p^e*(p-1));

\\ Lehman's deterministic cubic-root search. The prime markers are certified by exhausting the search.
fixedLehmanDivisor(n) = {
  if(n<4,return(n));
  my(root=sqrtint(n));if(root^2==n,return(root));
  my(K=sqrtnint(n,3)+1,W=sqrtnint(n,6)+1);
  for(v=2,K,if(n%v==0,return(v)));
  for(k=1,K,
    my(z=4*k*n,A=sqrtint(z-1)+1,span=ceil(W/sqrtint(k))+2);
    for(a=A,A+span,
      my(b);if(issquare(a^2-z,&b),
        my(g=gcd(n,a+b));if(g>1 && g<n,return(g))
      )
    )
  );
  n
};

fixedPrimeList(n) = {
  if(n==1,return([]));
  my(g=fixedLehmanDivisor(n));
  if(g==n,[n],concat(fixedPrimeList(g),fixedPrimeList(n/g)))
};

fixedRemainingLocal(n,d) = {
  my(ps=vecsort(fixedPrimeList(n)),i=1,v=1);
  while(i<=#ps,
    my(p=ps[i],j=i+1);while(j<=#ps && ps[j]==p,j++);
    v*=fixedLocal(p,j-i,d);i=j
  );
  v
};

\\ Return [exact quotient, largest trial candidate in the staged search, used Lehman fallback].
fixedMiddleQuotient(M,d,t) = {
  my(f);
  if(d%8!=3 || M%d || !issquare(M/d,&f) || f%2!=1,error("invalid fixed-discriminant index"));
  my(k=logint(M,2)\2);
  if(t<0 || t>k,error("requested digit outside the supported range"));
  my(step=2^(k-t),lo=fixedSmallCount(d)*f,r=f,done=1,cap=sqrtnint(f,3)+1,Y=min(cap,8));
  while(1,
    for(p=done+1,Y,
      if(r%p==0,
        my(e=valuation(r,p));r/=p^e;lo*=fixedLocal(p,e,d)
      )
    );
    if(r==1,return([floor(lo/step),Y,0]));
    if(r<(Y+1)^2,return([floor(lo*fixedLocal(r,1,d)/step),Y,0]));
    my(h=logint(r,Y+1),hi=floor(lo*((Y+2)/Y)^h));
    if(floor(lo/step)==hi\step,return([hi\step,Y,0]));
    if(Y==cap,return([floor(lo*fixedRemainingLocal(r,d)/step),Y,1]));
    done=Y;Y=min(2*Y,cap)
  )
};

fixedReference(f,d) = {
  my(F=factor(f));
  fixedSmallCount(d)*f*prod(i=1,matsize(F)[1],fixedLocal(F[i,1],F[i,2],d))
};

fixedFirstPad(u,K) = {
  my(s=sqrtint((2^(2*K)-1)\u)+1);
  sqrtint((s-2)\(4*u))+1
};

\\ Encode the comparison z>=target in a standard middle digit when n=pz is mixed modulo 3.
fixedComparisonPad(n,target) = {
  my(u=3*n^2,K=8*(logint(u,2)+1)+16,needed=ceil(2^K/(n+2*target)));
  my(z=ceil((needed-1)/(4*u)),j=if(z>0,1+sqrtint(z-1),0),s=1+4*u*j^2);
  if((n+2*(target-1))*s>=2^K || (n+2*target)*s<2^K || logint(u*s^2,2)\2!=K,
    error("unable to encode the comparison"));
  [u*s^2,s,K]
};

fixedFinishMixed(n,lo,hi) = {
  my(rad=max(1,sqrtnint(n,4)\64),A=ceil(sqrtint(n)/2));
  forstep(v=lo,hi,2*rad+1,
    my(c=v+rad,roots=zncoppersmith('x+c,n,rad,A));
    foreach(roots,w,my(z=c+w);
      if(z>1 && z<n && n%z==0,return(if(z%3==1,z,n/z)))
    )
  );
  0
};

checkFixedDigits() = {
  for(n=2,5000,
    my(g=fixedLehmanDivisor(n));
    if(g<=1 || n%g || (g==n)!=isprime(n),error("Lehman witness ",[n,g]))
  );
  foreach([3,11,19,35,59],d,
    if(!issquarefree(d) || fixedSmallCount(d)!=3*qfbhclassno(d),error("base count ",d))
  );
  my(total=0,fallbacks=0,trial=0);
  foreach([3,11,19,35,59],d,
    forstep(f=1025,2047,2,
      my(M=d*f^2,c=fixedReference(f,d),k=logint(M,2)\2);
      foreach([0,2],t,
        my(v=fixedMiddleQuotient(M,d,t));if(v[1]!=c\2^(k-t),error("ordinary quotient ",[M,t,v]));
        total++;trial+=v[2];fallbacks+=v[3]
      )
    )
  );
  print(["ordinary exact quotients",total,"fallbacks",fallbacks,"mean trial cutoff",trial/total]);
  my(pads=0,maxY=0,peak=0,capUsed=0);
  foreach([[3,143],[3,187],[11,143],[19,11^2*13]],pair,
    my(d=pair[1],n=pair[2],u=d*n^2,c=fixedReference(n,d),K=8*(logint(u,2)+1)+16);
    my(lo=fixedFirstPad(u,K),hi=fixedFirstPad(u,K+1)-1);
    for(i=0,31,
      my(j=lo+(hi-lo)*(2*i+1)\64,s=1+4*u*j^2,M=u*s^2);
      foreach([0,2],t,my(v=fixedMiddleQuotient(M,d,t));
        if(v[1]!=c*s\2^(K-t),error("padded quotient ",[d,n,i,t]));
        pads++;maxY=max(maxY,v[2]);capUsed+=v[3];peak=max(peak,logint(M,2)+1)
      )
    )
  );
  print(["direct exact standard-pad quotients",pads,"largest index bits",peak,
         "largest trial cutoff",maxY,"fallbacks",capUsed]);
  my(p=10007,z=17011,n=p*z,lo=sqrtint(n)\2,hi=2*sqrtint(n)+2,calls=0);
  if(!isprime(p) || !isprime(z) || p%3!=2 || z%3!=1,error("mixed semiprime fixture"));
  while(hi-lo>2*sqrtnint(n,4),
    my(mid=(hi+lo+1)\2,pad=fixedComparisonPad(n,mid));
    my(bit=bittest(pad[2]*(n+2*z),pad[3]));if(bit!=(z>=mid),error("wrong threshold bit"));
    if(bit,lo=mid,hi=mid-1);calls++
  );
  if(fixedFinishMixed(n,lo,hi)!=z,error("terminal Coppersmith split"));
  print(["mixed input",n,"comparison bits",calls,"final interval",[lo,hi],"lattice factor",z]);
};

iferr(checkFixedDigits(),err,print(err);quit(1));
