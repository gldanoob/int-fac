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

\\ Monic subproduct and remainder trees over a possibly composite residue ring.
fixedProductTree(leaves) = {
  my(layers=List([leaves]),row=leaves);
  while(#row>1,
    row=vector((#row+1)\2,i,if(2*i<=#row,row[2*i-1]*row[2*i],row[2*i-1]));
    listput(layers,row)
  );
  Vec(layers)
};

fixedStripInterval(r,done,Y) = {
  if(r==1 || done>=Y,return([r,[]]));
  my(h=sqrtint(Y-done-1)+1,blocks=(Y-done+h-1)\h,unit=Mod(1,r));
  my(factors=fixedProductTree(vector(h,i,unit*('x+i))),product=factors[#factors][1]);
  my(tree=fixedProductTree(vector(blocks,i,unit*('x-done-(i-1)*h))),values=[product%tree[#tree][1]]);
  forstep(k=#tree-1,1,-1,
    my(nextValues=vector(#tree[k],i,values[(i+1)\2]%tree[k][i]));
    values=nextValues
  );
  my(parts=List());
  for(i=1,blocks,
    if(gcd(r,lift(polcoef(values[i],0)))==1,next);
    for(p=max(2,done+(i-1)*h+1),min(Y,done+i*h),
      if(r%p==0,my(e=valuation(r,p));r/=p^e;listput(parts,[p,e]))
    )
  );
  [r,Vec(parts)]
};

fixedCompactK(b) = (3*b+1)\2+2*(logint((b+2)^12,2)+1)+8;

fixedPadOptions(d,k) = {
  my(opts=List(),lo=1,hi=k,b);
  if(k>=24 && k%8==0,b=(k-16)\8;listput(opts,[sqrtint((2^b-1)\d),b,0]));
  while(lo<hi,my(mid=(lo+hi)\2);if(fixedCompactK(mid)<k,lo=mid+1,hi=mid));
  if(fixedCompactK(lo)==k,listput(opts,[sqrtint((2^lo-1)\d),lo,1]));
  Vec(opts)
};

\\ A valid recovered outer conductor is an exact certificate for its local contribution.
fixedPadCertificate(f,d,opt,small) = {
  my(H=opt[1],b=opt[2]);
  if(!H,return(0));
  my(xs=[1]);
  foreach(small,pe,
    my(old=xs,p=pe[1]);
    for(e=1,pe[2],xs=concat(xs,select(v->v<=H,old*p^e)))
  );
  foreach(xs,n,
    my(u=d*n^2,s=f\n);
    if(logint(u,2)+1!=b,next);
    if(opt[3],
      my(x);if(s<4*u || !issquare(s-4*u,&x) || gcd(x,2*u)!=1,next),
      if((s-1)%(4*u) || !issquare((s-1)\(4*u)),next)
    );
    my(c=fixedSmallCount(d)*n);
    foreach(small,pe,if(n%pe[1]==0,c*=fixedLocal(pe[1],valuation(n,pe[1]),d)));
    return(s*c)
  );
  0
};

\\ Return exact quotient, largest cutoff and strategy (0 enclosure, 1 toy fallback, 2 certified pad).
fixedMiddleQuotient(M,d,t) = {
  my(f);
  if(d%8!=3 || M%d || !issquare(M/d,&f) || f%2!=1,error("invalid fixed-discriminant index"));
  my(k=logint(M,2)\2);
  if(t<0 || t>k,error("requested digit outside the supported range"));
  my(step=2^(k-t),lo=fixedSmallCount(d)*f,r=f,done=1,cap=sqrtint(f)+1,Y=min(cap,8));
  my(opts=fixedPadOptions(d,k),attempted=vector(#opts),small=[]);
  while(1,
    my(strip=fixedStripInterval(r,done,Y));r=strip[1];small=concat(small,strip[2]);
    foreach(strip[2],pe,lo*=fixedLocal(pe[1],pe[2],d));
    if(r==1,return([floor(lo/step),Y,0]));
    if(r<(Y+1)^2,return([floor(lo*fixedLocal(r,1,d)/step),Y,0]));
    my(h=logint(r,Y+1),hi=floor(lo*((Y+2)/Y)^h));
    if(floor(lo/step)==hi\step,return([hi\step,Y,0]));
    for(o=1,#opts,if(!attempted[o] && opts[o][1] && Y>=opts[o][1],
      my(c=fixedPadCertificate(f,d,opts[o],small));if(c,return([floor(c/step),Y,2]));
      attempted[o]=1)
    );
    if(f<=65536 && Y>=sqrtnint(f^2,5)+1,return([floor(lo*fixedRemainingLocal(r,d)/step),Y,1]));
    if(Y==cap,error("residual survived full square-root cutoff"));
    done=Y;Y=min(2*Y,cap)
  )
};

fixedPhiSigma(f,t,isSigma) = {
  my(step=2^(logint(f,2)-t),lo=f,r=f,done=1,Y=8);
  while(1,
    my(strip=fixedStripInterval(r,done,Y));r=strip[1];
    foreach(strip[2],pe,
      my(p=pe[1],e=pe[2]);
      lo*=if(isSigma,(p^(e+1)-1)/(p^e*(p-1)),(p-1)/p)
    );
    if(r==1,return(floor(lo/step)));
    if(r<(Y+1)^2,return(floor(lo*if(isSigma,(r+1)/r,(r-1)/r)/step)));
    my(h=logint(r,Y+1),bound=if(isSigma,lo*((Y+1)/Y)^h,lo*(Y/(Y+1))^h));
    if(floor(lo/step)==floor(bound/step),return(floor(lo/step)));
    done=Y;Y*=2
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
  my(extractions=0,arith=0);
  for(n=2,1000,
    my(nF=factor(n),all=vector(matsize(nF)[1],i,[nF[i,1],nF[i,2]]),r=n,done=1);
    foreach([5,13,40,73],Y,
      my(strip=fixedStripInterval(r,done,Y),pieces=select(pe->pe[1]>done && pe[1]<=Y,all));
      if(strip[2]!=pieces || strip[1]*prod(i=1,#pieces,pieces[i][1]^pieces[i][2])!=r,
        error("factorial block extraction ",[r,done,Y,strip,pieces]));
      r=strip[1];done=Y;extractions++
    );
    foreach([0,min(2,logint(n,2)),logint(n,2)],t,
      if(fixedPhiSigma(n,t,1)!=sumdiv(n,q,q)\2^(logint(n,2)-t) ||
         fixedPhiSigma(n,t,0)!=eulerphi(n)\2^(logint(n,2)-t),error("phi/sigma quotient ",[n,t]));
      arith+=2
    )
  );
  print(["factorial block extractions",extractions,"phi and sigma quotients",arith]);
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
  my(pads=0,maxY=0,peak=0,capUsed=0,certs=0);
  foreach([[3,143],[3,187],[11,143],[19,11^2*13]],pair,
    my(d=pair[1],n=pair[2],u=d*n^2,c=fixedReference(n,d),K=8*(logint(u,2)+1)+16);
    my(lo=fixedFirstPad(u,K),hi=fixedFirstPad(u,K+1)-1);
    for(i=0,31,
      my(j=lo+(hi-lo)*(2*i+1)\64,s=1+4*u*j^2,M=u*s^2);
      foreach([0,2,K],t,my(v=fixedMiddleQuotient(M,d,t));
        if(v[1]!=c*s\2^(K-t),error("padded quotient ",[d,n,i,t]));
        pads++;maxY=max(maxY,v[2]);capUsed+=(v[3]==1);certs+=(v[3]==2);peak=max(peak,logint(M,2)+1)
      )
    )
  );
  print(["direct exact standard-pad quotients",pads,"largest index bits",peak,
         "largest trial cutoff",maxY,"toy fallbacks",capUsed,"certified pads",certs]);
  my(compact=0,compactCerts=0,compactPeak=0);
  foreach([[3,143],[3,187],[11,143],[19,11^2*13]],pair,
    my(d=pair[1],n=pair[2],u=d*n^2,K=fixedCompactK(logint(u,2)+1),c=fixedReference(n,d));
    my(lo=sqrtint(sqrtint((2^(2*K)-1)\u)-4*u)+1,hi=sqrtint(sqrtint((2^(2*K+2)-1)\u)-4*u));
    for(i=0,31,
      my(x=lo+(hi-lo)*(2*i+1)\64);while(gcd(x,2*u)!=1,x++);
      my(s=x^2+4*u,M=u*s^2);
      if(logint(M,2)\2!=K,error("compact dyad"));
      foreach([0,2,K],t,
        my(v=fixedMiddleQuotient(M,d,t));
        if(v[1]!=s*c\2^(K-t),error("compact certified quotient ",[d,n,i,t]));
        compact++;compactCerts+=(v[3]==2);compactPeak=max(compactPeak,logint(M,2)+1)
      )
    )
  );
  print(["direct compact-pad quotients",compact,"certified pads",compactCerts,"peak index bits",compactPeak]);
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
