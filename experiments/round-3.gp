read("experiments/round-2.gp");
read("experiments/triprime.gp");

\\ For squarefree n with three prime factors, decode the cubic using two
\\ supplied sums. The coefficient acquisition cost is external to this test.
triprimePolynomial(n,s1,squareSum) = {
  my(S=s1-n-1, disc=4*squareSum-3*S^2, r);
  if(disc<0 || !issquare(disc,&r), error("inconsistent divisor sums"));
  my(e1=n-1+(S-r)/2);
  'x^3-e1*'x^2+(S-e1)*'x-n
};

checkTriprimes() = {
  my(ps=primes([2,53]), count=0);
  for(i=1,#ps,for(j=i+1,#ps,for(k=j+1,#ps,
    my(p=ps[i],q=ps[j],r=ps[k],n=p*q*r,s1=sigma(n),s3=sigma(n,3));
    my(f=triprimePolynomial(n,s1,sigma(n^2)), S=s1-n-1, T=n+1);
    if(f!=('x-p)*('x-q)*('x-r),error("cubic mismatch"));
    if(4*(s3/s1)-4*T^2+4*T*S-S^2!=3*(S-2*(p+q+r))^2,error("same-index norm"));
    count++
  )));
  count
};

checkBoxJoins() = {
  my(n=541*701, K=1, counts=List());
  for(d=1,5,
    K=lcm(K,4^d-1);
    my(rows=Map(), count=0);
    for(x=512,639,for(y=640,767,
      if((x*y-n)%K==0,count++;mapput(rows,[x%K,y%K],1))
    ));
    listput(counts,[K,count,#rows])
  );
  my(out=Vec(counts));
  if(out!=[[3,3655,2],[15,586,8],[315,22,22],[5355,2,2],[1826055,1,1]],error("box join"));
  out
};

checkClassInterval() = {
  my(D=-56444,Q=5000,weighted=0,total=0,prefix=0);
  for(n=2,2*Q-1,
    if(n>=Q,my(w=n*log(n)); weighted+=w*prefix;total+=w);
    if(isprime(n),prefix-=log(1-kronecker(D,n)/n))
  );
  my(H=sqrt(-D)*exp(weighted/total)/Pi);
  my(E=(6.593*log(-D)+19.321)/(sqrt(Q)*log(Q))+log(-D)/((Q-1)*log(Q)));
  my(g=qfbred(qfbprimeform(D,3)), h=g^(2^16));
  my(out=[ceil(H*exp(-E)),floor(H*exp(E)),select(m->h^m==g^0,[17,19,21]),Vec(g^76)]);
  if(out!=[131,176,[19],[103,0,137]],error("class interval"));
  out
};

checkLPFibers() = {
  my(g=qfbprimeform(-55,2), sums=vector(5,i,
    my(r=5+i,f=Vec(g^r),t=-valuation(f[1],2)*if(f[2]%4==1,1,-1));
    r+t));
  if(sums!=[8,8,8,8,12] || Vec(g^6)!=[4,3,4],error("relation lifts"));
  for(k=1,12,my(a=2^k,h=qfbprimeform(1-4*a^2,2)); if(h^k!=Qfb(a,1,a) || h^(-k)!=h^k,error("cutoff")));
  sums
};

\\ Return whether any of z^1,...,z^h equals one at a prime factor of n.
\\ Product and remainder trees are defined in round-2.gp.
prefixOrderHit(n,z,h) = {
  my(s=sqrtint(h), blocks=h\s, tail=h%s, roots=vector(s), b=z^-1);
  for(i=1,s,roots[i]=b;b/=z);
  my(poly=productTree(roots,1,s)[1], points=vector(blocks), jump=z^s, g=Mod(1,n));
  for(i=1,blocks,points[i]=g;g*=jump);
  my(vals=List());
  treeValues(poly,productTree(points,1,blocks),~vals);
  if(gcd(lift(prod(i=1,#vals,vals[i])),n)>1,return(1));
  for(i=1,tail,g*=z;if(gcd(lift(g)-1,n)>1,return(1)));
  0
};

splitGlobal(n,a,M) = {
  if(n<=2 || M<1 || gcd(a,n)!=1 || Mod(a,n)^M!=1,error("expected a positive global relation"));
  my(c=gcd(M,n-1),z=Mod(a,n)^c);
  if(z==1,return(1));
  my(lo=1,hi=sqrtint(M/c));
  while(lo<hi,my(mid=(lo+hi)\2);if(prefixOrderHit(n,z,mid),hi=mid,lo=mid+1));
  my(d=gcd(lift(z^lo)-1,n));
  if(d<=1 || d==n,error("promised distinct odd semiprime required"));
  d
};

checkGlobalOrders() = {
  my(tests=0, hits=0);
  forprime(p=3,47,forprime(q=p+1,47,
    my(n=p*q);
    for(a=2,39,if(gcd(a,n)!=1,next());
      my(o=znorder(Mod(a,n)));
      foreach([1,2,5,12],j,
        my(M=j*o, z=Mod(a,n)^gcd(M,n-1), d=splitGlobal(n,a,M));
        if(z==1,if(d!=1,error("miss")),if(d!=p && d!=q,error("invalid divisor"));hits++);
        tests++
      )
    )
  ));
  if(splitGlobal(1333,3,210)!=31,error("global example"));
  [tests,hits]
};

checkMixedRoots() = {
  my(n=479348657, D=-4*n, Q=2^(logint(-D,2)+1), ps=[167,653]);
  my(g=vector(2,i,qfbred(qfbprimeform(D,ps[i]))), h=vector(2,i,g[i]^Q));
  my(target=[h[2]/h[1],(h[1]*h[2])^-1], powers=h, j=0);
  while(powers!=target && j<6,powers=vector(2,i,powers[i]^2);j++);
  if(powers!=target,error("mixed collision"));
  my(k=2^j+1,d=matsnf([k,-1;1,k])[1], M=d>>valuation(d,2));
  my(c=lift(Mod(Q^2,M)^-1),z=vector(2,i,h[i]^c),w=vector(2,i,g[i]/z[i]^Q));
  for(i=1,2,if(z[i]^(Q^2)!=h[i] || h[i]==g[i]^0,error("projection")));
  my(out=[j,d,M,gcd(Vec(w[2])[1],n)]);
  if(out!=[6,4226,2113,1009],error("mixed root witness"));
  out
};

\\ Determine the worst first hit across all phases for the blind priority schedule.
blindStrideCount(events,h) = {
  my(covered=vector(h), count=0, used=Map(), probes=1);
  foreach(events,e,covered[e+1]=1;count++);
  for(priority=1,2*h,
    fordiv(priority,w,
      my(r=sqrtint(4*w+1));
      if(r*r!=4*w+1 || r<3,next());
      my(j=(r-3)/2,offset=(priority/w)*2^j);
      if(mapisdefined(used,offset),next());
      mapput(used,offset,1);probes++;
      foreach(events,e,
        my(i=1+(e-offset)%h);
        if(!covered[i],covered[i]=1;count++)
      );
      if(count==h,return(probes))
    )
  );
  error("stride 1 should cover the orbit")
};

checkBlindStrides() = {
  my(events=archivedEvents(), out=vector(2,i,blindStrideCount(events[i],198850)));
  if(out!=[20322,5090],error("blind stride schedule"));
  out
};


\\ Columns r,s are two independent exact relations for the two unit bases.
splitRankTwo(n,a,b,r,s) = {
  my(f=v->Mod(a,n)^v[1]*Mod(b,n)^v[2]);
  if(n%2==0 || gcd(a*b,n)!=1 || !matdet(Mat([r~,s~])) || f(r)!=1 || f(s)!=1,error("invalid relations"));
  while(1,
    my(changed=0, words=[r,s,r+s]);
    for(i=1,3,
      my(u=words[i]);
      if(u[1]%2 || u[2]%2,next());
      my(v=u/2,z=lift(f(v)));
      if(z!=1 && z!=n-1,return(gcd(z-1,n)));
      if(z==1,if(i==2,s=v,r=v);changed=1;break())
    );
    if(!changed,return(1))
  )
};

checkRankTwo() = {
  my(n=65, hits=0, checked=0);
  for(a=1,n-1,if(gcd(a,n)!=1,next());
    for(b=1,n-1,if(gcd(b,n)!=1,next());
      my(oa=znorder(Mod(a,n)),ob=znorder(Mod(b,n)),d=splitRankTwo(n,a,b,[oa,ob],[oa,-ob]), expect=0);
      my(x=Mod(a,n)^0);
      for(i=0,oa-1,my(y=x);for(j=0,ob-1,if(y^2==1 && y!=1 && y!=-1,expect=1);y*=Mod(b,n));x*=Mod(a,n));
      if((d>1)!=expect || n%d || d==n,error("rank two mismatch"));checked++;hits+=(d>1)
    )
  );
  if(splitRankTwo(n,8,18,[4,4],[4,-4])!=13,error("mixed relations"));
  [checked,hits]
};
