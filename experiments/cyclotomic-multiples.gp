\\ Search one finite coefficient box. A successful result records the polynomial.
splitCyclotomicBox(n,m,k,height) = {
  if(n<3 || n%2==0 || m<1 || k<2 || height<0,error("invalid cyclotomic box"));
  my(d=m>>valuation(m,2));
  for(degree=2,k,
    forvec(coeff=vector(degree,i,[-height,height]),
      my(f=x^degree+Polrev(coeff), power=liftall(Mod(Mod(1,n)*x,f)^d));
      my(g=gcd(concat([n],vector(degree-1,i,polcoef(power,i)))));
      if(1<g && g<n,return([g,f]))
    )
  );
  [1,0]
};

checkCyclotomicBoxes() = {
  \\ Each row gives [index, covered prime, cofactor, extra multiplier, first degree].
  my(cases=[[3,5,17,2^8*307,3],[4,11,11*17,2^8,4],
            [5,5,7,16,5],[6,5,11,64*111,6]]);
  foreach(cases,c,
    my(k=c[1],p=c[2],n=p*c[3],m=c[4]*subst(polcyclo(k),x,p));
    my(hit=splitCyclotomicBox(n,m,k,1));
    if(hit[1]!=p || poldegree(hit[2])!=c[5],error("bounded cyclotomic search ",c));
    if(k==6 && liftall(Mod(Mod(1,n)*x,hit[2])^m)!=1,
      error("expected the full exponent to give the identity at both primes"))
  );
  if(splitCyclotomicBox(85,2^8*31*307,2,1)!=[1,0],error("unexpected quadratic split"));
  if(splitCyclotomicBox(17,307,3,1)!=[1,0],error("spurious prime split"));
  if(splitCyclotomicBox(14489*14503,14489^2+14489+1,3,2)!=[1,0],
    error("expected the whole height-two box to miss"));
  my(p=5667905425817027078359952011480794959255287699625520230463791431884359);
  my(q=p+168,m=p^2+p+1);
  if(!isprime(p) || !isprime(q) || gcd(m,q*(q^6-1))!=1,
    error("height-three prime certificate"));
  if(splitCyclotomicBox(p*q,m,3,3)!=[1,0],error("expected the whole height-three box to miss"));
  if(splitCyclotomicBox(p*q,m,3,4)!=[p,x^3-4*x^2-3*x-4],error("height-four witness"));
  \\ Count sign vectors whose cyclotomic projection is constant.
  for(k=3,10,
    my(u=(x^k-1)/polcyclo(k),ones=(x^k-1)/(x-1),constant=0);
    for(mask=0,2^k-1,
      my(v=Polrev(vector(k,j,bittest(mask,j-1))));
      my(w=liftall(lift(Mod(Mod(1,2)*v*u,x^k-1))));
      if(w==0 || w==ones,constant++)
    );
    if(constant!=2^(k-eulerphi(k)+(hammingweight(k)==1)),error("sign projection at index ",k))
  );
  #cases
};
