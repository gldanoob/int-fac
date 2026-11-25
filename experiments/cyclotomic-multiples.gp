cyclotomicCoefficientGcd(n,d,f) = {
  my(power=liftall(Mod(Mod(1,n)*x,f)^d));
  gcd(concat([n],vector(poldegree(f)-1,i,polcoef(power,i))));
};

\\ Search one finite coefficient box. A successful result records the polynomial.
splitCyclotomicBox(n,m,k,height) = {
  if(n<3 || n%2==0 || m<1 || k<2 || height<0,error("invalid cyclotomic box"));
  my(d=m>>valuation(m,2));
  for(degree=2,k,
    forvec(coeff=vector(degree,i,[-height,height]),
      my(f=x^degree+Polrev(coeff),g=cyclotomicCoefficientGcd(n,d,f));
      if(1<g && g<n,return([g,f]))
    )
  );
  [1,0]
};

checkCubicScalarModel(p,q,height,expectedHits) = {
  my(n=p*q,m=p^2+p+1,hits=0);
  if(!isprime(p) || !isprime(q) || p%3!=1 || gcd(m,q*(q^6-1))!=3 ||
     min(p,q)<=height^2+height,error("cubic scalar model assumptions"));
  for(d=2,3,
    forvec(c=vector(d,j,[-height,height]),
      my(f=x^d+Polrev(c),g=cyclotomicCoefficientGcd(n,m,f));
      my(inert=d==3 && (c[2] || c[3]) && #polrootsmod(f,p)==0);
      if((inert && g!=p) || (!inert && g!=1 && g!=n),error("cubic scalar model ",f));
      if(g==p,hits++)
    )
  );
  if(hits!=expectedHits,error("cubic scalar model count ",hits));
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
  foreach([[2,2,367,373],[4,1,211,223],[6,1,211,223],[8,1,227,233]],v,
    my(k=v[1],h=v[2],p=v[3],q=v[4],m=subst(polcyclo(k),x,p));
    if(!isprime(p) || !isprime(q) || q<=p || q>2*p ||
       splitCyclotomicBox(p*q,m,k,h)!=[1,0],error("balanced even-index miss ",v)));
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
  p=24763102584321751944268821159635694704503772729308318972897810337966384138507108937879503989045648329929045593283754372269849516295353301697542889679; q=p+110; m=p^2+p+1;
  if(!isprime(p) || !isprime(q) || gcd(m,q*(q^6-1))!=1,
    error("height-four prime certificate"));
  if(splitCyclotomicBox(p*q,m,3,4)!=[1,0],error("expected the whole height-four box to miss"));
  if(splitCyclotomicBox(p*q,m,3,5)!=[p,x^3-4*x^2-5*x-5],error("height-five witness"));
  p=123733; q=123737;
  if(#polrootsmod(x^3-2,p)!=0,error("expected an inert pure cubic"));
  checkCubicScalarModel(p,q,2,0);
  checkCubicScalarModel(p,q,3,56);
  p=124855102398854570831177532388275947679201618458733020317118446340180791; q=p+16;
  checkCubicScalarModel(p,q,3,0);
  checkCubicScalarModel(p,q,4,44);
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

\\ Full literal replay of the paired prime fixture, run separately from the short suite.
checkPairedCubicBox() = {
  my(p=6084388588251393175949014831974809464878988981873524433296636149705472126228033846765094966948306381241202554123411329885625010620107179169204903755828305152002656663883006164524890783784495797287893897299470691099307821589062112551267917849389881473232572705776810417034411846396054733096171549395692124907933051518339601012116141589912350864829150453272222185860216041431078831);
  my(q=4704869673295731713181971977184059697407460815763858831161872607085570402482602581183078166359659999593227930833501443872769517591);
  my(n=p*q,m=p^2+p+1,hits=0);
  if(!isprime(p) || !isprime(q) || p%3!=1 || q%3!=1 ||
     m%(q^2+q+1) || gcd(m,q*(q^2-1))!=3,error("paired prime assumptions"));
  if(splitCyclotomicBox(n,m,3,4)!=[1,0],error("paired height-four split"));
  if(splitCyclotomicBox(n,m,3,5)!=[q,x^3-4*x^2-5*x-5],error("paired height-five witness"));
  forvec(c=vector(3,i,[-4,4]),
    if(c[2] || c[3],
      my(f=x^3+Polrev(c),a=#polrootsmod(f,p)==0,b=#polrootsmod(f,q)==0);
      if(a!=b,error("paired inertness mismatch ",f));
      hits+=a));
  if(hits!=78,error("paired inertness count ",hits));
  hits
};

checkDualCubicHeightFive() = {
  my(p=508961741223076646327831254220359177129733378337682010159415812572815148962965545641339938825691409335536493976781107341750834152234854509376810751);
  my(q=561758698292688217113428090639547348333634156756244687775200810868194329340493471143867703613714392797661849741193872207506873581717354063386196751);
  my(hp=p^2+p+1,hq=q^2+q+1,m=lcm(hp,hq),n=p*q,hits=0);
  if(!isprime(p) || !isprime(q) || p>=q || q>=2*p || gcd(hp,hq)!=13 ||
     gcd(m,p*(p^2-1)*q*(q^2-1))!=1,error("dual-order primes or exponents"));
  if(splitCyclotomicBox(n,m,3,5)!=[1,0],error("dual-order height-five split"));
  if(splitCyclotomicBox(n,m,3,6)!=[p,x^3+3*x^2-6*x-6],error("dual-order first witness"));
  forvec(c=vector(3,i,[-5,5]),
    my(f=x^3+Polrev(c),a=polisirreducible(Mod(1,p)*f),b=polisirreducible(Mod(1,q)*f));
    if(a!=b,error("dual-order inertness mismatch ",f));hits+=a);
  if(hits!=178,error("dual-order inertness count ",hits));
  hits
};

checkCyclicCubicProjection() = {
  my(f=x^3+x^2-2*x-1,beta=Mod(x^2-2,f)/Mod(x,f),g=minpoly(beta));
  if(g!=x^3-3*x^2-4*x-1 || norm(beta)!=1 || poldisc(g)!=49,error("cyclic projection"));
  my(roots=polrootsmod(f,13),signs=Set(apply(t->kronecker(lift(subst(lift(beta),x,t)),13),roots)));
  if(!polisirreducible(Mod(1,5)*g) || signs!=[-1,1],error("projected local signs"));
  foreach([1,2,3,5,13,31,2^20*3^10*31*157],a,my(m=31*a);
    if(cyclotomicCoefficientGcd(65,m>>valuation(m,2),g)!=5,error("projected gcd")));
  g
};
