\\ Load from the repository root with read("experiments/lucas-carmichael.gp").
\\ pPlusOneSplit(n,M) returns one proper divisor, or 1 for a prime.
\\ pPlusOneFactors(N) uses M=N+1 throughout. checkLucasCarmichael() runs the fixtures.

\\ Let w=(1+sqrt(-ell))/2. Its norm form is Q(a,b)=a^2+ab+c*b^2.
\\ A primitive representation of r^h generates one of the two prime ideals
\\ above r raised to h: divisibility by both would make r divide both a and b.
lcGamma(n,ell,r,h) = {
  my(c=(ell+1)/4, Q=Qfb(1,1,c), v=qfbsolve(Q,Mat([r,h])), normAlpha=r^h);
  if(#v!=2 || gcd(v)!=1 || qfeval(Q,v)!=normAlpha, error("bad generator at ",[ell,r,h]));
  my(alpha=Mod(Mod(1,n)*(v[1]+v[2]*'x),'x^2-'x+c));
  alpha^2 / Mod(normAlpha,n)   \\ alpha/bar(alpha)
};

\\ At exponent oddpart(M)*2^j, d contains exactly the prime powers
\\ p^k | n for which z=1 mod p^k. A hit may include only part of p^v_p(n).
lcChain(n,M,gamma) = {
  my(s=valuation(M,2), z=gamma^(M>>s));
  for(j=0,s,
    my(delta=liftall(z-1), d=gcd([n,polcoef(delta,0),polcoef(delta,1)]));
    if(d>1, return(if(d<n,d,1)));   \\ once z=1 mod n, all later gcds equal n
    if(j<s, z=z^2)
  );
  1
};

\\ Suppose p+1 | M for one unknown odd p | n. For a different odd q | n,
\\ choose a prime ell=3 mod 4 with p,q inert in Q(sqrt(-ell)). Frobenius conjugates alpha,
\\ so gamma^(t+1)=1 and gamma^((t+1)/2)=(r/t)^h at t=p,q (Euler's criterion
\\ applied to Norm(alpha)). Genus theory gives odd h for prime discriminant -ell.
\\ Choose split r with (r/t)=-1 at the larger v_2(t+1) (either on a tie)
\\ and +1 at the other. The local orders then have different 2-adic valuations.
\\ The chain reaches 1 at p. If it also reaches 1 at q, the first such steps
\\ differ. In either case some gcd contains exactly one of p,q, even for squareful n.
\\
\\ These choices are for the proof. CRT gives nonempty sign cosets of index
\\ at most 8 modulo 4pq for ell and 4*ell*p*q for r. Under Dirichlet GRH the
\\ least primes in them are O(log^2 n) (Lamzouri-Li-Soundararajan, Thm. 1.4,
\\ https://arxiv.org/abs/1309.3595). Doubling the search box reaches that pair.
\\ For a polynomial implementation, count reduced forms |b|<=a<=sqrt(ell/3)
\\ with the usual boundary ties. This also bounds h by O(ell). Find a root of
\\ -ell mod r by trial and Hensel-lift to R=r^h. Take an odd lift B of the root.
\\ The form [R,B,(B^2+ell)/(4R)] is the h-th power ideal's form. Gauss reduction
\\ takes it to Q; transporting (1,0) by the inverse basis change represents R
\\ primitively on Q. All coefficients have polynomial bit length in log n.
\\ Trial division suffices for the small primes, AKS and integer roots for n.
\\ Each pair needs O(log M) modular products. GP uses class-number, form and
\\ primality routines below. The time bound assumes the stated promise on M.
pPlusOneSplit(n,{M=n+1}) = {
  if(type(n)!="t_INT" || n<2 || type(M)!="t_INT" || M<1,
    error("expected n >= 2 and M >= 1, both integers"));
  if(isprime(n), return(1));
  if(n%2==0, return(2));
  my(root);
  if(ispower(n,,&root), return(root));

  my(bound=8);
  while(1,
    forprime(ell=3,bound,
      if(ell%4!=3, next);
      if(n%ell==0, return(ell));
      my(h=qfbclassno(-ell,1));
      if(h%2!=1, error("even class number at ",ell));
      forprime(r=3,bound,
        if(kronecker(-ell,r)!=1, next);
        if(n%r==0, return(r));
        my(d=lcChain(n,M,lcGamma(n,ell,r,h)));
        if(d>1, return(d))
      )
    );
    bound*=2
  )
};

\\ Complete under a common multiple of all p+1. Both children inherit the
\\ original M, including when d and n/d have a common prime divisor.
pPlusOneFactors(n,{M=n+1}) = {
  my(d=pPlusOneSplit(n,M));
  if(d==1, return([n]));
  vecsort(concat(pPlusOneFactors(d,M),pPlusOneFactors(n/d,M)))
};

checkLucasCarmichael() = {
  foreach([399,935,2015,60059,81719,588455],n,
    my(P=pPlusOneFactors(n));
    if(#P<2 || #Set(P)!=#P || vecprod(P)!=n, error("LC factorization at ",n));
    foreach(P,p, if(!isprime(p) || (n+1)%(p+1), error("LC criterion at ",[n,p])));
    print("LC n=",n," M=",n+1," factors=",P)
  );

  my(d=lcChain(935,936,lcGamma(935,3,7,1)));
  if(d!=85, error("composite chain gcd at 935: ",d));
  print("n=935 ell=3 r=7 chain gcd=",d);

  \\ For this norm-7 generator, at exponent 15 the two separate gcds are 17 and 5.
  my(w=Mod(Mod(1,85)*'x,'x^2-'x+1), gamma=(2+w)^2/Mod(7,85));
  if(lcChain(85,15,gamma)!=1, error("spurious single-coordinate hit"));

  my(n=24863, P=pPlusOneFactors(n), d=pPlusOneSplit(n));
  if(P!=[23,23,47] || d!=1081 || gcd(d,n/d)!=23, error("squareful split at ",n));
  print("squareful n=",n," M=",n+1," gcd=",d," factors=",P);

  \\ Of 61+1 and 67+1, only 67+1 divides 204. The witness for ell=23 uses the nonprincipal prime
  \\ above 3, with norm 3^3 for its principal cube. The hit is at the last step.
  my(n=4087, M=204, h=qfbclassno(-23,1), g=lcGamma(n,23,3,h));
  if(h!=3 || n!=61*67 || M%(67+1) || M%(61+1)==0, error("one-prime promise fixture"));
  foreach([61,67],p,
    my(localGamma=lcGamma(p,23,3,h));
    if(kronecker(-23,p)!=-1 || localGamma*conj(localGamma)!=1 ||
       localGamma^((p+1)/2)!=kronecker(3,p), error("local order identity at ",p))
  );
  if(lcChain(n,M/2,g)!=1 || lcChain(n,M,g)!=67 || pPlusOneSplit(n,M)!=67,
    error("terminal chain gcd at ",[n,M]));
  print("one-prime promise n=",n," M=",M," ell=23 r=3 h=",h," chain gcd=67")
};

\\ Removing g^2 leaves two coprime children with exactly the parent's odd valuations.
oddValuationPrimes(n,M) = {
  if(issquare(n),return([]));
  if(isprime(n),return([n]));
  my(d=pPlusOneSplit(n,M), e=n/d, g=gcd(d,e));
  concat(oddValuationPrimes(d/g,M),oddValuationPrimes(e/g,M))
};

factorWithSigma(n,oracle) = {
  if(type(n)!="t_INT" || n<1,error("expected a positive integer"));
  my(answer=List(), weight=1);
  if(n%2==0,my(e=valuation(n,2));listput(answer,[2,e]);n=n>>e);
  while(n>1,
    my(root);
    if(!issquare(n,&root),
      my(P=if(isprime(n),[n],oddValuationPrimes(n,oracle(n))));
      if(!#P,error("nonsquare has no recovered odd valuation"));
      foreach(P,p,
        my(e=valuation(n,p));
        if(e%2!=1,error("invalid odd-valuation prime"));
        listput(answer,[p,e*weight]); n=n/p^e
      );
      if(!issquare(n,&root),error("expected square remainder"))
    );
    n=root; weight*=2
  );
  vecsort(Vec(answer))
};

lcTestSigma(m) = { listput(lcQueryLog,m); sigma(m) };

checkSigmaQueries() = {
  local(lcQueryLog);
  my(inputs=[1,64,935,23^2*47,3^3*5^6*7^4*11^8,2^5*37^6*113^12,101^2*107^2*151^2]);
  foreach(inputs,n,
    lcQueryLog=List();
    my(maxCalls=if(n==1,0,1+logint(logint(n,2),2)));
    my(F=factorWithSigma(n,lcTestSigma));
    my(expected=factor(n));
    if(#lcQueryLog>maxCalls || F!=vector(matsize(expected)[1],i,[expected[i,1],expected[i,2]]),error("divisor-sum oracle at ",n))
  );
  #inputs
};
