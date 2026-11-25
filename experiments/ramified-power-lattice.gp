\\ Run at the repository root. The lattice receives counts and public polynomials.
read("experiments/hidden-divisor-lattice.gp");

powerCountOracle(m) = {
  my(F=factor(m),d=prod(i=1,matsize(F)[1],F[i,1]^(F[i,2]%2)));
  my(count=if(d==3,1,3*qfbclassno(-d)));
  for(i=1,matsize(F)[1],
    my(p=F[i,1],h=F[i,2]\2);
    count*=p^h+(1-kronecker(-d,p))*(p^h-1)/(p-1)
  );
  count
};

checkRamifiedPowerLattice() = {
  my(p=10007,q=5003,n=p^3*q^2,b=logint(n,2)+1,a=(3*n)%8,e=3,h=(e-1)/2);
  if(min(p,q)<=b^2,error("trial cutoff unexpectedly covers fixture"));
  my(bin=logint(p,2),mass=0,lcmHidden=1,checks=0,indices=List());
  forprime(r=b+1,8*b,
    my(j=lift(Mod(-h-1,r)/e),k=r-1,M=powerCountOracle(a*n^(2*j+1)),D=(p^r-1)/(p-1));
    if(j<1 || j>=r || M%D || gcd(D,lcmHidden)!=1 || M>n^(2*r),error("row bound ",[r,j]));
    mass+=k*bin^2/(logint(M,2)+1);lcmHidden*=D;checks++;listput(indices,j)
  );
  if(mass<=bin+3,error("combined radius misses dyadic bin"));
  my(center=10000,radius=16,dim=14,rs=[2,5,7,11],ts=[5,2,1,1]);
  my(rows=vector(#rs,i,
    my(r=rs[i],j=lift(Mod(-h-1,r)/e),M=powerCountOracle(a*n^(2*j+1)));
    [subst(polcyclo(r),'x,'x+center),M,ts[i],(center-radius)^(r-1)]
  ));
  my(short=hiddenDivisorShortPolynomial(rows,dim,radius));
  my(norm=vecsum(abs(vector(dim,i,polcoef(short,i-1)*radius^(i-1)))));
  my(bound=prod(i=1,#rows,rows[i][4]^rows[i][3]));
  my(primes=select(t->t>1 && n%t==0 && isprime(t),
    apply(w->w+center,hiddenDivisorRoots(short,rows,radius))));
  if(norm>=bound || primes!=[p],error("short polynomial certificate"));
  print(["input bits",b,"prime-index rows",checks,"distinct powers",#Set(Vec(indices)),
         "certified floor(log2 radius)+3",floor(mass),"bin exponent",bin,
         "four-row LLL factor",primes[1],"scaled norm and lower-bound bits",[logint(norm,2)+1,logint(bound,2)+1]]);
};

iferr(checkRamifiedPowerLattice(),err,print(err);quit(1));
