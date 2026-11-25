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
  my(rawProduct=1,primitiveProduct=1,overlaps=0,compositeMass=0,maxBits=0,orders=[],grouped=0);
  for(j=25,50,
    my(r=e*j+h+1,P=2^bin,M=powerCountOracle(a*n^(2*j+1)));
    my(newOrders=setminus(select(k->k>=3,divisors(r)),orders));
    my(raw=1,primitive=1,den=1,d=0);
    foreach(newOrders,k,
      my(value=subst(polcyclo(k),'x,p));
      raw*=value;primitive*=value/gcd(value,k);den*=4*k;d+=eulerphi(k)
    );
    orders=setunion(orders,newOrders);if(#newOrders>1,grouped++);
    my(A=ceil(P^d/den));
    if(gcd(raw,rawProduct)>1,overlaps++);
    if(M%primitive || gcd(primitive,primitiveProduct)!=1 || primitive<A,error("primitive-order row ",[j,r]));
    if(M>n^(2*j+2),error("public modulus exceeded bound"));
    compositeMass+=logint(A,2)^2/(d*(logint(M,2)+1));
    maxBits=max(maxBits,logint(a*n^(2*j+1),2)+1);
    rawProduct*=raw;primitiveProduct*=primitive
  );
  if(!overlaps || !grouped || compositeMass<=bin+3,error("composite radius or overlap fixture failed"));
  print(["all-index rows",26,"rows with multiple orders",grouped,"overlapping full values",overlaps,
         "certified floor(log2 radius)+3",floor(compositeMass),"maximum index bits",maxBits]);
  my(schedules=0);
  foreach([16,32,65],J,
    forstep(v=1,2*J+9,2,
      my(seen=[],degreeMass=0);
      for(j=(J+1)\2,J,
        my(r=v*j+(v+1)/2,ks=setminus(select(k->k>=3,divisors(r)),seen));
        my(d=sum(i=1,#ks,eulerphi(ks[i])));
        if(!setsearch(ks,r) || (v>=J && 2*d<r),error("group degree bound ",[J,v,j]));
        seen=setunion(seen,ks);degreeMass+=d/j
      );
      if(degreeMass<v*J/8,error("summed degree bound ",[J,v]));
      schedules++
    )
  );
  print(["verified grouped degree schedules",schedules]);
};

iferr(checkRamifiedPowerLattice(),err,print(err);quit(1));
