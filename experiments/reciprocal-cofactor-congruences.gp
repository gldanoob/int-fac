\\ Finite short-vector replay. The splitter receives the integer, public polynomials and search bounds.
read("experiments/hidden-divisor-lattice.gp");

reciprocalMonic(f,M) = {
  my(X=variable(f),d=poldegree(f),inv=lift(Mod(pollead(f),M)^-1));
  X^d+sum(j=0,d-1,(inv*polcoef(f,j)%M)*X^j)
};

reciprocalMultiplicity(dim,A,M,d) = {
  my(t=0);
  while(d*(t+1)<=dim && M^(d*(t+1))<=A^dim,t++);
  t
};

reciprocalFixtureSplit(N,F,G,r,s,firstBin,lastBin,dim) = {
  my(X=variable(F),d=poldegree(F),e=poldegree(G),M1=N^(d+r),M2=N^s);
  my(rev=sum(i=0,d,polcoef(F,i)*N^i*X^(d-i)));
  my(f1=reciprocalMonic(rev,M1),f2=reciprocalMonic(G,M2),windows=0);
  for(k=firstBin,lastBin,
    my(P=2^k,R=max(1,P\4));
    forstep(lo=P,2*P-1,2*R+1,
      my(c=lo+R,Q=ceil(N/(c+R)),A1=lo^(d+r),A2=Q^s);
      my(rows=[[subst(f1,X,X+c),M1,reciprocalMultiplicity(dim,A1,M1,d),A1],
               [subst(f2,X,X+c),M2,reciprocalMultiplicity(dim,A2,M2,e),A2]]);
      my(short=hiddenDivisorShortPolynomial(rows,dim,R),norm=vecsum(abs(vector(dim,i,polcoef(short,i-1)*R^(i-1)))));
      my(bound=A1^rows[1][3]*A2^rows[2][3]);
      windows++;
      foreach(hiddenDivisorRoots(short,rows,R),offset,
        my(x=c+offset);
        if(x<=1 || x>=N || N%x,next);
        my(y=N/x);
        if(subst(F,X,y)%x^r==0 && subst(G,X,x)%y^s==0,
          return([x,y,c,R,norm,bound,windows,vecmax(abs(Vec(short)))])
        )
      )
    )
  );
  []
};

checkReciprocalCofactors() = {
  my(X='x,F=X^2+X+13,G=X^2+X+5,N=250112689);
  my(answer=reciprocalFixtureSplit(N,F,G,1,1,8,13,18));
  if(#answer<8 || answer[1]!=2207 || answer[2]!=113327 || answer[5]>=answer[6],
    error("uncertified asymmetric quadratic fixture ",answer));
  if(!polisirreducible(F) || !polisirreducible(G) || gcd(polcoef(F,0),N)!=1,
    error("fixture should have irreducible different-constant quadratics"));
  print(["proper split",answer[1..2],"ratio exceeds",answer[2]\answer[1],
         "bin windows tried",answer[7],"center and radius",answer[3..4],
         "strict scaled norm and bound",[answer[5],answer[6]]]);

  my(exact=0,defective=0);
  for(x=2,60,for(y=2,80,
    if(gcd(x,y)>1,next);
    foreach([[X+1,X^2+3,1,1],[X^2+X+1,X^2-X+1,1,1],[X^2+X+3,X^3+2,2,1],
             [X^3-3*X-5,7*X^2-2*X+3,1,2]],data,
      my(f=data[1],g=data[2],r=data[3],s=data[4],d=poldegree(f),n=x*y);
      if(gcd(n,polcoef(f,0)*pollead(g))>1,next);
      my(D1=x^d*gcd(x^r,subst(f,X,y)),D2=gcd(y^s,subst(g,X,x)));
      my(m1=n^(d+r),m2=n^s,rev=sum(i=0,d,polcoef(f,i)*n^i*X^(d-i)));
      if(subst(reciprocalMonic(rev,m1),X,x)%D1 || subst(reciprocalMonic(g,m2),X,x)%D2 ||
         gcd(D1,D2)>1 || m1%D1 || m2%D2,error("hidden divisors ",[x,y,data]));
      if(D1==x^(d+r) && D2==y^s,exact++,defective++)
    )
  ));
  print(["exact and deficient reverse-row checks",exact,defective]);
  my(smallPrimes=1,localChecks=0,rough=0,family=0);
  forprime(ell=2,101,
    my(roots=sum(t=0,ell-1,(t*(t^2+t+1)*(t^2+t-1))%ell==0));
    if(roots>=ell || (ell>5 && roots!=3+kronecker(-3,ell)+kronecker(5,ell)),
      error("local sieve factor ",[ell,roots]));
    smallPrimes*=ell;localChecks++
  );
  forstep(t=1001,9999,2,
    my(x=t^2+t+1,y=t*(t^2+t-1),n=x*y);
    if(gcd(x,y)>1 || (y^2-2*y+4)%x || (x-1)*(x-2)%y || sqrtnint(n,5)!=t,
      error("parametric reciprocal pair ",t));
    if(gcd(n,smallPrimes)==1,rough++);family++
  );
  if(!rough,error("no rough member of finite family"));
  print(["parametric products",family,"surviving primes through 101",rough,"sieve factor checks",localChecks]);
};

iferr(checkReciprocalCofactors(),err,print(err);quit(1));
