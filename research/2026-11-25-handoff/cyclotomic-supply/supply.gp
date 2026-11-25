\\ gp -q supply.gp
powerSupply(n, k, e, a) = {
  my(x='x, f=polcyclo(k), d=poldegree(f), t=d*e+1, b,
     moduli, h, u, radius, guess, p, hits=0, calls=0);
  if(a%n==0, error("progression requires N not dividing a"));
  if(gcd(n,a)>1, return([gcd(n,a),0,0]));
  h=sum(j=0,d,polcoef(f,j)*n^j*a^(d-j));
  moduli=n*h^e;
  u=lift(Mod(a,moduli)^-1);
  b=1+logint(moduli,2);
  for(i=1, logint(n,2),
    my(P=2^i, A=2^((i-1)*t), w=((i-1)^2*t^2)\b-3);
    radius=if(w>=0,2^min(i,w),0);
    forstep(lo=P,min(2*P-1,n-1),2*radius+1,
      my(center=lo+radius);
      if(radius,
        calls++;
        guess=zncoppersmith(x+center-(u*n%moduli),moduli,radius,A),
        hits++;
        guess=[0]
      );
      foreach(guess,z,
        p=center+z;
        if(p>1 && p<n && n%p==0 && (n/p-a)%subst(f,x,p)^e==0,
          return([p,hits,calls])
        )
      )
    )
  );
  [0,hits,calls]
};

{
  my(x='x);
  foreach([[32869,3,1,1],[20483,3,2,7],[1033,5,2,5]], case,
    my(p=case[1],k=case[2],e=case[3],a=case[4],f=polcyclo(k),
       t=subst(f,x,p)^e,q=a+t,n,A,D,res);
    if(!isprime(p),error("fixture prime"));
    while(!isprime(q),q+=t);
    n=p*q;
    A=n*sum(j=0,poldegree(f),polcoef(f,j)*n^j*a^(poldegree(f)-j))^e;
    D=p*t;
    if(A%D || (n-a*p)%D,error("hidden divisor identity"));
    res=powerSupply(n,k,e,a);
    if(res[1]!=p || res[3]<1,error("failed positive-radius recovery: ",res));
    print([n,k,e,a,p,q,(q-a)/t,res[2],res[3]])
  )
};
