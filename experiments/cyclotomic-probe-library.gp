read("experiments/cyclotomic-multiples.gp");

\\ Retain at least the expected number of primes by fixing one colour at a time.
separatedPrimes(k,X) = {
  my(ps=select(p->(p+1)%k==0,primes([X,2*X])), J=lcm([1..k-1]));
  my(A=vector(#ps,i,Set(Vec(factor(subst(polcyclo(k),x,ps[i]))[,1]))));
  my(B=vector(#ps,i,Set(Vec(factor(ps[i]*(ps[i]^J-1))[,1]))));
  my(conflicts=setintersect(Set(concat(A)),Set(concat(B))));
  my(remaining=[1..#ps],weight=vector(#ps,i,2^-#setintersect(conflicts,setunion(A[i],B[i]))));
  my(mean0=vecsum(weight));
  foreach(conflicts,ell,
    my(gain=sum(i=1,#ps,weight[i]*(!!setsearch(A[i],ell)-!!setsearch(B[i],ell))));
    my(keepA=gain>=0);
    for(i=1,#ps,
      if(setsearch(A[i],ell),weight[i]*=2*keepA);
      if(setsearch(B[i],ell),weight[i]*=2*!keepA)
    )
  );
  remaining=select(i->weight[i],remaining);
  if(#remaining<mean0 || vecmax(weight)!=1,error("conditional expectation"));
  if(#setintersect(Set(concat(vector(#remaining,i,A[remaining[i]]))),
                   Set(concat(vector(#remaining,i,B[remaining[i]])))),error("cross order"));
  print(["separator",k,#ps,#conflicts,mean0,#remaining]);
  vector(#remaining,i,ps[remaining[i]])
};

localAnswer(f,p,k) = {
  my(a=Mod(1,p)*f);
  a==x^poldegree(f) || (poldegree(f)==k && polisirreducible(a))
};

checkLibrary(k,X) = {
  my(ps=separatedPrimes(k,X),h=vector(#ps,i,subst(polcyclo(k),x,ps[i])));
  my(fs=[x^2,x^2-x,(x-1)^2,x^2+1,x^k,x^k-x,x^k-3*x+1,x^k+x+1]);
  \\ Coefficients above the prime range include a reducible fibre and a nilpotent fibre.
  fs=concat(fs,[x^k+ps[1]*x,x^k+ps[1],(x-ps[1])^k]);
  my(total=0,hits=0);
  for(i=1,#ps-1,for(j=i+1,#ps,
    my(p=ps[i],q=ps[j],M=lcm(h[i],h[j]));
    foreach(fs,f,
      my(want=p^localAnswer(f,p,k)*q^localAnswer(f,q,k));
      if(cyclotomicCoefficientGcd(p*q,M,f)!=want,error("literal probe ",[p,q,k,f]));
      total++; hits+=(want==p || want==q)
    )
  ));
  if(!hits,error("need at least one split"));
  print(["powers",k,total,hits])
};
checkUpperList() = {
  my(ps=primes([17,59]), fs=List(), uncovered=List());
  for(i=1,#ps,for(j=1,#ps,if(i!=j,listput(uncovered,[ps[i],ps[j]]))));
  my(rows=Vec(uncovered),initial=#rows);
  forvec(c=vector(3,t,[-4,4]),
    my(f=x^3+Polrev(c),left=List());
    foreach(rows,v,
      my(p=v[1],q=v[2],roots=polrootsmod(f,q));
      my(signs=Set(vector(#roots,t,kronecker(lift(roots[t]),q))));
      if(polisirreducible(f*Mod(1,p)) && setsearch(signs,1) && setsearch(signs,-1),
        my(M=lcm(p^2+p+1,q^2+q+1)*(p*q-2)^3);
        if(cyclotomicCoefficientGcd(p*q,M,f)!=p,error("multiplier-independent probe")),
        listput(left,v)));
    if(#left<#rows,listput(fs,f));
    rows=Vec(left); if(!#rows,break)
  );
  if(#rows,error("uncovered ordered pairs"));
  print(["upper list",#fs,initial])
};
iferr(checkLibrary(3,1000);checkLibrary(5,250);checkUpperList(),E,print(E);quit(1));
