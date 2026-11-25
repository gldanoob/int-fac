\\ Literal projections in real cyclic fields, including dual-order inputs.

element_mod(a,f,t) = Mod(Mod(1,t)*lift(a),f);

frobenius_lifts(f,p) = {
  my(k=poldegree(f), g=Mod(x,f), local=element_mod(g,f,p)^p, sig=0,
     automorphisms=nfgaloisconj(f), iterates=vector(poldegree(f)));
  foreach(automorphisms,h,
    if(element_mod(h,f,p)==local,sig=h;break)
  );
  if(sig==0,error("no Frobenius lift"));
  iterates[1]=g;
  for(i=2,k,iterates[i]=subst(sig,x,iterates[i-1]));
  if(#Set(iterates)!=k || subst(sig,x,iterates[k])!=g,error("orientation"));
  return(iterates)
};

projection(alpha, conjugates, U) = {
  return(prod(i=0,poldegree(U),
    subst(lift(alpha),x,conjugates[i+1])^polcoeff(U,i)));
};

literal_scalar_gcd(n, exponent, f) = {
  my(power=liftall(Mod(Mod(1,n)*x,f)^exponent));
  return(gcd(concat([n],vector(poldegree(f)-1,i,polcoeff(power,i)))));
};

find_probe(k,f,p,q,U,conjugates,wanted) = {
  my(g=Mod(x,f),r=polrootsmod(f,q)[1],
     ordered=vector(k,i,subst(lift(conjugates[i]),x,r)));
  for(radius=1,4,
    forvec(c=vector(k,i,[-1,1]),
      if(!c[k]&&!c[k-1]&&!c[k-2]&&radius>1,next);
      my(alpha=radius*g+Mod(Polrev(c),f), Nm=abs(norm(alpha)), local, beta, signs);
      if(Nm==0||gcd(Nm,p*q)>1,next);
      local=element_mod(alpha,f,p)^((p^k-1)/2);
      if(wanted && local!=wanted,next);
      beta=projection(alpha,conjugates,U);
      signs=vector(k,i,kronecker(lift(subst(lift(beta),x,ordered[i])),q));
      if(#Set(signs)!=2||setsearch(Set(signs),0),next);
      return([alpha,beta,signs,liftall(local)]);
    );
  );
  error(["no projected probe",k,wanted]);
};

fixture(k,ell) = {
  my(groupgen=znprimroot(ell), f=galoissubcyclo(ell,[lift(groupgen^k)]),
     U=(x^k-1)/polcyclo(k), p=0, q=0, N, M, D, C);
  if(poldegree(f)!=k || polsturm(f)!=k,error("cyclic field"));
  forprime(t=101,2000,
    if(polisirreducible(Mod(1,t)*f),p=t;break)
  );
  forprime(t=p+1,2*p,
    if(#polrootsmod(f,t)==k,q=t;break)
  );
  if(!p||!q,error("missing prime pair"));
  C=frobenius_lifts(f,p);
  N=p*q;
  M=lcm([polcyclo(k,p),polcyclo(k,q),q-1]);
  D=M>>valuation(M,2);
  foreach(if(k==6,[0],[1,-1]), wanted,
    my(res=find_probe(k,f,p,q,U,C,wanted), alpha=res[1], beta=res[2], signs=res[3],
       A=abs(norm(alpha))^sum(i=0,poldegree(U),max(0,-polcoeff(U,i))),
       gamma=A*beta, minimal=minpoly(gamma), local=element_mod(beta,f,p)^D, b, mult, split);
    if(element_mod(beta,f,p)^polcyclo(k,p)!=1,error("projected covered order"));
    if(k==6 && local!=1,error("odd index order"));
    if(k!=6 && local!=wanted,error(["even index scalar sign",wanted,local]));
    if(denominator(lift(gamma))!=1 || gcd(A,N)!=1,error("denominator clear"));
    if(literal_scalar_gcd(N,D,minimal)!=p ||
       literal_scalar_gcd(N,M,minimal)!=N,error("literal gcd with dual exponent"));
    b=polcyclo(k,p); b>>=valuation(b,2);
    if(literal_scalar_gcd(N,b,minimal)!=p,error("literal gcd with bare order"));
    mult=p^2*q^3*nextprime(q+1);
    split=literal_scalar_gcd(mult,D,minimal);
    if(split%p || split%q==0 || split<=1 || split>=mult,
      error("literal gcd with additional prime powers"));
    print(["index",k,"field",f,"p,q",p,q,"U",U,"alpha",lift(alpha),
           "(alpha/p)",res[4],"beta^odd at p",liftall(local),"q signs",signs,
           "minpoly",minimal,"M",M,"odd/full gcd",p,N,"non-squarefree input and gcd",mult,split]);
  );
};

iferr({
  fixture(4,17);
  fixture(6,13);
  fixture(8,17);
},err,print(err);quit(1));
