\\ Run from the repository root. The decoder takes polynomial lists and N.
read("experiments/hidden-divisor-lattice.gp");

affineSupplyRow(k,slopes,i) = {
  my(z='z,x='x,a=slopes[i],t=#slopes);
  my(H=z*prod(j=1,t,if(i==j,1,slopes[j]*z+a-slopes[j])));
  my(Q=polresultant(polcyclo(k,z),x-H,z));
  if(subst(Q,x,H)%polcyclo(k,z)!=0,error("resultant identity"));
  subst(Q,x,a^(t-1)*x)
};

recoverSupplyPrimes(N,indices,menus,dim,R) = {
  my(x='x,t=#indices+1,b=sqrtnint(N,t),P=max(2,b\2),found=Set(),calls=0);
  my(limits=vector(#menus,j,[1,#menus[j]]));
  forvec(choice=limits,
    my(M=vector(#menus,j,abs(subst(menus[j][choice[j]],x,N))));
    if(vecmin(M)<2,next);
    forstep(lo=P,2*b+2,2*R+1,
      my(c=lo+R,f=x+c,rows=[[f,N,logint(lo^dim,N),lo]]);
      for(j=1,#indices,
        my(F=polcyclo(indices[j]),d=poldegree(F),A=(lo-1)^d);
        rows=concat(rows,[[subst(F,x,f),M[j],logint(A^dim,M[j]^d),A]])
      );
      my(S=hiddenDivisorShortPolynomial(rows,dim,R),roots=hiddenDivisorRoots(S,rows,R));
      calls++;
      foreach(roots,z,if(N%(c+z)==0 && isprime(c+z),found=setunion(found,[c+z])));
      if(vecprod(found)==N,return([found,calls]))
    )
  );
  [found,calls]
};

{
  my(indices=[2,3],slopes=[6,8,10],ps=186*slopes+[1,1,1],N=vecprod(ps));
  my(menus=vector(#indices,j,vector(#slopes,i,affineSupplyRow(indices[j],slopes,i))));
  for(i=1,#ps,for(j=1,#indices,
    if(!isprime(ps[i]) || subst(menus[j][i],x,N)%subst(polcyclo(indices[j]),x,ps[i]),
      error("order supply ",[i,j]))
  ));
  my(got=recoverSupplyPrimes(N,indices,menus,8,25));
  if(got[1]!=ps,error("three-prime lattice recovery ",got));
  print([N,got]);

  my(S=vector(2,i,affineSupplyRow(3,[4,5],i)),p=359,q=487);
  if(S!=[16*x^2+16*x+31,25*x^2+25*x+13] || 4*(q-1)==5*(p-1) ||
    subst(S[2],x,p*q)%(p^2+p+1),error("non-affine fixture"));
  my(out=recoverSupplyPrimes(p*q,[3],[S],8,12));
  if(#out[1]!=1 || Set([out[1][1],p*q/out[1][1]])!=[p,q] || !isprime(q),
    error("two-prime recovery ",out));
  print([p*q,out]);

  my(removed=0);
  forprime(p=31,139,
    my(g1=(p+1)/gcd(6,p+1), h=p^2+p+1, fac=factor(h/gcd(h,3)));
    my(g2=prod(i=1,matsize(fac)[1],fac[i,1]^ceil(fac[i,2]/2)));
    if(gcd(g1,g2)!=1,error("overlapping indices"));
    for(v=1,5000,
      my(u=p*v+1,covered=(6*u%(p+1)==0 && 3*u^2%h==0));
      if(covered!=(u%(g1*g2)==0),error("multiplicity and content ",[p,v]));
      removed+=covered
    )
  );
  if(!removed,error("missing repeated-factor cases"));
  print("content and multiplicity events ",removed)
}
