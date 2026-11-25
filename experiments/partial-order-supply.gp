\\ Run from the repository root.
read("experiments/hidden-divisor-lattice.gp");

checkPartialMass(p,q,ks,shifts,lower,upper) = {
  my(N=p*q,x='x,g=vector(#ks),sumSquares=0);
  for(j=1,#ks,
    my(F=subst(polcyclo(ks[j]),x,p),d=eulerphi(ks[j]),a=lower[j]*d/2,b=upper[j]*d/2);
    g[j]=gcd(F,N+shifts[j]);
    if(g[j]>=F || g[j]^denominator(a)<N^numerator(a) ||
      g[j]^denominator(b)>N^numerator(b) || d*upper[j]^2>=1,
      error("partial bounds ",[p,q,ks[j]]));
    sumSquares+=d*lower[j]^2
  );
  if(sumSquares<=1,error("insufficient combined bound"));
  [g,sumSquares]
};

{
  my(p=109,q=163,N=p*q);
  print(checkPartialMass(p,q,[2,5],[-2,-4],[4/5,2/5],[17/20,9/20]));
  my(U=sqrtint(N),P=U\2,A1=sqrtnint(N^2,5),A2=sqrtnint(N^4,5));
  my(dim=8,R=32,calls=0,found=0);
  forstep(lo=P,2*U+2,2*R+1,
    my(c=lo+R,f=x+c,M1=N-2,M2=N-4);
    my(rows=[[f,N,logint(lo^dim,N),lo],[f+1,M1,logint(A1^dim,M1),A1],
             [subst(polcyclo(5),x,f),M2,logint(A2^dim,M2^4),A2]]);
    my(S=hiddenDivisorShortPolynomial(rows,dim,R));
    calls++;
    foreach(hiddenDivisorRoots(S,rows,R),z,
      if(1<c+z && c+z<N && N%(c+z)==0,found=c+z;break(2))
    )
  );
  if(found!=p || calls!=1,error("partial lattice recovery ",[found,calls]));
  print([N,found,calls]);
  print(checkPartialMass(12613,16421,[2,3,7],[-1,-4,2],
                         [11/20,57/100,19/200],[3/5,3/5,1/10]));
  my(pairs=0,multi=0);
  forprime(u=101,300,forprime(v=u+1,min(300,2*u),
    my(product=1,nontrivial=0);
    foreach([3,4,6],k,
      my(F=polcyclo(k),G=gcd(subst(F,x,u),subst(F,x,v)));
      G/=gcd(G,k);
      my(same=gcd(G,v-u),inverse=gcd(G,u*v-1));
      if(same*inverse!=G || gcd(product,G)!=1,error("two-sided rows ",[u,v,k]));
      product*=G;
      nontrivial+=(G>1)
    );
    pairs++;
    multi+=(nontrivial>=2)
  ));
  print(["coprime classes",pairs,multi]);
}
