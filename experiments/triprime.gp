\\ Reconstruct a promised triprime from two normalized coefficients per good level.
\\ Only the test callback below enumerates divisors.
triprimeRootPolynomial(residues,degree) = {
  'x^(degree-#residues)*prod(i=1,#residues,'x-residues[i])
};

mergeCoefficients(old,M,poly,q) = {
  vector(#old,i,lift(chinese(Mod(old[i],M),Mod(polcoef(poly,i-1),q))))
};

smallRoots(coeffs,M,bound) = {
  my(poly='x^#coeffs+sum(i=1,#coeffs,coeffs[i]*'x^(i-1)));
  zncoppersmith(poly,M,bound)
};

triprimeFieldFactors(n,coefficient) = {
  my(p=sqrtnint(n,3), M=1, target=n^24, q=7, levels=0);
  my(sextic=vector(6),quartic=vector(4));
  if(p^3==n && isprime(p),return([[p,p,p],0]));
  while(M<=target,
    q=nextprime(q+1);
    if(q%12!=11 || n%q==0,next());
    my(u=(q-1)/2, g=znprimroot(q), residue=Mod(1,q), logs=vector(q-1));
    my(w=ffgen(factormod(polcyclo(u),2)[1,1],'w), powers=vector(u,i,w^(i-1)));
    for(i=0,q-2,logs[lift(residue)]=i%u;residue*=g);
    my(c=logs[n%q],C=powers[c+1],shift=(u+1)/2*c);
    my(R1=coefficient(q,logs,powers,shift,1)*powers[1+shift%u]);
    if(!R1,next());
    my(R3=coefficient(q,logs,powers,shift,3)*powers[1+(3*shift)%u]);
    my(S=R1+1+C,P=(R3+1+C^3+S^3+C+C^2)/R1,distinct=List(),repeated=List());
    for(i=0,u-1,
      my(t=powers[1+i],J=t^2+t,D=t^3+S*t+C,square=lift(g^(2*i)));
      if(D^2+S*J*D+P*J^2==0,listput(distinct,square));
      if(t^4+t^3+(1+C+R1)*t^2+C*t+C==0,listput(repeated,square))
    );
    sextic=mergeCoefficients(sextic,M,triprimeRootPolynomial(distinct,6),q);
    quartic=mergeCoefficients(quartic,M,triprimeRootPolynomial(repeated,4),q);
    M*=q; levels++
  );
  my(candidates=Set(concat(smallRoots(sextic,M,n^2),smallRoots(quartic,M,n^2))));
  my(left=n,factors=List());
  foreach(candidates,z,
    if(z>1 && issquare(z,&p) && left%p==0 && isprime(p),
      while(left%p==0,listput(factors,p);left/=p)
    )
  );
  if(left>1 && isprime(left),listput(factors,left);left=1);
  if(left!=1 || #factors!=3,error("could not verify a triprime factorization"));
  [vecsort(Vec(factors)),levels]
};

checkFieldDecoder() = {
  my(panel=[[71,107,113],[73,79,137],[71,103,269],[73,283,293],[71,71,113],[73,97,109],[73,73,109],[73,73,73]], levels=List());
  foreach(panel,expected,
    my(n=prod(i=1,3,expected[i]), ds=divisors(n));
    my(fixture=(q,logs,powers,shift,j)->sum(i=1,#ds,powers[1+(j*(logs[ds[i]%q]-shift))%#powers]));
    my(result=triprimeFieldFactors(n,fixture));
    if(result[1]!=expected,error("field decoder at ",n));
    listput(levels,result[2])
  );
  Vec(levels)
};

checkFieldWitnesses() = {
  my(q=2543,g=Mod(5,q),w=Mod('x,Mod(1,2)*('x^20+'x^8+'x^7+'x+1)));
  my(triples=[[1,7,12],[2,3,15],[1,8,21],[3,12,15]], rows=List());
  for(i=1,#triples,
    my(ds=[1]);
    foreach(triples[i],index,
      my(p=2^64+(lift(g^(41*index))-2^64)%q);
      while(!isprime(p),p+=q);
      ds=concat(ds,p*ds)
    );
    my(logs=vector(#ds,k,lift(znlog(Mod(ds[k],q),g))%1271), powers=[1,3,5]);
    my(masks=vector(3,k,
      my(value=sum(t=1,#ds,w^((powers[k]*(logs[t]-636*logs[#ds]))%1271)));
      subst(liftall(lift(value)),'x,2)
    ));
    listput(rows,concat([ds[#ds]%q],masks))
  );
  my(out=Vec(rows));
  if(out!=[[752,538088,767197,510065],[752,538088,163851,701923],[1883,767196,818349,701923],[1883,767196,818349,701922]],error("field witnesses"));
  out
};
