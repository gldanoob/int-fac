\\ Each output records a shortest generator modulo scalars, its two local
\\ valuations at 3, and the good odd-prime splitting patterns in the quartic.
s4marker(l) = {
  if(!isprime(l) || l%120!=53,error("marker ",l));
  my(P);
  foreach(divisors(10),d,
    my(fs=nflist("S3",l*d^2,0,quadpoly(l)));
    if(#fs,P=subst(polredabs(fs[1]),'x,'y);break)
  );
  if(!P,error("no cubic field ",l));
  my(nf=nfinit(P),w=nf.zk,tr=vector(3,i,nfelttrace(nf,w[i])));
  if(w[1]!=1 || nf.sign!=[3,0],error("unexpected integral basis/signature"));
  my(B=matrix(2,2,i,j,3*nfelttrace(nf,w[i+1]*w[j+1])-tr[i+1]*tr[j+1]));
  my(minimum=qfminim(B,,1),v=minimum[3][,1],norm=minimum[2]);
  if(v~*B*v!=norm || gcd(v)!=1,error("projected minimum"));
  my(xmax=sqrtint(norm*B[2,2]\matdet(B)),ymax=sqrtint(norm*B[1,1]\matdet(B)));
  for(i=-xmax,xmax,for(j=-ymax,ymax,
    if((i || j) && [i,j]*B*[i,j]~<norm,error("shorter vector found"))
  ));
  my(beta=Mod(v[1]*w[2]+v[2]*w[3],P),pr=idealprimedec(nf,3));
  if(#pr!=2 || pr[1].f!=1 || pr[2].f!=2,error("type above 3"));
  my(k);
  for(t=0,8,if(nfeltval(nf,beta-t,pr[1])==1 && nfeltval(nf,beta-t,pr[2])==0,k=t;break));
  if(type(k)!="t_INT" || nfeltval(nf,beta-k,pr[1])!=1 ||
     nfeltval(nf,beta-k,pr[2])!=0,error("local translation"));
  my(root=polrootsreal(charpoly(beta,'x))[1]);
  k+=9*round((root-k)/9);
  my(alpha=beta-k,f=charpoly(alpha,'x),height=vecmax(abs(Vec(f))));
  if(nfeltval(nf,alpha,pr[1])!=1 || nfeltval(nf,alpha,pr[2])!=0 ||
     2*abs(root-k)>9 || !polisirreducible(f),error("generator check"));
  my(s1=-polcoef(f,2),s2=polcoef(f,1),s3=-polcoef(f,0));
  my(g='x^4-2*s2*'x^2-8*s3*'x+s2^2-4*s1*s3);
  if(polgalois(g)[1]!=24,error("quartic Galois group"));
  [l,P,v,k,norm,nf.disc,f,height,g]
};

checkLocalS4(row) = {
  my(f=row[7],g=row[9],bad=2*polcoef(f,0)*poldisc(f)*poldisc(g),counts=[0,0,0],examples=[0,0,0]);
  forprime(q=5,997,
    if(bad%q==0,next);
    my(ff=factormod(f,q)[,1],gg=factormod(g,q)[,1],cd=vecsort(Vec(apply(poldegree,ff))),qd=vecsort(Vec(apply(poldegree,gg))));
    my(mixed=0,swap=0);
    if(cd==[1,1,1],
      my(signs=apply(t->kronecker(lift(-polcoef(t,0)),q),ff));
      mixed=vecmin(signs)!=vecmax(signs)
    );
    if(cd==[1,2],foreach(ff,t,if(poldegree(t)==2,swap=kronecker(lift(polcoef(t,0)),q)==-1)));
    if(mixed!=(qd==[2,2]) || swap!=(qd==[4]) || (cd==[3])!=(qd==[1,3]),
      error("quartic Frobenius mismatch ",[q,cd,qd,mixed,swap]));
    my(flags=[cd==[3],mixed,swap]);
    for(j=1,3,if(flags[j],counts[j]++;if(!examples[j],examples[j]=q)))
  );
  if(vecmin(counts)<1,error("missing local type"));
  my(p=examples[1],e=105*(p^2+p+1));
  for(j=2,3,
    my(n=p*examples[j],z=liftall(Mod(Mod(1,n)*'x,f)^e));
    if(gcd([n,polcoef(z,1),polcoef(z,2)])!=p,error("modular-polynomial split"))
  );
  [counts,examples]
};

balancedS4(rows,X) = {
  my(m=#rows,limit=2^m,pc=vector(limit),qc=vector(limit),primes=0);
  my(bad=prod(i=1,m,2*polcoef(rows[i][7],0)*poldisc(rows[i][7])*poldisc(rows[i][9])));
  forprime(p=X,2*X,
    if(bad%p==0,next);
    my(pm=0,qm=0);
    for(i=1,m,
      my(degrees=vecsort(Vec(apply(poldegree,factormod(rows[i][9],p)[,1]))));
      if(degrees==[1,3],pm+=2^(i-1));
      if(degrees==[4] || degrees==[2,2],qm+=2^(i-1)));
    if(bitand(pm,qm),error("incompatible Frobenius properties at one prime"));
    pc[pm+1]++;qc[qm+1]++;primes++);
  my(hits=vector(m,k,
    sum(i=1,limit,sum(j=1,limit,if(bitand(bitand(i-1,j-1),2^k-1),pc[i]*qc[j],0)))));
  if(vecmin(hits)<=0 || hits[m]>=primes*(primes-1),error("missing pair outcomes"));
  [X,primes,primes*(primes-1),hits];
};

markerRows=apply(s4marker,[53,173,293,1013,1000133]);
foreach(markerRows,r,print([r,checkLocalS4(r)]));
print(["ordered pairs guaranteed to split by each prefix",balancedS4(markerRows,1000)]);
