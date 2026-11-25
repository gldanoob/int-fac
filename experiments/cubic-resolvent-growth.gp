height(f) = vecmax(abs(Vec(f)));
shorttranslate(f) = {
  my(best=f);
  foreach(polrootsreal(f),r,
    my(g=subst(f,x,x+round(r)));
    if(height(g)<height(best),best=g));
  best;
};

probe(F,d,residue) = {
  my(D=prod(i=1,#F,poldisc(F[i])),checks=0);
  forprime(p=5,200,
    if(p%3==residue && D%p,
      my(signs=apply(e->kronecker(e,p),d));
      if(vecmax(signs)!=1,error("missing positive sign",p));
      for(i=1,#F,
        my(n=#polrootsmod(F[i],p));
        if((signs[i]==-1 && n!=1) || (signs[i]==1 && n==1),error("Frobenius sign",p,F[i])));
      checks++));
  checks;
};
mirror(D) = {
  my(bnf=bnfinit(quadpoly(-3*D,y),1));
  if(!bnfcertify(bnf) || bnf.no%3,error("mirror class group", D));
  my(bnr=bnrinit(bnf,1,1),H=subgrouplist(bnr,[3])[1]);
  my(F=bnrclassfield(bnr,H,2),G=nfsubfields(F,3,1));
  if(!#G,error("missing cubic subfield",D));
  my(g=shorttranslate(polredabs(G[1])));
  if(!polisirreducible(g) || nfdisc(g)!=-3*D,error("mirror polynomial",g));
  g;
};

positiveMarker(l) = {
  if(!isprime(l) || !(l%9==4 || l%9==5),error("invalid prime marker",l));
  my(a=if(l%9==4,1,-1),n=sqrtnint(l\4,3)+1);
  while(n%2 || (l-a-3*n)%27 || valuation(4*n^3-l,3)!=3,n++);
  my(f=x^3+3*n*x^2-l,g=subst(f,x,a+3*x)/27);
  if(!polisirreducible(f) || denominator(g)!=1,error("positive marker polynomial",l));
  if(poldisc(g)!=l*(4*n^3-l)/27 || gcd(poldisc(g),6)!=1,error("polynomial discriminant",l));
  my(D=nfdisc(g));
  if(D<=0 || gcd(D,6)!=1 || !issquarefree(D) || valuation(D,l)!=1,error("positive marker field",l));
  my(u=shorttranslate(polredabs(g)),v=mirror(D));
  if(height(u)^2>81*D || height(v)^2>243*D,error("sample height",l));
  print(["mirror pair",l,n,D,u,height(u),nfdisc(v),v,height(v),probe([u,v],[D,-3*D],2)]);
};

negativeSingleton(l) = {
  if(!isprime(l) || l%49!=1,error("invalid singleton marker",l));
  my(t=10+49*round((3*sqrt(l)-10)/49),c=t^2-9*l);
  if(valuation(c,7)!=1 || t%7==0,error("Eisenstein condition",l));
  shorttranslate(x^3-3*c*x-2*t*c);
};

negativeTriangle(p,q) = {
  my(m=(p+q)/2,h=(q-p)/2,Q=x^3-3*h^2*x-2*m*h^2);
  if(p>=q || p<=2*h || !(isprime(p) && isprime(q)),error("invalid close primes",p,q));
  if(poldisc(Q)!=-108*h^4*p*q,error("close pair polynomial discriminant",p,q));
  my(F=[negativeSingleton(p),negativeSingleton(q),shorttranslate(Q)],d=[-3*p,-3*q,-3*p*q]);
  if(prod(i=1,3,d[i])!=-3*(3*p*q)^2,error("triangle squareclass",p,q));
  for(i=1,3,if(!polisirreducible(F[i]) || !issquare(nfdisc(F[i])/d[i]),error("triangle field",F[i])));
  my(heights=apply(height,F),discs=apply(nfdisc,F));
  print(["negative triangle",p,q,h,discs,F,heights,probe(F,d,1)]);
};

cubeGapMatching(Y) = {
  my(available=Map(),markers=List(),n=0,steps=Set([]),largest=0,localchecks=0);
  forprime(p=Y+1,2*Y,if(p%49==1,mapput(available,p,1);listput(markers,p)));
  foreach(Vec(markers),u,
    if(!mapisdefined(available,u),next);
    forstep(t=7,sqrtnint((2*Y-u)\2,3),7,
      my(v=u+2*t^3);
      if(!mapisdefined(available,v),next);
      my(f=x^3-3*t^2*x-u-v,d=[-3*u,-3*v,-3*u*v]);
      if(poldisc(f)!=-108*u*v,error("bad cube-gap discriminant"));
      my(F=[negativeSingleton(u),negativeSingleton(v),shorttranslate(f)]);
      for(i=1,3,
        if(!polisirreducible(F[i]) || !issquare(poldisc(F[i])/d[i]),error("bad cube-gap field"));
        largest=max(largest,height(F[i]))
      );
      if(n<3,localchecks+=probe(F,d,1));
      n++;steps=setunion(steps,[t]);mapdelete(available,u);mapdelete(available,v);break
    )
  );
  foreach(Vec(available),u,
    forstep(t=7,sqrtnint((2*Y-u)\2,3),7,
      if(mapisdefined(available,u+2*t^3),error("matching is not maximal"))
    )
  );
  if(n==0 || #steps<2 || #markers!=2*n+#Vec(available),error("missing matching coverage"));
  print(["cube gaps",Y,#markers,n,steps,largest,localchecks])
};

separateBases() = {
  my(f=x^3-3*x^2-2,g=x^3-6*x^2-3*x+2,h=x^3-2,counts=[0,0]);
  if(!issquare(-poldisc(f)) || !issquare(poldisc(g)/3) || !issquare(-poldisc(h)/3),
    error("wrong quadratic resolvents"));
  forprime(p=13,100000,
    if(p%12==1 && #polrootsmod(f,p)==3 && #polrootsmod(g,p)==3,
      my(n=#polrootsmod(h,p));
      if(n!=0 && n!=3,error("unexpected uncovered splitting type",p));
      counts[1+(n==3)]++));
  if(vecmin(counts)==0,error("missing uncovered Frobenius type"));
  print(["two separate quadratic Artin conditions, uncovered inert and split",counts]);
};

positiveMarker(1013);
positiveMarker(1021);
positiveMarker(1031);
positiveMarker(1000003);
negativeTriangle(10193,10487);
negativeTriangle(1373,1471);
negativeTriangle(1000001213,1000001311);
cubeGapMatching(100000);
cubeGapMatching(1000000);
separateBases();
quit;
