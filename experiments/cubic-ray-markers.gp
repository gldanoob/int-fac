\\ Construct an S3 cubic from the anti-invariant part of a quadratic ray group.
markerField(D,m) = {
  my(bnf=bnfinit(quadpoly(D,'y),1));
  if(!bnfcertify(bnf),error("uncertified quadratic class group ",D));
  my(ray=bnrinit(bnf,m,1,3), dim=#ray.cyc, tau=-polcoef(bnf.pol,1)-'y);
  my(plus=bnrgaloismatrix(ray,tau)+matid(dim), best=m+1, chosen);
  foreach(subgrouplist(ray,[3],1),H,
    if(denominator(H^(-1)*plus)!=1,next());   \\ tau acts as -1 on the quotient.
    my(ideal=bnrconductor(ray,H)[1],f=ideal[1,1]);
    if(ideal!=f*matid(2) || m%f,error("nonrational conductor ",ideal));
    if(f<best,best=f;chosen=H)
  );
  if(best>m,error("anti-invariant cubic quotient missing ",[D,m]));
  my(F=bnrclassfield(ray,chosen,2), sub=nfsubfields(F,3,1));
  if(!#sub,error("missing cubic subfield ",[D,m]));
  my(f=polredabs(sub[1]),g=f);
  foreach(polrootsreal(f),root,
    my(t=subst(f,'x,'x+round(root)));
    if(vecmax(abs(Vec(t)))<vecmax(abs(Vec(g))),g=t)
  );
  my(height=vecmax(abs(Vec(g))),disc=nfdisc(g));
  if(!polisirreducible(g) || disc!=D*best^2 || height^2>81*abs(disc),error("bad cubic ",g));
  [D,bnf.no,best,g,disc,height]
};

for(i=1,4,my(l=[1093,2549,100829,1000273][i]);if(!isprime(l) || l%364!=1,error("prime marker ",l));foreach([l,-3*l],D,print(markerField(D,91))));
for(i=1,3,my(l=[13,173,100213][i]);if(!isprime(l) || l%40!=13,error("small-conductor marker ",l));print(markerField(l,10));print(markerField(-3*l,3)));
