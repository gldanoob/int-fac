\\ Count unordered prime pairs in (X,2X] with gcd(Phi_k(p),Phi_k(q)) >= Y.
moderateCounts(X,Y,k) = {
  my(ps=primes([X+1,2*X]),f=polcyclo(k),v=apply(p->subst(f,x,p),ps));
  my(ells=select(ell->ell%k==1,primes([Y,2*Y])),occ=Map(),total=0,tagged=0,hits=0);
  for(i=1,#ps,
    foreach(divisors(v[i]),h,
      if(h>=Y,my(old=0); mapisdefined(occ,h,&old); mapput(occ,h,old+1))
    );
    for(j=i+1,#ps,
      my(g=gcd(v[i],v[j]),tags=sum(t=1,#ells,g%ells[t]==0));
      total+=(g>=Y);
      tagged+=(tags>0);
      hits+=tags
    )
  );
  my(recovered=0,m=Mat(occ));
  for(i=1,matsize(m)[1],
    my(h=m[i,1],n=m[i,2]);
    if(n<2,next);
    my(w=-sum(e=1,Y-1,if(h%e==0,moebius(h/e),0)));
    recovered+=w*binomial(n,2)
  );
  my(progressionHits=0);
  foreach(ells,ell,
    my(roots=Set(lift(polrootsmod(f,ell))));
    if(#roots!=eulerphi(k),error("root count ",[k,ell]));
    my(n=sum(t=1,#ps,setsearch(roots,ps[t]%ell)!=0));
    progressionHits+=binomial(n,2)
  );
  if(total!=recovered || hits!=progressionHits,error("overlap count ",[k,total,recovered,hits,progressionHits]));
  [total,tagged,hits]
};

{
  foreach([3,4,5,6,8,10,12],k,print([k,moderateCounts(8000,20,k)]))
}
