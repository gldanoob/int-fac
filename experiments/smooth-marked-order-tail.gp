\\ Jordan-weight divisor certificates and CM torsion orbits at prime powers.

orbit_count(ell,a,delta) = {
  my(m=ell^a,units=List(),seen=Map(),orbits=0,primitive=0);
  for(s=0,m-1,for(t=0,m-1,if((s^2-delta*t^2)%ell,listput(units,[s,t]))));
  for(x0=0,m-1,for(y0=0,m-1,
    if(x0%ell==0 && y0%ell==0,next);
    primitive++;
    if(mapisdefined(seen,[x0,y0]),next);
    orbits++;
    for(i=1,#units,
      my(s=units[i][1],t=units[i][2]);
      mapput(seen,[(s*x0+delta*t*y0)%m,(s*y0+t*x0)%m],1);
    );
  ));
  if(matsize(Mat(seen))[1]!=primitive,error("coverage"));
  my(sgn=kronecker(delta,ell),expected=if(sgn==1,2*a+1,if(sgn<0,1,2)));
  if(orbits!=expected,error("Cartan orbit count",[ell,a,delta,orbits]));
  primitive;
}

jordan(d,k) = {my(f=factor(d));prod(j=1,matsize(f)[1],(f[j,1]^k-1)*f[j,1]^(k*(f[j,2]-1)))}

certificates() = {
  my(total=0,eligible=0,top=0);
  for(n=2,2000,
    my(ds=divisors(n));
    for(k=1,3,if(sum(i=1,#ds,jordan(ds[i],k))!=n^k,error("Jordan identity"));total++);
    forprime(y0=3,13,
      my(sm=1,fac=factor(n));
      for(i=1,matsize(fac)[1],if(fac[i,1]<=y0,sm*=fac[i,1]^fac[i,2]));
      for(bound=14,60,
        if(sm<bound,next);
        my(sds=divisors(sm),cut=select(x->x<=bound,sds));
        if(vecmax(cut)*y0<bound,error("divisor window"));
        for(k=1,2,
          my(weight=sum(i=1,#cut,jordan(cut[i],k)));
          if(weight*y0^k<bound^k,error("truncated mass"));
          eligible++;
        );
      );
    );
  );
  [total,eligible];
}

replay() = {
  my(cases=0,pts=0);
  forprime(ell=3,7,for(a=1,2,
    my(ns=2);while(kronecker(ns,ell)!=-1,ns++);
    for(t=1,3,pts+=orbit_count(ell,a,[1,ns,ell][t]);cases++);
  ));
  print("split, inert and ramified Cartan orbit checks, primitive torsion pairs = ",[cases,pts]);
  print("Jordan identities, truncated smooth divisor certificates = ",certificates());
}
iferr(replay(),e,print(e);quit(1));
quit;
