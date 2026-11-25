\\ Full generation in each finite product unit group, via its prime quotients.
box_polynomials(k,r) = {
  my(found=List());
  forvec(v=vector(k,i,[-r,r]),
    if(vecmax(abs(v))!=r,next);
    my(a=Polrev(v));
    if(a!=0,listput(found,[sum(i=1,k,abs(v[i])), a]));
  );
  return(apply(w->w[2],vecsort(Vec(found),1)));
};

unit_radii(f,t,probes1,probes2,{adjoin_scalar=0}) = {
  if(adjoin_scalar,probes1=concat([lift(znprimroot(t))],probes1));
  my(decomp=factor(Mod(1,t)*f)[,1], lens=apply(poldegree,decomp),
     generators=apply(g->ffgen(g,'y),decomp), sizes=apply(n->t^n-1,lens),
     primes=factor(lcm(sizes))[,1], probes=concat(probes1,probes2), seen=vector(#probes),
     full1=1, full2=1);
  foreach(primes,ell,
    my(components=select(i->sizes[i]%ell==0,[1..#sizes]), r=#components,
       roots=vector(#components), basis=List(), powers=apply(i->sizes[i]/ell,components));
    for(j=1,#probes,
      if(!seen[j],seen[j]=apply(z->subst(probes[j],x,z),generators));
      if(#select(z->z==0,seen[j]),next);
      my(row=vector(r,i,
        my(z=seen[j][components[i]]^powers[i]);
        if(z==1,0,if(roots[i]==0,roots[i]=z;1,fflog(z,roots[i],ell)))
      ), m);
      if(row==vector(r),next);
      listput(basis,row);
      m=matrix(#basis,r,a,b,Mod(basis[a][b],ell));
      if(matrank(m)<#basis,listpop(basis));
      if(#basis==r,
        if(j>#probes1,full1=0);
        break
      );
    );
    if(#basis<r,full1=full2=0;break);
  );
  return([Str(vecsort(Vec(lens))),full1,full2]);
};

sweep(name,f,lo,hi) = {
  my(k=poldegree(f), d=poldisc(f), p1=box_polynomials(k,1), p2=box_polynomials(k,2),
     tally=Map(), bad=List(), badprojective=List(), count=0);
  forprime(t=lo,hi,
    if(d%t==0,next);
    my(v=unit_radii(f,t,p1,p2), pv=if(v[2],v,unit_radii(f,t,p1,p2,1)), old);
    count++;
    if(!mapisdefined(tally,v[1],&old), old=[0,0,0,0,0]);
    mapput(tally,v[1],old+[1,v[2],v[3],pv[2],pv[3]]);
    if(!v[3],listput(bad,[t,v[1]]));
    if(!pv[3],listput(badprojective,[t,v[1]]));
  );
  my(keys=Vec(tally));
  print([name,lo,hi,count,#p1,#p2,vector(#keys,i,[keys[i],mapget(tally,keys[i])]),Vec(bad),Vec(badprojective)]);
};

iferr({
  sweep("C3",x^3+x^2-2*x-1,1009,26000);
  sweep("S3",x^3-x-1,1009,26000);
  sweep("C5",x^5+x^4-4*x^3-3*x^2+3*x+1,1009,26000);
  sweep("S5",x^5-x-1,1009,26000);
},err,print(err);quit(1));

projective_gcd(N, exponent, polynomials) = {
  my(g=N);
  foreach(polynomials,f,
    my(v=liftall(Mod(Mod(1,N)*x,f)^exponent));
    g=gcd(concat([g],vector(poldegree(f)-1,i,polcoeff(v,i))));
  );
  return(g);
};



iferr({
  my(f=x^3-x-1, candidates=List(),
     exceptions=[3343,11491,12289,15773,17909,18143,23021,23159,23677]);
  forvec(v=vector(3,i,[-2,2]),
    if(v[2]||v[3],listput(candidates,[Polrev(v),minpoly(Mod(Polrev(v),f))]));
  );
  for(i=1,#exceptions,
    my(t=exceptions[i], degrees=apply(poldegree,factor(Mod(1,t)*f)[,1]),
       exponent=lcm(apply(d->t^d-1,degrees)), odd=exponent>>valuation(exponent,2), witness=[]);
    if(#degrees==1,error("expected reducible"));
    foreach(candidates, a,
      if(gcd(abs(norm(Mod(a[1],f))),t)>1,next);
      my(power=liftall(Mod(Mod(1,t)*a[1],f)^odd));
      if(poldegree(power)<1,next);
      if(projective_gcd(t,odd,[a[2]])!=1,error("quotient power comparison"));
      witness=a; break;
    );
    if(#witness==0,error(["no odd obstruction",t]));
    print([t,Vec(degrees),odd,witness]);
  );
},err,print(err);quit(1));


small_norm_generators(f, bound, want) = {
  my(k=poldegree(f), found=Map(), arch=polroots(f), keys, max_abs);
  forvec(c=vector(k,i,[-3,3]),
    my(a=Polrev(c), n=abs(norm(Mod(a,f))), old);
    if(n<5 || n>bound || !isprime(n) || #polrootsmod(f,n)!=k, next);
    max_abs=vecmax(apply(r->abs(subst(a,x,r)),arch));
    if(!mapisdefined(found,n,&old) || max_abs<old[1], mapput(found,n,[max_abs,a]));
  );
  keys=Vec(found);
  if(#keys<want,error(["too few markers",k,keys]));
  return(vector(want,i,[keys[i],mapget(found,keys[i])[2]]));
};

products_of_three(f, markers) = {
  my(vals=List());
  for(a=1,#markers-2, for(b=a+1,#markers-1, for(c=b+1,#markers,
    listput(vals,lift(Mod(markers[a][2]*markers[b][2]*markers[c][2],f)))
  )));
  return(Vec(vals));
};

projective_order(f, markers, p) = {
  my(g=ffgen(Mod(1,p)*f,'y), k=poldegree(f), order=polcyclo(k,p));
  return(lcm(vector(#markers,i,
    fforder(subst(markers[i][2],x,g)^(p-1),order))));
};

polymod(v,f,p) = liftall(Mod(Mod(1,p)*v,f));
is_inert(f,p) = polisirreducible(Mod(1,p)*f);

box_fixture(f) = {
  my(k=poldegree(f), b=small_norm_generators(f,500,8), products=products_of_three(f,b),
     max_coeff=vecmax(apply(a->vecmax(abs(Vec(a))), products)),
     minpolys=apply(z->minpoly(Mod(z[2],f)),b), p=nextprime(10000), q, ordp, ordq, n, a, mp, mq, v);
  if(#Set(products)!=binomial(#b,3),error("distinct exact products"));
  for(i=1,#b, if(abs(norm(Mod(b[i][2],f)))!=b[i][1],error("norm")));
  while(!is_inert(f,p),p=nextprime(p+1));
  q=nextprime(p+1);while(!is_inert(f,q),q=nextprime(q+1));
  if(2*max_coeff>=p || #Set(apply(w->polymod(w,f,p),products))!=#products,error("injective reduction"));
  ordp=projective_order(f,b,p); ordq=projective_order(f,b,q);
  mp=polcyclo(k,p);mq=polcyclo(k,q);
  if(ordp!=mp || ordq!=mq,error(["inert full projective group",k,p,q,ordp,ordq]));
  n=p*q; a=mq/gcd(mp,mq);
  if(a%2!=1 || a<=1,error("paired scale"));
  v=vector(4,i,
    my(d=[mp,mp*a,2*mp*a,mp*(a-1)][i]);
    projective_gcd(n,d>>valuation(d,2),minpolys)
  );
  if(v!=[p,n,n,p],error(["dual literal batch",k,p,q,v]));
  print(["balanced products",k,apply(z->z[1],b),#products,max_coeff,p,q,ordp,ordq]);
  print(["both inert literal gcds",k,p,q,a,v]);
};

iferr({
  box_fixture(x^3+x^2-2*x-1);
  box_fixture(x^5+x^4-4*x^3-3*x^2+3*x+1);
},err,print(err);quit(1));
