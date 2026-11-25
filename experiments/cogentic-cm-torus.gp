\\ Anti-invariant prime valuations for Q(theta,i), theta real quadratic.
gauss_quotient(z,prime) = {
  my(n=norm(prime), t=z*conj(prime));
  if(real(t)%n || imag(t)%n,return([]));
  [t/n];
}

split_gaussian(p) = {
  for(u=1,sqrtint(p),
    my(v);
    if(issquare(p-u^2,&v) && v>0,return(u+I*v));
  );
  error("missing sum of squares");
}

cm_factor_base(bound) = {
  my(ps=primes([3,bound]));
  vector(#ps,j,my(p=ps[j]); if(p%4==1,[p,split_gaussian(p)],[p,p]));
}

unit_label(z) = {
  if(!z,error("zero label"));
  z/=gcd(real(z),imag(z));
  while(real(z)<=0 || imag(z)<0, z*=I);
  z;
}

cm_entries(z,idx,s,c,disc,fb) = {
  my(value=z^2+s*z+c, entries=List());
  if(gcd(norm(value),2*disc)!=1,return(0));
  for(j=1,#fb,
    my(p=fb[j][1], g=fb[j][2], split=p%4==1);
    for(side=0,split,
      my(pr=if(side,conj(g),g), first=gauss_quotient(value,pr), v=0);
      if(!#first,next);
      while(#first, value=first[1]; v++; first=gauss_quotient(value,pr));
      if(split,
        my(rt=lift(-Mod(real(pr),p)/imag(pr)), slope=lift(Mod(real(z)+rt*imag(z),p)));
        listput(entries,[[idx,p,slope,0],if(side,-v,v)]),
        my(u=lift(Mod(real(z),p)), t=lift(Mod(imag(z),p)));
        if(t,listput(entries,[[idx,p,u,min(t,p-t)],if(t<p-t,v,-v)]));
      );
    );
    if(norm(value)==1,return(Vec(entries)));
  );
  0;
}

rational_label(z,fb) = {
  my(vs=List());
  z=unit_label(z);
  my(q=gauss_quotient(z,1+I));
  while(#q,z=q[1];q=gauss_quotient(z,1+I));
  for(j=1,#fb,
    my(p=fb[j][1],g=fb[j][2],num=0);
    if(p%4!=1,next);
    for(side=0,1,
      my(pr=if(side,conj(g),g));
      q=gauss_quotient(z,pr);
      while(#q,z=q[1];num+=if(side,-1,1);q=gauss_quotient(z,pr));
    );
    if(num,listput(vs,[[0,p,0,0],-num]));
    if(norm(z)==1,break);
  );
  [unit_label(z),Vec(vs)];
}

torus_split(n,g,exponent) = {
  my(i0=Mod(x,Mod(1,n)*(x^2+1)), pi=real(g)+imag(g)*i0);
  my(base=pi/(real(g)-imag(g)*i0));
  if(base^exponent!=1,error("invalid torus order"));
  my(t=valuation(exponent,2),w=base^(exponent/2^t));
  for(j=0,t,
    my(poly=liftall(w-1),fac=gcd(n,gcd(polcoef(poly,0),polcoef(poly,1))));
    if(1<fac && fac<n,return(fac));
    w=w^2;
  );
  1;
}

cm_probe(n,height,bound) = {
  my(m=sqrtint(n),fb=cm_factor_base(bound), cols=List(), ref=Map());
  my(slopes=[2,3,4,5], rows=Map(), nrows=0);
  for(idx=1,#slopes,
    my(s=slopes[idx],c=n-m^2-s*m,disc=s^2-4*c);
    if(disc<=0 || issquare(disc),next);
    for(a=-height,height,for(b=1,height,
      my(z=a+b*I, eval=z-m);
      if(gcd(norm(eval),n)!=1,next);
      my(e=cm_entries(z,idx,s,c,disc,fb));
      if(type(e)!="t_VEC",next);
      my(part=rational_label(eval,fb), tag=part[1], en=concat(e,part[2]), old);
      if(tag==1,listput(cols,en); next);
      if(mapisdefined(ref,tag,&old),
        listput(cols,concat(en,vector(#old,k,[old[k][1],-old[k][2]]))),
        mapput(ref,tag,en));
    ));
  );
  for(j=1,#cols,for(k=1,#cols[j],
    my(key=cols[j][k][1]);
    if(!mapisdefined(rows,key),nrows++;mapput(rows,key,nrows));
  ));
  if(!nrows,return([]));
  my(mat=matrix(nrows,#cols));
  for(j=1,#cols, for(k=1,#cols[j],mat[mapget(rows,cols[j][k][1]),j]+=cols[j][k][2]));
  my(piv=matindexrank(mat), ir=piv[1], ic=piv[2]);
  if(!#ir,return([]));
  my(basis=vecextract(mat,[1..nrows],ic), inv=vecextract(mat,ir,ic)^-1);
  for(j=1,#fb,
    my(p=fb[j][1],key=[0,p,0,0]);
    if(p%4!=1 || gcd(n,p)>1 || !mapisdefined(rows,key),next);
    my(rhs=vector(nrows)~, row=mapget(rows,key));
    rhs[row]=1;
    my(sol=inv*vecextract(rhs,ir));
    if(basis*sol!=rhs,next);
    my(exponent=120*denominator(sol),fac=torus_split(n,fb[j][2],exponent));
    if(fac>1,return([p,fb[j][2],exponent,fac,#cols,#ic]));
  );
  [];
}

cm_torus_replay() = {
  my(splits=0,signs=0);
  forprime(p=3,127, forprime(ell=5,149,
    if(ell==p || ell%4!=1,next);
    my(g=split_gaussian(ell), i0=Mod(x,Mod(1,p)*(x^2+1)),u=real(g)+imag(g)*i0);
    my(t=u/(real(g)-imag(g)*i0),m=p-kronecker(-1,p));
    if(t^(m/2)!=kronecker(ell,p),error("torus sign"));
    signs++;
  ));
  for(j=1,4,
    my(n=[77,143,221,5767][j],out=cm_probe(n,if(n==5767,40,24),71));
    if(!#out || out[4]<=1 || out[4]>=n || n%out[4],error("missing quartic certificate"));
    print([n,out]);splits++;
  );
  print(signs," local torus signs; ",splits," quartic factorizations");
}
if(type(cogentic_as_library)!="t_INT",iferr(cm_torus_replay(),err,print(err);quit(1)));
