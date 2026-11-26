\\ Replay a full Gaussian order certificate from an imaginary quadratic order.
cogentic_as_library=0;
read("experiments/cogentic-cm-torus.gp");

joint_source_entries(a,b,d,factor_base) = {
  my(value=a^2+d*b^2, entries=List());
  if(gcd(a,b)!=1 || gcd(value,2*d)!=1,return(0));
  foreach(factor_base,p,
    my(e=valuation(value,p));
    if(e,listput(entries,[[1,p,lift(Mod(-a,p)/b)],e]);value/=p^e);
    if(value==1,return(Vec(entries)));
  );
  0
};

joint_gaussian_entries(z,factor_base) = {
  my(entries=List());
  foreach(factor_base,item,
    my(p=item[1], g=item[2]);
    for(side=0,p%4==1,
      my(pr=if(side,conj(g),g), part=gauss_quotient(z,pr), e=0);
      while(#part,z=part[1];e++;part=gauss_quotient(z,pr));
      if(e,listput(entries,[[0,p,side],e]));
    );
    if(norm(z)==1,return(Vec(entries)));
  );
  0
};

joint_gaussian_certificate(n,c,height,bound,ell) = {
  my(d=c^2-n, pf=primes([2,bound]), gf=concat([[2,1+I]],cm_factor_base(bound)));
  my(rows=Map(), columns=List(), nrows=0, target=[0,ell,0], row);
  if(d<=0 || ell%4!=1 || !isprime(ell) || gcd(ell,n)!=1,error("invalid Gaussian chart"));
  for(a=-height,height,for(b=1,height,
    if(gcd(a^2+d*b^2,n)>1,next);
    my(s=joint_source_entries(a,b,d,pf));
    if(type(s)!="t_VEC",next);
    my(g=joint_gaussian_entries(a+b*c*I,gf));
    if(type(g)!="t_VEC",next);
    my(col=concat(s,g));
    foreach(col,item,
      if(!mapisdefined(rows,item[1]),nrows++;mapput(rows,item[1],nrows));
    );
    listput(columns,col);
  ));
  if(!mapisdefined(rows,target,&row),return([]));
  my(mat=matrix(nrows,#columns));
  for(j=1,#columns,foreach(columns[j],item,mat[mapget(rows,item[1]),j]=item[2]));
  my(piv=matindexrank(mat), ir=piv[1], ic=piv[2]);
  my(basis=vecextract(mat,[1..nrows],ic), rhs=vector(nrows)~);
  rhs[row]=1;
  my(sol=vecextract(mat,ir,ic)^-1*vecextract(rhs,ir));
  if(basis*sol!=rhs,return([]));
  my(e=12*denominator(sol), g=split_gaussian(ell));
  my(i0=Mod(x,Mod(1,n)*(x^2+1)), alpha=real(g)+imag(g)*i0);
  if(alpha^e!=1,error("invalid full Gaussian order"));
  [g,e,#columns,#ic]
};

joint_gaussian_replay() = {
  my(n=989, ell=5, cert=joint_gaussian_certificate(n,32,40,397,ell));
  if(#cert!=4 || cert[1]!=1+2*I,error("missing Gaussian order"));
  my(g=cert[1], e=cert[2]);
  if(torus_split(n,g,e)!=43,error("quotient did not split"));
  my(w=Mod(ell,n)^(e/2^valuation(e,2)));
  for(j=0,valuation(e,2),
    my(d=gcd(lift(w-1),n));
    if(1<d && d<n,error("unexpected norm split"));
    w=w^2;
  );
  foreach([23,43],p,
    my(i0=Mod(x,Mod(1,p)*(x^2+1)), alpha=1+2*i0, u=alpha/(1-2*i0));
    my(order=select(d->alpha^d==1,divisors(p^2-1))[1]);
    my(torus_order=select(d->u^d==1,divisors(p+1))[1]);
    my(norm_order=znorder(Mod(ell,p)));
    if(norm_order!=p-1 || torus_order!=p+1 || order!=p^2-1,error("local order"));
    if(e%order,error("incompatible certificate"));
  );
  print("Full Gaussian certificate ", cert, " splits 989 by its quotient");

  my(primes=apply(split_gaussian,[5,13,17,29,37,41]), samples=List());
  for(i=1,#primes,for(j=i+1,#primes,listput(samples,primes[i]*primes[j])));
  foreach([131,139],p,
    my(i0=Mod(x,Mod(1,p)*(x^2+1)));
    my(images=apply(z->real(z)+imag(z)*i0,Vec(samples)));
    if(#Set(images)!=binomial(#primes,2),error("sample collision"));
    for(j=1,#samples,
      my(z=images[j], conjugate=real(samples[j])-imag(samples[j])*i0);
      my(norm_order=znorder(Mod(norm(samples[j]),p)));
      my(u=z/conjugate, torus_order=select(d->u^d==1,divisors(p+1))[1]);
      my(s=z^2, square_order=select(d->s^d==1,divisors(p^2-1))[1]);
      if(lcm(norm_order,torus_order)!=square_order,error("joint sample order"));
    );
  );
  print(#samples," Gaussian subset products have distinct images and checked joint orders at each of two inert primes");
};
iferr(joint_gaussian_replay(),err,print(err);quit(1));
