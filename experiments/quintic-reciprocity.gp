\\ Ray-primary quintic reciprocity and finite cutoffs.
cyclo5 = polcyclo(5);

ray_markers(count) = {
  my(found=List(), seen=List());
  forvec(c=vector(4,i,[-2,2]),
    my(pi=1+125*Polrev(c), t=norm(Mod(pi,cyclo5)));
    if(!isprime(t) || setsearch(Set(seen),t),next);
    if(t%5!=1 || valuation(norm(Mod(pi-1,cyclo5)),5)<9,error("ray depth"));
    my(roots=select(u->subst(pi,x,u)==0,polrootsmod(cyclo5,t)));
    if(#roots!=1 || roots[1]^5!=1 || roots[1]==1,error(["marker root",pi,t]));
    listput(found,[pi,t,roots[1]]);
    listput(seen,t);
    if(#found==count,return(Vec(found)));
  );
  error("not enough ray markers");
};

left_symbol(w,marker) = {
  my(t=marker[2], root=marker[3], z=Mod(w,t)^((t-1)/5));
  for(j=0,4,if(z==root^j,return(j)));
  error(["left symbol", w, t]);
};

right_symbol(pi,p) = {
  if(p==5,error("exclude ramified p=5"));
  my(factors=factor(Mod(1,p)*cyclo5)[,1], total=0);
  foreach(factors,f,
    my(root=ffgen(f,'y), value=subst(pi,x,root), z, exponent=-1);
    if(value==0,error(["nonunit",pi,p]));
    z=value^((p^poldegree(f)-1)/5);
    for(j=0,4,if(z==root^j,exponent=j;break));
    if(exponent<0,error(["right symbol",pi,p,f,z]));
    total+=exponent;
  );
  return(total%5);
};

check_symbols() = {
  my(marks=ray_markers(4), classes=vector(4), nontrivial=vector(4),
     pairs=0);
  foreach(marks,marker,
    print(["ray marker",marker[1],marker[2],lift(marker[3]),
           valuation(norm(Mod(marker[1]-1,cyclo5)),5)]);
    forprime(p=2,250,
      if(p==5,next);
      my(a=left_symbol(p,marker), b=right_symbol(marker[1],p));
      if(a!=b,error(["prime",marker,p,a,b]));
      classes[p%5]++;
      if(a,nontrivial[p%5]++);
    );
    forprime(p=2,40,
      if(p==5,next);
      forprime(q=p+1,50,
        if(q==5,next);
        my(a=right_symbol(marker[1],p),b=right_symbol(marker[1],q));
        for(i=1,4,for(j=1,4,
          if(left_symbol(p^i*q^j,marker)!=(i*a+j*b)%5,
            error(["composite",marker,p,q,i,j]));
          pairs++;
        ));
      );
    );
  );
  if(vecmin(nontrivial)<1,error("need a nontrivial comparison in every branch"));
  print(["prime classes 1,2,3,4 mod 5",classes,nontrivial,"composite comparisons",pairs]);
};

conductors = List();
forprime(t=11,260,if(t%5==1,listput(conductors,t)));
conductors = Vec(conductors);
primitive = apply(znprimroot,conductors);
state5(p,m) = vector(m,i,znlog(Mod(p,conductors[i]),primitive[i])%5);

two_row_distinguishes(x,y) = {
  for(i=1,#x,
    if((x[i]==0)!=(y[i]==0),return(1));
    for(j=i+1,#x,for(c=1,4,
      if(((x[i]+c*x[j])%5==0)!=((y[i]+c*y[j])%5==0),return(1))
    ))
  );
  return(0);
};

cutoff_counts() = {
  my(ps=List());
  forprime(p=1009,2000,listput(ps,p));
  foreach([1,2,3,5,8,12],m,
    my(v=apply(p->state5(p,m),Vec(ps)), zero=vector(m), singles=0,
       proportional=0, union_count=0);
    for(i=1,#v,
      if(v[i]==zero,singles++);
      for(j=1,#v,
        if(i==j,next);
        my(bad=0);
        for(c=1,4,if(v[j]==(c*v[i])%5,bad=1;break));
        if(bad==two_row_distinguishes(v[i],v[j]),error("sparse cutoff rule"));
        if(bad,proportional++);
        if(bad||v[i]==zero,union_count++);
      );
    );
    print(["cutoff",m,conductors[m],#v,singles,proportional,union_count]);
  )
};

quintic_field(row) = {
  my(use=select(i->row[i]!=0,[1..#row]), piv=use[1],
     n=prod(j=1,#use,conductors[use[j]]), lifts=vector(#use,j,
        my(i=use[j],ell=conductors[i]); lift(chinese(primitive[i],Mod(1,n/ell)))),
     ker=List());
  for(j=1,#use,
    listput(ker,lift(Mod(lifts[j],n)^5));
    if(j==1,next);
    my(i=use[j], exponent=(-row[i]*lift(Mod(row[piv],5)^-1))%5);
    listput(ker,lift(Mod(lifts[j]*lifts[1]^exponent,n)));
  );
  my(out=galoissubcyclo(n,Vec(ker),2));
  if(out[2]!=n || poldegree(out[1])!=5,error("field degree/conductor"));
  return(polredabs(out[1]));
};

batch_gcd5(N,M,f) = {
  my(g=N);
  forvec(c=vector(5,i,[-1,1]),
    if(c[2]==0&&c[3]==0&&c[4]==0&&c[5]==0,next);
    my(alpha=Mod(Mod(1,N)*Polrev(c),f), v=liftall(alpha^M));
    g=gcd(concat([g],vector(4,i,polcoeff(v,i))));
    if(g==1,break);
  );
  return(g);
};

dual_fixture() = {
  my(p=0,q=0,a,b,row, fields, xord,yord,D,N);
  forprime(t=1009,1500,
    a=state5(t,2);
    if(a[1]&&a[2],p=t;break);
  );
  forprime(t=p+1,2*p,
    b=state5(t,2);
    if(b[1]&&b[2]&&(a[1]*b[2]-a[2]*b[1])%5,q=t;break);
  );
  if(!p||!q,error("fixture primes"));
  row=[1,lift(Mod(-a[1],5)/Mod(a[2],5))];
  fields=apply(quintic_field,[[1,0],[0,1],row]);
  if(vector(3,i,polisirreducible(Mod(1,p)*fields[i]))!=[1,1,0] ||
     vector(3,i,polisirreducible(Mod(1,q)*fields[i]))!=[1,1,1],error("fixture Frobenius"));
  xord=polcyclo(5,p);
  yord=polcyclo(5,q);
  D=lcm(xord,yord);
  N=p*q;
  if(batch_gcd5(N,xord,fields[3])!=1 ||
     apply(f->batch_gcd5(N,D,f),fields)!=[N,N,q],error("quotient cutoff fixture"));
  print(["literal mixed quintic",p,q,a,b,row,fields[3],1,[N,N,q]]);
};

iferr({
  check_symbols();
  cutoff_counts();
  dual_fixture();
},err,print(err);quit(1));
