\\ Fresh split markers and simple-root lifts.
markers(f,count) = {
  my(out=List(), previous=1, root, c);
  forprime(ell=5, 10000,
    if(previous%ell==0, next);
    root=polrootsmod(f,ell);
    if(#root!=poldegree(f), next);
    c=lift(root[1]); if(!c,c=ell);
    if(subst(f,x,c)%ell^2==0,c+=ell);
    if(c<=0 || c>2*ell || valuation(subst(f,x,c),ell)!=1,error("marker lift"));
    listput(out,[ell,c]);
    previous*=subst(f,x,c);
    if(#out==count,return(Vec(out)));
  );
  error("not enough markers");
};

\\ The displayed cyclic conductors use theta = zeta + zeta^(-1).
valuation_matrix(f, batch) = {
  my(k=poldegree(f), roots, z=Mod(x,f), conjugates=vector(poldegree(f)), rows=List());
  for(j=1,k, conjugates[j]=lift(z); z=z^2-2);
  if(z!=Mod(x,f)||#Set(conjugates)!=k,error("conjugates"));
  for(i=1,#batch,
    my(ell=batch[i][1]);
    roots=polrootsmod(f,ell);
    foreach(roots,r,
      my(vals=matrix(#batch,k,j,t,if(subst(conjugates[t],x,r)==Mod(batch[j][2],ell),
                                     valuation(subst(f,x,batch[j][2]),ell),0)));
      listput(rows,concat(vector(#batch,j,vector(k-1,t,vals[j,t+1]-vals[j,1]))));
    );
  );
  return(matrix(#rows,#rows[1],i,j,rows[i][j]));
};

projective_gcd(N, exponent, polynomials) = {
  my(g=N);
  foreach(polynomials,f,
    my(v=liftall(Mod(Mod(1,N)*x,f)^exponent));
    g=gcd(concat([g],vector(poldegree(f)-1,i,polcoeff(v,i))));
  );
  return(g);
};

nonzero_units(f,batch,t) = {
  return(prod(i=1,#batch,gcd(t,subst(f,x,batch[i][2])))==1);
};

all_square_ratios(f,batch,t) = {
  my(roots=polrootsmod(f,t), c, signs);
  if(#roots!=poldegree(f)||!nonzero_units(f,batch,t), return(0));
  foreach(batch,z,
    c=z[2];
    signs=Set(vector(#roots,i,kronecker(lift(roots[i])-c,t)));
    if(#signs!=1,return(0));
  );
  return(1);
};

ordinary_pairs(f,batch) = {
  my(k=poldegree(f), polys=apply(z->subst(f,x,x+z[2]),batch), p, q, a, D, v);
  for(wanted=0,1,
    p=nextprime(10000);
    while(!nonzero_units(f,batch,p) || polisirreducible(Mod(1,p)*f)!=wanted,p=nextprime(p+1));
    q=nextprime(p+1);
    while(!nonzero_units(f,batch,q),q=nextprime(q+1));
    v=vector(7,i,
      a=[1,2,3,5,7,31,127][i];
      D=a*polcyclo(k,p);
      projective_gcd(p*q,D>>valuation(D,2),polys)
    );
    if(v!=vector(7,i,if(wanted,p,1)),error(["ordinary",k,p,q,v]));
    print(["ordinary",k,p,q,wanted,v]);
  );
};

endpoint(f,batch,conductor,bound) = {
  my(k=poldegree(f), p=0, q=0, polys=apply(z->subst(f,x,x+z[2]),batch), a,D,v);
  forprime(t=10000,bound,
    if(t%4==3 && (t%conductor==1 || t%conductor==conductor-1) && all_square_ratios(f,batch,t),
      p=t; break);
  );
  if(!p,error("endpoint prime not found"));
  forprime(t=p+1,2*p,
    if((t%conductor==1 || t%conductor==conductor-1) && nonzero_units(f,batch,t) &&
       !all_square_ratios(f,batch,t),q=t; break);
  );
  if(!q || #polrootsmod(f,q)!=k,error("endpoint cofactor not found"));
  a=(p-1)/2; D=a*polcyclo(k,p);
  v=projective_gcd(p*q,D,polys);
  if(D%2!=1 || v!=p,error(["endpoint",k,p,q,v]));
  print(["endpoint",k,p,q,a,v]);
};

fixture(k,conductor,f) = {
  my(b=markers(f,3), v=valuation_matrix(f,b));
  if(matrank(v)!=3*(k-1) || matrank(Mod(1,2)*v)!=3*(k-1),error("valuation rank"));
  print(["batch",k,b,matrank(v),matrank(Mod(1,2)*v)]);
  ordinary_pairs(f,b);
  endpoint(f,b,conductor,1000000);
};

iferr({
  fixture(3,7,x^3+x^2-2*x-1);
  fixture(5,11,x^5+x^4-4*x^3-3*x^2+3*x+1);
},err,print(err);quit(1));
