{
odd_projective(f,t,shift,odd_exp) =
  my(power=liftall(Mod(Mod(1,t)*(x-shift),f)^odd_exp));
  poldegree(power)<=0
}
{
valuation_exponent(shape,t) =
  sum(j=1,#shape,valuation(t^shape[j]-1,2))-valuation(t-1,2)
}
tail(a) = 1/(2^a*(2^a-1));
{
disjoint_average(shape,u) =
  my(a=#shape-1,b=sum(j=1,#shape,shape[j]%2==0),
     d=sum(j=1,#shape,if(shape[j]%2==0,valuation(shape[j],2)-1,0)));
  (tail(1+u*a)/2^(u*b)+tail(1+u*b)/2^(u*a))/2^(u*d)
}
{
one_fixture(label,f,shifts,squareclass,maxprime) =
  my(markers=vector(#shifts,j,abs(subst(f,x,shifts[j]))), disc=poldisc(f), rows=Map());
  if(#Set(markers)!=#shifts || !vecmin(apply(ell->ell%2 && isprime(ell) && disc%ell,markers)),
    error("invalid private marker", [label,markers,disc]));
  if(squareclass==2 && !issquare(disc/2),error("quadratic entanglement"));
  if(squareclass==1 && disc%2==0,error("unramified example should have odd discriminant"));

  forprime(t=3,maxprime,
    if((disc*prod(j=1,#markers,markers[j]))%t==0,next);
    my(factors=factormod(f,t)[,1], shape=Vec(vecsort(apply(g->poldegree(g),factors))),
       exponent=valuation_exponent(shape,t),
       odd_exp=lcm(apply(d->my(q=t^d-1); q/2^valuation(q,2),shape)),
       hit1=odd_projective(f,t,shifts[1],odd_exp),
       hit2=odd_projective(f,t,shifts[2],odd_exp), row);
    if(!mapisdefined(rows,shape,&row),row=[0,0,0,0,0]);
    mapput(rows,shape,row+[1,hit1,hit1*hit2,1/2^exponent,1/2^(2*exponent)]);
    if(squareclass==2 && (shape==[1,2]) != (kronecker(2,t)==-1),
      error("quadratic entanglement mismatch", [t,shape]));
    if(squareclass==2 && shape==[1,2] && exponent!=3,
      error("quadratic transposition exponent", [t,exponent]))
  );

  print(label," discriminant=",disc," markers=",markers);
  foreach(Vec(rows), shape,
    my(row=mapget(rows,shape), obs=[row[2],row[3]]/row[1],
       pred=[row[4],row[5]]/row[1], limit=vector(2,u,disjoint_average(shape,u)));
    if(squareclass==2,
      if(shape==[1,2],limit=vector(2,u,2^(-3*u)));
      if(shape==[1,1,1],limit=vector(2,u,2^(-2*u-1)+2^(-4*u-1)/(2^(2*u+1)-1)))
    );
    if(abs(obs[1]-pred[1])>.04 || abs(obs[2]-pred[2])>.04,
      error("unexpected finite discrepancy", [label,shape,row,obs,pred]));
    print("  ",shape," n=",row[1]," obs=",precision(obs*1.,6),
          " conditional-model=",precision(pred*1.,6)," limit=",limit)
  );
}
iferr({
  if(disjoint_average([1,1,1],1)!=1/7 || disjoint_average([1,2],1)!=1/12,
    error("cubic formula"));
  one_fixture("C3",x^3-x^2-2*x+1,[-3,3],1,250000);
  one_fixture("S3",x^3-x-1,[-2,2],1,250000);
  one_fixture("S4",x^4-x-1,[-2,2],1,250000);
  one_fixture("S3 entangled",x^3-18*x^2-8*x+16,[-1,-3],2,250000);
},err,print(err);quit(1));
