\\ Test short shift generation via exact local discrete logs and lattice index.
{
shift_index(f,t,bound,projective) =
  my(factors=factormod(f,t), fs=factors[,1], r=#fs);
  if(vecmax(factors[,2])!=1,error("fixture requires squarefree f"));
  my(roots=vector(r,j,ffgen(fs[j],'a)));
  my(gens=vector(r,j,ffprimroot(roots[j])));
  my(orders=vector(r,j,t^poldegree(fs[j])-1));
  my(columns=matdiagonal(orders));
  if(projective,
    my(scalar=lift(znprimroot(t)));
    columns=concat(columns,vector(r,j,fflog(scalar*roots[j]^0,gens[j]))~)
  );
  for(c=-bound,bound,
    if(subst(f,x,Mod(c,t))!=0,
      columns=concat(columns,vector(r,j,fflog(roots[j]-c,gens[j]))~)
    )
  );
  matdet(mathnf(columns))
}
{
check_generation() =
  my(cases=0);
  foreach([101,257,1009], t,
    my(quadratic=liftall(ffinit(t,2,x)), cubic=liftall(ffinit(t,3,x)));
    my(polys=[cubic, x*(x-1)*(x-2), x*quadratic,
              liftall(ffinit(t,4,x)), x*(x-1)*quadratic]);
    foreach(polys, f,
      my(k=poldegree(f), B=k*sqrtint(t)+2*k+1);
      if(2*B-1>t,error("support wraps", [t,k,B]));
      if(shift_index(f,t,B-1,0)!=1 || shift_index(f,t,B-1,1)!=1,
        error("generation", [t,f,B]));
      cases++
    )
  );
  if(shift_index(x*(x+1)*(x^2+x+1),2,1,1)!=3,error("small field obstruction"));
  print("exact generation passed for ",cases," windows and the small field obstruction")
}
H(t)=t^2+t+1;
{
split_shift(f,n,M,B,require_unit) =
  my(d=M/2^valuation(M,2));
  for(c=-B,B,
    my(g=gcd(n,subst(f,x,c)));
    if(g!=1,
      if(!require_unit && g<n,return([g,c]));
      next
    );
    my(v=liftall(Mod(Mod(1,n)*(x-c),f)^d));
    g=gcd(n,gcd(polcoef(v,1),polcoef(v,2)));
    if(1<g && g<n,return([g,c]))
  );
  [1,0]
}
{
check_splits() =
  my(cyclic=x^3-x^2-2*x+1, general=x^3-x-1);
  my(cases=[[cyclic,11,13,2^5*H(11),3], [general,13,17,2^8*H(13),1],
            [cyclic,11,17,H(11),0], [cyclic,1013,1049,2^6*H(1013),3]]);
  foreach(cases, row,
    my([f,p,q,M,target_roots]=row);
    if(#polrootsmod(f,p)!=0 || #polrootsmod(f,q)!=target_roots
       || gcd(poldisc(f),p*q)!=1,
       error("incorrect local types", row));
    my(B=3*sqrtint(q)+6, hit=split_shift(f,p*q,M,B,1));
    if(hit[1]!=p,error("failed split", row));
    print("p=",p," q=",q," roots at q=",target_roots," unit shift c=",hit[2])
  );
  if(split_shift(cyclic,11*17,H(11)*H(17),20,1)[1]!=1,
     error("common exponent should be blind"));
  print("common inert exponent obstruction passed")
}
{
check_repeated() =
  foreach([101,257,1009], t,
    my(B=3*sqrtint(t)+7, gen=znprimroot(t), columns=matdiagonal([t-1,t-1,t]));
    for(c=1-B,B-1,
      my(a=Mod(1-c,t),b=Mod(-1-c,t));
      if(a && b,
        columns=concat(columns,[znlog(a,gen),znlog(b,gen),lift(1/a)]~))
    );
    if(matdet(mathnf(columns))!=1,error("repeated linear factor",t))
  );
  print("three repeated-factor rings have full unit index one")
}
iferr(check_generation();check_splits();check_repeated(),err,print(err);quit(1));
