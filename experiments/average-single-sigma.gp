\\ Deterministic finite fixtures for one supplied sigma value or p+1 multiple.

interval_strip(n, bound) = {
  if(n==1,return([1,[]]));
  my(h=sqrtint(bound-1)+1, blocks=(bound+h-1)\h,
     poly=prod(i=1,h,x+Mod(i,n)), work=n, found=List());
  for(j=0,blocks-1,
    if(gcd(work,lift(subst(poly,x,Mod(j*h,n))))==1,next);
    for(k=max(2,j*h+1),min(bound,(j+1)*h),
      while(work%k==0,
        if(!isprime(k),error("interval traversal order"));
        listput(found,k);
        work/=k;
      )
    );
  );
  return([work,Vec(found)]);
};

separate(n, M, discmax, radius) = {
  my(v=valuation(M,2), odd=M>>v, g, powers=vector(v+1,i,odd<<(i-1)));
  for(a=2,radius+1,
    g=gcd(n,a);
    if(1<g&&g<n,return([g,"rational base gcd",a]));
    foreach(powers,d,
      g=gcd(n,lift(Mod(a,n)^d)-1);
      if(1<g&&g<n,return([g,"split algebra",a,d]));
    );
  );
  for(d=2,discmax,
    if(!isprime(d),next);
    my(f=x^2-d);
    for(a=-radius,radius,
      for(b=1,radius,
        g=gcd(n,a^2-d*b^2);
        if(1<g&&g<n,return([g,"norm gcd",d,a,b]));
        my(elem=Mod(Mod(1,n)*(a+b*x),f));
        foreach(powers,e,
          my(value=liftall(elem^e));
          g=gcd(n,polcoeff(value,1));
          if(1<g&&g<n,return([g,"quadratic",d,a,b,e]));
        )
      )
    )
  );
  return([1,"no split"]);
};

complete(n, M, bound, discmax, radius) = {
  my(initial=interval_strip(n,bound), found=List(initial[2]), incomplete=List(),
     queue=List([initial[1]]), history=List());
  while(#queue,
    my(v=queue[#queue], split, g);
    listpop(queue);
    if(v==1,next);
    if(isprime(v),listput(found,v);next);
    split=separate(v,M,discmax,radius);
    g=split[1];
    if(g==1,listput(incomplete,v);next);
    if(g<=1 || g>=v || v%g,error("invalid split"));
    listput(history,[v,split]);
    listput(queue,g);
    listput(queue,v/g);
  );
  if(prod(i=1,#found,found[i])*prod(i=1,#incomplete,incomplete[i])!=n,
    error("factorization product"));
  return([vecsort(Vec(found)),vecsort(Vec(incomplete)),initial[2],Vec(history)]);
};

supplied_sigma(factors) = prod(i=1,#factors, (factors[i][1]^(1+factors[i][2])-1)/(factors[i][1]-1));
integer_from(factors) = prod(i=1,#factors,factors[i][1]^factors[i][2]);
expected_factors(factors) = vecsort(concat(vector(#factors,i,vector(factors[i][2],j,factors[i][1]))));

fixture(name, data, M, cut, fields, radius, succeeds, {must_use_quadratic=0}) = {
  my(n=integer_from(data), result=complete(n,M,cut,fields,radius));
  if(succeeds && (result[1]!=expected_factors(data) || #result[2]),
     error(["incomplete fixture",name,result]));
  if(!succeeds && !#result[2], error(["fixture should be incomplete",name]));
  if(must_use_quadratic && !#select(h->h[2][2]=="quadratic",result[4]),
     error(["missing quadratic probe",name,result]));
  print([name,n,M,result]);
};

iferr({
  my(data=[[2,4],[3,3],[5,2],[7,4],[1009,1],[1013,1],[1019,1],[1021,1],
           [1031,1],[1033,1],[1039,1]]);
  fixture("sigma, seven residual primes",data,supplied_sigma(data),7,32,3,1,1);
  data=[[1009,1],[1021,1],[1031,1],[1039,1],[1051,1],[1063,1],[1087,1]];
  my(M=lcm(apply(t->t[1]+1,data))*2^4*3*11*101);
  fixture("larger lcm multiple",data,M,7,32,3,1,1);
  fixture("only one p+1 supplied",data,1010,7,2,1,0);
  fixture("no order supplied",data,1,7,32,3,0);
  data=[[1009,2],[1031,1],[1039,1],[1051,1],[1063,1],[1087,1]];
  my(S=supplied_sigma(data));
  if(S%1010==0,error("repeat fixture should miss the p+1 promise"));
  fixture("residual repeated prime, bounded stage",data,S,7,2,1,0);
  fixture("same repeat, later interval stage",data,S,1031,32,3,1);
  if(gcd(11*1019,1^2-3*2^2)!=11,error("norm witness"));
  print(["explicit nonunit norm witness",11*1019,[3,1,2],11]);
  if(interval_strip(97^3*101^2*103*107,102)!=[103*107,[97,97,97,101,101]],
     error("clipped final interval"));
  print(["clipped interval and full multiplicities",102]);
},err,print(err);quit(1));
