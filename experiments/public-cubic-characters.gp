conductors = [7,13,19];
primitive = apply(znprimroot, conductors);
field_cache = Map();
probe_cache = Map();

character(t,m) = vector(m,i,znlog(Mod(t,conductors[i]),primitive[i])%3);
dot(a,b) = sum(i=1,#a,a[i]*b[i])%3;
normalize(v) = {
  for(i=1,#v,if(v[i],return((v*v[i])%3)));
  error("zero character")
};

field_for(v) = {
  my(row=normalize(v), key=Str(row), f);
  if(mapisdefined(field_cache,key,&f),return(f));
  my(support=select(i->row[i]!=0,[1..#row]), n=prod(i=1,#support,conductors[support[i]]),
     liftgens=vector(#support,j,
       my(i=support[j], ell=conductors[i], rest=n/ell);
       lift(chinese(Mod(lift(primitive[i]),ell),Mod(1,rest)))
     ), pivot=support[1], kernel=List(), info);
  for(j=1,#support,
    listput(kernel,lift(Mod(liftgens[j],n)^3));
    if(j==1,next);
    my(i=support[j], exponent=(-row[i]*row[pivot])%3);
    listput(kernel,lift(Mod(liftgens[j]*liftgens[1]^exponent,n)));
  );
  info=galoissubcyclo(n,Vec(kernel),2);
  if(info[2]!=n || poldegree(info[1])!=3,error(["field",row,info]));
  f=polredabs(info[1]);
  mapput(field_cache,key,f);
  return(f)
};

probes_for(row) = {
  my(key=Str(normalize(row)),out,f, terms=List());
  if(mapisdefined(probe_cache,key,&out),return(out));
  f=field_for(row);
  for(radius=1,2,
    forvec(c=vector(3,i,[-radius,radius]),
      if(vecmax(abs(c))!=radius || !(c[2]||c[3]),next);
      if(c[3]<0 || (!c[3]&&c[2]<0),next);
      listput(terms,minpoly(Mod(Polrev(c),f)));
    )
  );
  out=Vec(terms);
  mapput(probe_cache,key,out);
  return(out)
};

batch_gcd(n,d,probes) = {
  my(g=n);
  foreach(probes,f,
    my(poly=liftall(Mod(Mod(1,n)*x,f)^d));
    g=gcd([g,polcoeff(poly,1),polcoeff(poly,2)]);
    if(g==1,break);
  );
  return(g)
};

pivot_rows(s) = {
  my(m=#s, pivot=0, peak, out=List());
  for(i=1,m,if(s[i],pivot=i;break));
  if(!pivot,error("zero pivot"));
  peak=vector(m,j,if(j==pivot,s[pivot],0));
  listput(out,peak);
  for(i=1,m,
    if(i==pivot,next);
    listput(out,vector(m,j,((i==j)+(1-s[i])*peak[j])%3));
  );
  return(Vec(out))
};

nonzero_rows(m) = {
  my(rows=List());
  forvec(w=vector(m,i,[0,2]),
    if(w!=vector(m) && w==normalize(w),listput(rows,w))
  );
  return(Vec(rows))
};

compositum(m) = {
  my(n=prod(i=1,m,conductors[i]), kernel=vector(m,j,
       my(ell=conductors[j]);
       lift(chinese(primitive[j]^3,Mod(1,n/ell)))
     ), info=galoissubcyclo(n,kernel,2));
  if(info[2]!=n || poldegree(info[1])!=3^m,error(["compositum",m]));
  return(info[1])
};

check_fields(m,rows) = {
  my(composite=compositum(m));
  foreach(rows,row,
    my(f=field_for(row));
    if(!nfisincl(f,composite,1),error(["embedding",m,row]));
    forprime(t=1009,1600,
      if(polisirreducible(Mod(1,t)*f)!=(dot(row,character(t,m))!=0),
        error(["Frobenius", t,row,f]));
    );
    if(m==3, print(["field",row,f]));
  );
  forprime(t=1009,1600,
    if(poldisc(composite)%t==0,next);
    my(local_degree=if(character(t,m)==vector(m),1,3),
       factors=factor(Mod(1,t)*composite)[,1]);
    if(#factors!=3^m/local_degree || #select(f->poldegree(f)!=local_degree,factors),
      error(["compositum local",m,t]));
  );
};

representatives(m,lo,hi) = {
  my(v=vector(3^m), seen=0);
  forprime(t=lo,hi,
    my(c=character(t,m),i=1+sum(j=1,m,c[j]*3^(j-1)));
    if(v[i]==0,v[i]=[t,c];seen++);
    if(seen==#v,return(v));
  );
  error(["incomplete character states",m,seen])
};

replay(m) = {
  my(rows=nonzero_rows(m), ps=representatives(m,10000,14000), qs=representatives(m,14001,19500),
     worstfail=0, cases=0, samples=vector(4));
  check_fields(m,rows);
  foreach(ps,vp,
    foreach(qs,vq,
      my(p=vp[1], a=vp[2], q=vq[1], b=vq[2], n=p*q, s=character(n,m),
         mp=polcyclo(3,p), mq=polcyclo(3,q), md=lcm(mp,mq),
         onefail=1, dualfail=1, gs=List(), gd=List(),
         tests=if(s==vector(m),rows,pivot_rows(s)));
      if(p>=q || q>2*p || mp%mq==0 || s!=(a+b)%3,error("balanced mode and public state"));
      if(s!=vector(m) && (matrank(Mod(1,3)*matrix(m,m,i,j,tests[i][j]))!=m
         || #select(t->(dot(t,s)!=1 || #select(v->v!=0,t)>2),tests)),
        error(["pivot rows",s,tests]));
      foreach(tests,row,
        my(xin=dot(row,a)!=0, yin=dot(row,b)!=0, probes=probes_for(row),
           expected_s=if(xin,p,1), expected_d=expected_s*if(yin,q,1),
           actual_s=batch_gcd(n,mp,probes), actual_d=batch_gcd(n,md,probes));
        if(actual_s!=expected_s || actual_d!=expected_d,
          error(["literal gcd",m,p,q,row,actual_s,actual_d,expected_s,expected_d]));
        cases+=2;
        listput(gs,actual_s); listput(gd,actual_d);
        if(1<actual_s && actual_s<n,onefail=0);
        if(1<actual_d && actual_d<n,dualfail=0);
      );
      if(onefail||dualfail,worstfail++);
      if(m==3,
        my(which=0);
        if(s==vector(m), if(!onefail,which=4),
          if(gs[1]==1 && !dualfail,which=1);
          if(gd[1]==n && !dualfail,which=2);
          if(gs[1]==p && gd[1]==p,which=3);
        );
        if(which && !samples[which],
          print(["sample",which,p,q,a,b,s,tests,Vec(gs),Vec(gd)]);samples[which]=1)
      );
    )
  );
  if(m==3 && samples!=[1,1,1,1],error("sample coverage"));
  if(worstfail!=3^(m+1)-2,error(["worst failures",m,worstfail]));
  print(["summary", m,#ps*#qs,cases,worstfail]);
};

iferr({
  for(m=1,3,replay(m))
},err,print(err);quit(1));
