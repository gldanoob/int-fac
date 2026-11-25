\\ Two reciprocal quartic CM polynomials with a common norm-one value.
cm_reciprocal_polys(n,trace,k,cap) = {
  my(lead=3^k, out=List());
  for(h=0,2*lead, forstep(sign=-1,1,2,
    if(h==0 && sign==1,next);
    my(lin=h*sign);
    if(lin%3==0,next);
    my(ct=-lead+centerlift(-Mod(lead,n)*trace^2-lin*trace+lead));
    if(ct%3 || abs(lin)>=4*lead ||
       4*lead+2*lin+ct<=0 || 4*lead-2*lin+ct<=0,next);
    my(delta=lin^2-4*lead*ct);
    if(delta<=0 || issquare(delta),next);
    my(f=lead*(x^2+1)^2+lin*x*(x^2+1)+ct*x^2);
    listput(out,[lead,lin,ct,poldisc(f)]);
    if(#out>=cap,return(Vec(out)));
  ));
  Vec(out);
}

reciprocal_mark(a,b,k,pol,idx,ps) = {
  my(q3=valuation(a,3)-valuation(b,3));
  if(abs(q3)>=k,return(0));
  my(u=a^2+b^2,v=a*b,normval=pol[1]*u^2+pol[2]*u*v+pol[3]*v^2);
  if(valuation(normval,3)!=abs(q3),error("unexpected pole valuation"));
  normval/=3^abs(q3);
  if(normval%2==0,return(0));
  my(entries=List());
  for(j=1,#ps,
    my(p=ps[j],ev=valuation(normval,p));
    if(!ev,next);
    if(pol[4]%(p^2)==0,return(0));
    my(r=lift(Mod(a,p)/b),rev=lift(1/Mod(r,p)));
    if(r!=rev,listput(entries,[[idx,p,min(r,rev)],if(r<rev,ev,-ev)]));
    normval/=p^ev;
  );
  if(normval==1,Vec(entries),0);
}

reciprocal_pair(n,g,height,bound,k,left,right,marks,ps) = {
  my(columns=List(), rowids=Map(), nr=2);
  for(j=1,#marks,
    my(a=marks[j][1],b=marks[j][2],l=reciprocal_mark(a,b,k,left,1,ps));
    if(type(l)!="t_VEC",next);
    my(r=reciprocal_mark(a,b,k+1,right,2,ps));
    if(type(r)!="t_VEC",next);
    my(col=concat(l,r));
    for(t=1,#col,
      my(key=col[t][1]); if(!mapisdefined(rowids,key),nr++;mapput(rowids,key,nr));
    );
    listput(columns,[valuation(a,3)-valuation(b,3),col]);
  );
  if(#columns<2,return([]));
  my(mat=matrix(nr,#columns));
  for(j=1,#columns,
    mat[1,j]=1; mat[2,j]=columns[j][1];
    my(col=columns[j][2]);
    for(t=1,#col,mat[mapget(rowids,col[t][1]),j]+=col[t][2]);
  );
  my(piv=matindexrank(mat),ir=piv[1],ic=piv[2],rhs=vector(nr)~);
  rhs[1]=1;rhs[2]=-(k+1);
  my(basis=vecextract(mat,[1..nr],ic));
  my(sol=vecextract(mat,ir,ic)^-1*vecextract(rhs,ir));
  if(basis*sol!=rhs,return([]));
  my(exponent=120*denominator(sol),fac=torus_split(n,g,exponent));
  if(fac>1,return([exponent,fac,#columns,#ic,left[2],left[3],right[2],right[3]]));
  [];
}

reciprocal_probe(n,height,bound,{caps=3}) = {
  my(ps=primes([5,bound]));
  forprime(target=5,bound,
    if(target%4!=1 || gcd(target,n)>1,next);
    my(g=split_gaussian(target), trace=2*real(g^2)/Mod(target,n), marks=List());
    for(a=1,height,for(b=1,a-1,
      if(gcd(a,b)>1,next);
      my(red=Mod(a^2+b^2,n)-trace*a*b);
      if(gcd(lift(red),n)==1,listput(marks,[a,b]));
    ));
    marks=Vec(marks);
    for(k=2,6,
      my(polys=cm_reciprocal_polys(n,trace,k,caps), others=cm_reciprocal_polys(n,trace,k+1,caps));
      for(i=1,#polys,for(j=1,#others,
        my(out=reciprocal_pair(n,g,height,bound,k,polys[i],others[j],marks,ps));
        if(#out,return(concat([target,k],out)));
      ));
    );
  );
  [];
}

reciprocal_rational(n,g,height,bound,k,pol,marks,ps,fb) = {
  my(columns=List(), seen=Map(), rowids=Map(), nr=0, wq=[0,norm(g),0]);
  listput(columns,[[[2,3,0],k],[wq,-1]]);
  for(j=1,#marks,
    my(a=marks[j][1],b=marks[j][2],col=reciprocal_mark(a,b,k,pol,1,ps));
    if(type(col)!="t_VEC",next);
    my(e=valuation(a,3)-valuation(b,3));
    if(e,col=concat(col,[[[2,3,0],e]]));
    my(z=a*conj(g)-b*g, tag=rational_label(z,fb), old);
    for(t=1,#tag[2],col=concat(col,[[[0,tag[2][t][1][2],0],tag[2][t][2]]]));
    if(tag[1]==1,listput(columns,col);next);
    if(mapisdefined(seen,tag[1],&old),
      listput(columns,concat(col,vector(#old,t,[old[t][1],-old[t][2]]))),
      mapput(seen,tag[1],col));
  );
  for(j=1,#columns,for(t=1,#columns[j],
    my(key=columns[j][t][1]);
    if(!mapisdefined(rowids,key),nr++;mapput(rowids,key,nr));
  ));
  my(mat=matrix(nr,#columns));
  for(j=1,#columns,for(t=1,#columns[j],mat[mapget(rowids,columns[j][t][1]),j]+=columns[j][t][2]));
  my(piv=matindexrank(mat),ir=piv[1],ic=piv[2],rhs=vector(nr)~);
  my(basis=vecextract(mat,[1..nr],ic),inv=vecextract(mat,ir,ic)^-1);
  for(j=1,#fb,
    my(p=fb[j][1],key=[0,p,0]);
    if(p%4!=1 || gcd(n,p)>1 || !mapisdefined(rowids,key),next);
    rhs[mapget(rowids,key)]=1;
    my(sol=inv*vecextract(rhs,ir));
    if(basis*sol==rhs,
      my(exponent=120*denominator(sol),fac=torus_split(n,fb[j][2],exponent));
      if(fac>1,return([p,exponent,fac,#columns,#ic,pol[2],pol[3]]));
    );
    rhs[mapget(rowids,key)]=0;
  );
  [];
}

reciprocal_rational_probe(n,height,bound,{caps=3}) = {
  my(ps=primes([5,bound]),fb=cm_factor_base(bound));
  forprime(target=5,bound,
    if(target%4!=1 || gcd(target,n)>1,next);
    my(g=split_gaussian(target),trace=2*real(g^2)/Mod(target,n),marks=List());
    for(a=1,height,for(b=1,a-1,
      if(gcd(a,b)>1,next);
      my(red=Mod(a^2+b^2,n)-trace*a*b);
      if(gcd(lift(red),n)==1,listput(marks,[a,b]));
    ));
    marks=Vec(marks);
    for(k=2,6,
      my(polys=cm_reciprocal_polys(n,trace,k,caps));
      for(i=1,#polys,
        my(out=reciprocal_rational(n,g,height,bound,k,polys[i],marks,ps,fb));
        if(#out,return(concat([target,k],out)));
      );
    );
  );
  [];
}
