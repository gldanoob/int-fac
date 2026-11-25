cardanoRadical(f,e) = {
  my(a=polcoef(f,2),b=polcoef(f,1),c=polcoef(f,0));
  my(P=a^2-3*b,Q=2*a^3-9*a*b+27*c,disc=Q^2-4*P^3,t);
  if(disc!=-27*poldisc(f) || !issquare(disc/e,&t),error("wrong mirror"));
  my(root=if(e==1,t,t*Mod('y,'y^2-e)));
  my(z=(-Q+root)/2);
  if(!z,z=(-Q-root)/2);
  if(!z || z^2+Q*z+P^3,error("Cardano invariant"));
  z
};

\\ Exact lower and upper rank certificates. Each row represents a character on all radicals.
cubicRadicalRows(fields,D) = {
  my(e=core(-3*D),m=#fields,nf=if(e==1,0,nfinit('y^2-e)));
  my(Z=apply(f->cardanoRadical(f,e),fields),bad=prod(i=1,m,poldisc(fields[i])));
  my(R=matrix(0,m),used=List(),l=3,rank=0);
  while(1,
    l=nextprime(l+1);
    if(l%3!=1 || bad%l==0 || kronecker(e,l)!=1,next);
    my(w=if(e==1,1,sqrt(Mod(e,l))),vals=apply(z->Mod(subst(lift(z),'y,w),l),Z));
    if(vecprod(vals)==0,next);
    my(g=Mod(1,l),a=1);
    while(g==1,a++;g=Mod(a,l)^((l-1)/3));
    my(row=vector(m,i,my(v=vals[i]^((l-1)/3));if(v==1,0,if(v==g,1,2))));
    my(T=matconcat([R;Mat(row)]));
    if(matrank(Mod(T,3))==rank,next);
    for(i=1,m,
      if(#polrootsmod(fields[i],l)!=if(row[i],0,3),error("residue test"))
    );
    R=T;rank++;listput(used,l);
    my(K=lift(matker(Mod(R,3))),ok=1);
    for(j=1,matsize(K)[2],
      my(v=prod(i=1,m,Z[i]^K[i,j]),c);
      if(e==1,
        if(!ispower(v,3,&c),ok=0;break),
        if(!nfeltispower(nf,v,3,&c),ok=0;break);
        c=nfbasistoalg(nf,c)
      );
      if(c^3!=v,error("cube witness"))
    );
    if(ok,return([R,Vec(used)]))
  )
};

radicalCollision(R) = {
  my(sz=matsize(R),r=sz[1],m=sz[2]);
  if(r==m,return((5/9)^m));
  my(counts=Map(),v);
  forvec(z=vector(r,i,[0,2]),
    my(word=lift(Mod(z*R,3)),mask=sum(i=1,m,(word[i]!=0)*2^(i-1)));
    if(!mapisdefined(counts,mask,&v),v=0);
    mapput(counts,mask,v+1)
  );
  my(keys=Vec(counts));
  sum(i=1,#keys,mapget(counts,keys[i])^2)/9^r
};

cubicRadicalBox(H,{weights=0}) = {
  my(S=List(),groups=Map());
  forvec(v=vector(3,i,[-H,H]),
    my(f='x^3+Polrev(v,'x));
    if(polisirreducible(f),listput(S,polredabs(f)))
  );
  S=Set(Vec(S));
  foreach(S,f,
    my(D=quaddisc(nfdisc(f)),v);
    if(!mapisdefined(groups,D,&v),v=[]);
    mapput(groups,D,concat(v,[f]))
  );
  my(total=0,cubes=0,last=0,defects=List(),cyclic=0);
  foreach(Vec(groups),D,
    my(F=mapget(groups,D),cert=cubicRadicalRows(F,D),R=cert[1],r=matsize(R)[1]);
    total+=r;cubes+=#F-r;last=max(last,vecmax(cert[2]));
    if(D==1,cyclic=r);
    if(r<#F,listput(defects,[D,#F,r]));
    if(weights && D!=1,
      my(P=radicalCollision(R));
      print([D,#F,r,numerator(P),denominator(P)])
    )
  );
  my(res=[H,#S,#Vec(groups),cyclic,total,cubes,last,Vec(defects)]);
  if(H==6 && [#S,#Vec(groups),cyclic,total,cubes]!=[369,330,4,360,9],
    error("archived height-six counts disagree"));
  res
};
