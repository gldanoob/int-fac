\\ Exact integer class-polynomial values and separate finite-field path counts.
default(parisize,96000000);

cmNextTargets(old,current,phi,back) = {
  my(image=polresultant(subst(current,'y,'x),phi,'x));
  my(value=divrem(image,old^back));
  if(value[2],error("non-backtracking division has remainder"));
  value[1]
};

cmFieldGraph(p,phi) = {
  my(g=ffgen(p^2,'a),vertices=List([0*g]),edges=List(),i=1);
  while(i<=#vertices,
    my(F=factormod(subst(phi,'x,vertices[i]),g),row=List(),count=0);
    for(j=1,matsize(F)[1],
      if(poldegree(F[j,1])!=1,error("supersingular neighbor outside quadratic field"));
      my(v=-polcoef(F[j,1],0),k=1);
      while(k<=#vertices && vertices[k]!=v,k++);
      if(k>#vertices,listput(vertices,v));
      listput(row,[k,F[j,2]]);count+=F[j,2]
    );
    if(count!=3,error("outdegree differs from three"));
    listput(edges,Vec(row));i++
  );
  my(B=matrix(#vertices,#vertices),target=0);
  for(j=1,#vertices,
    foreach(edges[j],v,B[j,v[1]]=v[2]);
    if(vertices[j]==1728+0*g,target=j)
  );
  if(!target || #vertices!=p\12+2,error("wrong supersingular component"));
  [B,target]
};

cmDepth(X) = {
  my(j=2);while(2^j<=16*X^2*(j+1)^2,j++);j
};

checkCmFilters() = {
  my(phi=polmodular(2),vals=vector(9),firstMiss=vector(9),tests=0);
  my(old='y,current=subst(phi,'x,0));
  for(j=1,#vals,
    my(H=polclass(-3*4^j,0,'y));vals[j]=subst(H,'y,1728);
    if(poldegree(H)!=2^(j-1) || !vals[j],error("ring class polynomial"));
    if(j<=5,
      if(current!=H^3,error("independent specialization ",j));
      my(newer=cmNextTargets(old,current,phi,if(j==1,3,2)));
      old=current;current=newer
    );
    forprime(p=5,2000,
      if(vals[j]%p==0 && p%12!=11,error("ordinary prime selected ",[p,j]));
      if(!firstMiss[j] && p%12==11 && vals[j]%p,firstMiss[j]=p);
      tests++
    )
  );
  print(["CM class polynomial levels",#vals,"independent integer recurrences",5,
         "prime exclusions",tests,"first omitted class prime",firstMiss]);
  my(graphs=0,entries=0,signs=0);
  forprime(p=5,400,if(p%12==11,
    my(data=cmFieldGraph(p,phi),B=data[1],to=data[2],dim=matsize(B)[1]);
    my(prev=matid(dim),cur=B,jmax=cmDepth(p));
    for(j=1,jmax,
      if(j<=#vals,
        if((cur[1,to]>0)!=(vals[j]%p==0),error("integer and field differ ",[p,j]));
        signs++
      );
      if(j==jmax,
        for(r=1,dim,for(c=1,dim,if(cur[r,c]<=0,error("unreached vertex at fixed depth"));entries++));
        break
      );
      my(after=cur*B-if(j==1,3,2)*prev);prev=cur;cur=after
    );
    graphs++
  ));
  print(["quadratic-field graphs",graphs,"agreement with exact integer values",signs,
         "positive endpoint pairs at theorem depth",entries]);
  my(other=0);
  foreach([[-3,-15],[-7,-20],[-15,-23]],ds,
    my(A=polclass(ds[1],0,'y),H=polclass(ds[2],0,'y),prev=A);
    my(cur=polresultant(subst(A,'y,'x),phi,'x));
    for(j=1,4,
      my(V=polresultant(cur,H,'y));
      if(!V,error("distinct CM fields intersect in characteristic zero"));
      forprime(p=5,200,if(ds[1]%p && ds[2]%p,
        if(V%p==0 && (kronecker(ds[1],p)!=-1 || kronecker(ds[2],p)!=-1),
          error("wrong two-field selector ",[ds,j,p]));
        other++
      ));
      my(after=cmNextTargets(prev,cur,phi,if(j==1,3,2)));prev=cur;cur=after
    )
  );
  my(V=vals[9],n=11^2*23^3*17^2*37);
  if(gcd(n,lift(Mod(V,n)^(logint(n,2)+1)))!=11^2*23^3,error("full prime powers"));
  print(["other CM-pair exclusions",other,"full selected prime powers",11^2*23^3]);
};

iferr(checkCmFilters(),err,print(err);quit(1));
