read("simultaneous.gp");

s3_matrix(f,batch) = {
  my(rows=List(), k=poldegree(f));
  for(i=1,#batch,
    my(ell=batch[i][1], roots=polrootsmod(f,ell));
    for(perm=0,k!-1,
      my(s=numtoperm(k,perm), vals=vector(#batch,j,
        vector(k,t,if(roots[s[t]]==Mod(batch[j][2],ell),
                    valuation(subst(f,x,batch[j][2]),ell),0))));
      listput(rows,concat(vals));
    );
  );
  return(matrix(#rows,#rows[1],i,j,rows[i][j]));
};

local_tests(title,f,batch) = {
  my(k=poldegree(f), polys=apply(z->subst(f,x,x+z[2]),batch), tally=Map());
  forprime(p=101,2000,
    if(!nonzero_units(f,batch,p)||poldisc(f)%p==0,next);
    my(cycles=vecsort(apply(poldegree,factor(Mod(1,p)*f)[,1])),
       d=lcm(cycles), gen=ffgen([p,d],'y), roots=polrootsmod(f,gen),
       size=p^d-1, odd=size>>valuation(size,2), sq=1, od=1);
    if(#roots!=k,error(["extension roots",p,d]));
    foreach(batch,z,
      my(c=z[2], base=roots[1]-c);
      for(i=2,k,
        my(ratio=(roots[i]-c)/base);
        if(ratio^(size/2)!=1,sq=0);
        if(ratio^odd!=1,od=0);
      );
    );
    if((od && !sq) || (projective_gcd(p,odd,polys)==p)!=od,
      error(["maximal odd exponent",title,p,od,sq]));
    if(#cycles==1 && p!=k && !od,error(["inert",title,p]));
    my(key=Str(cycles), count);
    if(!mapisdefined(tally,key,&count),count=[0,0,0]);
    mapput(tally,key,count+[1,sq,od]);
  );
  my(keys=Vec(tally));
  print([title,vector(#keys,i,[keys[i],mapget(tally,keys[i])])]);
};

iferr({
  my(f=x^3-x-1,b=markers(f,3),v=s3_matrix(f,b));
  if(matrank(v)!=9||matrank(Mod(1,2)*v)!=9,error("S3 square rank"));
  print(["S3",b,matrank(v),matrank(Mod(1,2)*v)]);
  local_tests("S3",f,b);
  f=x^3+x^2-2*x-1;
  local_tests("C3",f,markers(f,3));
  f=x^5+x^4-4*x^3-3*x^2+3*x+1;
  local_tests("C5",f,markers(f,3));
},err,print(err);quit(1));
