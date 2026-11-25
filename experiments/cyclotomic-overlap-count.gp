\\ Run from the repository root with gp -fq experiments/cyclotomic-overlap-count.gp.

checkRootEnclosure() = {
  my(checked=0);
  for(k=3,120,
    my(f=polcyclo(k),d=poldegree(f),mu=moebius(k));
    foreach([4,5,9,32,127,257,1024],t,
      my(v=subst(f,x,t), center=t-mu/d, err=8/(d*t));
      if((center-err)^d>v || v>(center+err)^d,error("root enclosure ",[k,t]));
      checked++
    )
  );
  checked
};

countOverlapPairs(X,k,B) = {
  my(f=polcyclo(k),d=poldegree(f),vals=vector(X,j,subst(f,x,X+j)));
  my(count=0, primePairs=0, multiplicities=Map());
  for(i=1,X-1,for(j=i+1,X,
    my(p=X+i,q=X+j,g=gcd(vals[i],vals[j]),a=vals[i]/g,b=vals[j]/g);
    if(g*B<(p*q)^(d/2),next);
    if(a*b>4*B^2 || gcd(a,b)!=1,error("reduced ratio ",[p,q]));
    my(key=[a,b],old=0);
    mapisdefined(multiplicities,key,&old);
    mapput(multiplicities,key,old+1);
    primePairs+=isprime(p)*isprime(q);
    count++
  ));
  if(count && vecmax(Mat(multiplicities)[,2])>128*d,error("ratio count"));
  [count,primePairs]
};

{
  print("root enclosures ",checkRootEnclosure());
  my(indices=[3,4,5,6,8,10,12],zero=vector(3,i,[0,0]),
    expected=[[[0,0],[3,0],[23,2]],[[0,0],[7,0],[43,2]],zero,
              [[0,0],[4,1],[25,1]],zero,zero,zero]);
  for(h=1,#indices,
    my(k=indices[h]);
    my(row=vector(3,i,countOverlapPairs(256,k,[16,64,256][i])));
    if(row!=expected[h],error("pair count at ",k));
    print([k,row])
  );
  my(p=283,q=389,g=gcd(subst(polcyclo(10),x,p),subst(polcyclo(10),x,q)));
  if(!isprime(p) || !isprime(q) || g!=37901 || ceil((p*q)^2/g)!=319758,
     error("degree-four prime pair"));
  print("degree-four prime pair ",[p,q,g]);
  my(p=2,q=3);
  for(j=1,32,
    if(q^2+1!=2*(p^2+1) || q>2*p || gcd(p^2+1,q^2+1)*2<p*q,
       error("Pell orbit ",j));
    [p,q]=[3*p+2*q,4*p+3*q]
  );
  print("Pell terms 32");
}
