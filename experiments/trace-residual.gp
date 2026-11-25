\\ V_k(t) = u^k + u^-k for t = u + u^-1. Input t is a residue mod n.
tracePower(t,k) = {
  my(a=2+0*t, b=t);
  foreach(binary(k),bit,
    my(c=a*b-t);
    if(bit,a=c;b=b^2-2,b=c;a=a^2-2)
  );
  a
};

\\ Each center j and radius s covers all j-i and j+i, 0 <= i <= s.
tracePrefixHit(n,t,h) = {
  my(s=sqrtint(h), width=2*s+1, blocks=h\width, start=blocks*width);
  if(blocks,
    my(roots=vector(s+1,i,tracePower(t,i-1)));
    my(centers=vector(blocks,i,tracePower(t,s+1+(i-1)*width)));
    my(poly=productTree(roots,1,#roots)[1], values=List());
    treeValues(poly,productTree(centers,1,blocks),~values);
    if(gcd(n,lift(prod(i=1,#values,values[i])))>1,return(1))
  );
  for(k=start+1,h,if(gcd(n,lift(tracePower(t,k)-2))>1,return(1)));
  0
};

\\ One candidate trace. A return of 1 means this trace supplied no split.
splitTraceResidual(n,t,E,H) = {
  if(n<=2 || n%2==0 || E<1 || H<1,error("expected odd n > 2 and positive E,H"));
  t=Mod(t,n);
  my(z=tracePower(t,E),lo=1,hi=H);
  if(!tracePrefixHit(n,z,H),return(1));
  while(lo<hi,
    my(mid=(lo+hi)\2);
    if(tracePrefixHit(n,z,mid),hi=mid,lo=mid+1)
  );
  my(m=E*lo, s=valuation(m,2), v=tracePower(t,m>>s));
  for(j=0,s,
    my(d=gcd(n,lift(v-2)));
    if(d>1 && d<n,return(d));
    v=v^2-2
  );
  1
};

checkTraceResidual() = {
  my(tests=0);
  foreach([35,45,77,143],n,for(t=0,12,
    my(z=Mod(t,n), hit=0, a=2+0*z, b=z);
    for(h=1,36,
      hit=hit || gcd(n,lift(b-2))>1;
      if(tracePrefixHit(n,z,h)!=hit,error("trace prefix disagrees with direct recurrence"));
      my(c=z*b-a); a=b; b=c; tests++
    )
  ));
  \\ ord_7(3)=6, ord_13(3)=3. At E=1 the first hit is k=3.
  my(t=lift(Mod(3,91)+Mod(3,91)^-1));
  if(splitTraceResidual(91,t,1,2)!=1 || splitTraceResidual(91,t,1,3)!=13,error("prefix boundary"));
  if(splitTraceResidual(91,t,6,1)!=13,error("equal endpoint, distinct order valuations"));
  \\ N=935, norm(37+6 sqrt(-23))=13^3. All local orders divide E.
  t=2*(37^2-23*6^2)/Mod(13^3,935);
  if(splitTraceResidual(935,t,936,1)!=17,error("inert norm-one trace"));
  tests
};

\\ Legendre and Holzer give a primitive solution inside these two short loops.
\\ A proper denominator gcd already splits n. A zero trace here is a valid trace.
smallConicTrace(n,ell,r) = {
  for(z=1,sqrtint(ell),for(y=1,sqrtint(r),
    my(a=r*z^2-ell*y^2,x);
    if(a<0 || !issquare(a,&x) || gcd([x,y,z])!=1,next());
    my(d=gcd(n,r*z^2));
    if(d>1,return([d,0]));
    return([1,2*(x^2-ell*y^2)/Mod(r*z^2,n)])
  ));
  error("no primitive point for split auxiliary prime ",[ell,r])
};

\\ Finite search with explicit parameter bound. One means the box gave no split.
splitConicBox(n,E,H,bound) = {
  if(n<=2 || n%2==0 || E<1 || H<1 || bound<1,error("invalid conic search parameters"));
  forprime(ell=3,bound,
    if(ell%4!=3,next());
    if(n%ell==0,if(ell<n,return(ell));next());
    forprime(r=3,bound,
      if(kronecker(-ell,r)!=1,next());
      if(n%r==0,if(r<n,return(r));next());
      my(pair=smallConicTrace(n,ell,r),d=pair[1]);
      if(d==n,next());
      if(d==1,d=splitTraceResidual(n,pair[2],E,H));
      if(d>1,return(d))
    )
  );
  1
};

checkConicBox() = {
  my(points=0);
  forprime(ell=3,79,if(ell%4==3,forprime(r=3,79,
    if(kronecker(-ell,r)==1,smallConicTrace(1009,ell,r);points++)
  )));
  my(found=splitConicBox(4087,204,1,23));
  if(found<=1 || found>=4087 || 4087%found,error("missing one-prime conic split"));
  \\ With E=17 the missing multiplier at 67 is 4. All parameters are below 61.
  found=splitConicBox(4087,17,4,23);
  if(found<=1 || found>=4087 || 4087%found,error("missing residual conic split"));
  if(splitConicBox(1009,1,5,23)!=1,error("spurious prime split"));
  points
};
