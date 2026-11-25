\\ Finite fixtures for the two-block frequency-one magnitude comparison.
\\ Search finitely many progression lifts; the running-time theorem uses random sampling.
fixedGapFixture(n,t,l,e) = {
  if(n%2==0 || gcd(n,t)!=1 || !isprime(l) || gcd(n,l)!=1 || e<1 || e>2,
    error("invalid fixture"));
  my(B=l^e, y=(2*t%n)/n, C=cos(2*Pi*y), z=sign(C)/2-C);
  my(x=(acos(z)-2*Pi*y)/(4*Pi), u=round(B*x)%B);
  if(u%l==0,u=(u+1)%B);
  my(m=n*B,a=lift(chinese(Mod(t*B,n)^-1,2*Mod(n*u,B)^-1)),r);
  for(j=1,2000,if(isprime(a+j*m),r=a+j*m;break));
  if(!r || r<=m || (t*B*r)%n!=1 || (u*n*r)%B!=2,error("auxiliary CRT"));
  my(v=n*B*r, last=lift(2*Mod(n*B,r)^-1));
  if((u*n*r+last*n*B+lift(Mod(2*t,n))*B*r-2)%v,error("phase sum"));
  my(gain=abs(4*cos(2*Pi*u/B)*cos(2*Pi*last/r)));
  if(abs(log(gain))>=2^-16,error("calibration ",gain));
  my(d=factor(n), w=prod(i=1,matsize(d)[1],
    my(b=d[i,1]^d[i,2]); 2*cos(2*Pi*lift(2*t*Mod(n/b,b)^-1)/b)));
  my(blocks=concat(vector(matsize(d)[1],i,d[i,1]^d[i,2]),[B,r]));
  my(fixed=prod(i=1,#blocks,my(b=blocks[i]);2*cos(2*Pi*lift(2*Mod(v/b,b)^-1)/b)));
  if(abs(log(abs(fixed/w))-log(gain))>10^-40,error("magnitude transfer"));
  if(abs(abs(w)-1)>2^-12 && (abs(w)>1)!=(abs(fixed)>1),error("threshold mismatch"));
  [abs(w)>1,abs(log(gain)),logint(v,2)+1]
};
checkFixedGaps() = {
  default(realprecision,80);
  my(cases=0,below=0,above=0,worst=0,maxbits=0);
  for(n=3,99,if(n%2==0,next);
    foreach([1,2,n\3,n\2],t,if(gcd(n,t)!=1,next);
      for(e=1,2,my(row=fixedGapFixture(n,t,100000007,e));
        cases++;if(row[1],above++,below++);worst=max(worst,row[2]);maxbits=max(maxbits,row[3]))));
  if(min(below,above)==0,error("missing outcome"));
  print([cases,below,above,worst,maxbits])
};
checkExactMagnitudes() = {
  my(phases=0,degrees=0);
  foreach([45,63,75,81,105,135,165,315,1155],L,
    my(z=Mod(x,polcyclo(L)),powers=vector(L,i,z^(i-1)),byKey=Map(),values=List());
    foreach(divisors(L),n,
      my(m=if(n%3==0 && n%9,n/3,n),roots=select(r->(r^2-1)%n==0,vector(n,i,i-1)));
      for(t=1,n,if(gcd(t,n)!=1,next);
        my(w=sum(i=1,#roots,powers[1+((2*t*roots[i])%n)*(L/n)]),v=lift(w^2));
        my(u=if(m==1,0,if(m==n,t,lift(Mod(t,m)/3))),key=[m,u^2%m],prev);
        if(mapisdefined(byKey,key,&prev),if(prev!=v,error("CRT equality")),mapput(byKey,key,v));
        listput(values,v);phases++;
        if(t==1 && L==n && n<=105,
          if(poldegree(minpoly(w^2))!=eulerphi(n)/2^omega(n),error("magnitude degree"));
          degrees++)));
    if(#Set(Vec(values))!=#byKey,error("distinct magnitudes collide")));
  print(["exact cyclotomic unit phases",phases,"minimal polynomial degrees",degrees])
};
iferr(checkFixedGaps();checkExactMagnitudes(),E,print(E);quit(1));quit(0);
