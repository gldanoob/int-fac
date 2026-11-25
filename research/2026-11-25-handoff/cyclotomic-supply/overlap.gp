\\ Run from repository root.
read("experiments/hidden-divisor-lattice.gp");

relativeRows(N,k) = {
  my(x='x,t='t,psi=polcyclo(k,t),d=poldegree(psi),z=Mod(t,psi));
  my(rows=List());
  for(j=1,k-1,
    if(gcd(j,k)>1,next);
    my(m=k/gcd(k,j+1), e=eulerphi(m), w=z^(j+1),
      basis=matrix(d,e,i,h,polcoef(lift(w^(h-1)),i-1)),
      normpoly=prod(h=1,k,if(gcd(h,k)==1 && ((h-1)*(j+1))%k==0,x-z^h,1)));
    my(F=sum(h=0,d/e,my(v=Col(vector(d,i,polcoef(lift(polcoef(normpoly,h)),i-1))),
      coeffs=matinverseimage(basis,v));
      if(denominator(coeffs)!=1,error("nonintegral coefficient"));
      sum(i=1,e,coeffs[i]*N^(i-1))*x^h));
    if(pollead(F)!=1 || poldegree(F)!=d/e,error("wrong relative degree"));
    listput(rows,[j,F,subst(polcyclo(m,t),t,N)])
  );
  Vec(rows)
};

checkRows(p,q,k) = {
  my(x='x, N=p*q, F=polcyclo(k,x), g=gcd(subst(F,x,p),subst(F,x,q)),
     ff=factor(g), rows=relativeRows(N,k), used=Set());
  for(i=1,matsize(ff)[1],
    my(ell=ff[i,1], h=ell^ff[i,2], which);
    if(k%ell==0,if(ff[i,2]!=1,error("ramification"));next);
    which=select(row->lift(Mod(p,h)^row[1])==q%h,rows);
    if(#which!=1,error("nonunique j"));
    if(which[1][3]%h || subst(which[1][2],x,p)%h,error("residue failed"));
    used=setunion(used,[which[1][1]])
  );
  [k,N,g,used]
};

recoverCubic(N,bound,dim) = {
  my(x='x,amin=sqrtint(N\2),amax=sqrtint(N),used=0);
  for(i=0, logint(N-1,2),
    for(j=0,logint(3*amax+1,2),
      my(A=2^i,C=2^j,R,rows);
      if(A>amax || A*C*12*bound<N,next);
      my(logA=log(A),logC=log(C),LN=log(N),
         exponent=log(amin)^2/LN+logA^2/log(N^2+N+1)+logC^2/(2*log(N-1)));
      R=max(1,floor(exp(exponent)/4));
      forstep(lo=amin,amax,2*R+1,
        my(center=lo+R, S, rs);
        rows=[[x+center,N,0,amin],[x+center+N+1,N^2+N+1,0,A],
             [(x+center)^2+(x+center)+1,N-1,0,C]];
        for(h=1,3,my(row=rows[h]);
          rows[h][3]=floor(dim*log(row[4])/(poldegree(row[1])*log(row[2])))
        );
        used++;
        S=hiddenDivisorShortPolynomial(rows,dim,R);
        rs=hiddenDivisorRoots(S,rows,R);
        foreach(rs,z,if((center+z)>1 && N%(center+z)==0,return([center+z,used,R])))
      )
    )
  );
  [0,used,0]
};

firstPrimeInClass(lo,h,residue,skip) = {
  my(n=lo+(residue-lo)%h);
  while(n==skip || !isprime(n),n+=h);
  if(n>2*lo,error("unbalanced fixture"));
  n
};

{
  my(witnesses=0);
  foreach([3,4,5,6,8,10,12,15,16,20,24,30,35],k,
    my(ell=nextprime(k+1), classes=0);
    while(ell%k!=1,ell=nextprime(ell+1));
    my(h=ell^2, root=lift(znprimroot(h)^(eulerphi(h)/k)),
       lo=256*h,p=firstPrimeInClass(lo,h,root,0));
    for(j=1,k-1,
      if(gcd(j,k)>1,next);
      my(q=firstPrimeInClass(lo,h,lift(Mod(root,h)^j),p), report=checkRows(p,q,k));
      if(!setsearch(report[4],j) || report[3]%h,error("missing fixture class"));
      classes++;
    );
    if(classes!=eulerphi(k),error("fixture coverage"));
    witnesses+=classes;
    print([k,ell,h,classes])
  );
  print(["total",witnesses]);
  my(got=recoverCubic(108802277,40,16));
  if(got[1]!=7639,error("factor ",got));
  print(got)
}
