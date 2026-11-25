\\ Replay with gp -fq cubic-miss-fields.gp | python cubic-miss-density.py.
\\ Set CUBIC_DENSITY_BRUTE=1 and pass -s 64000000 for independent H=1,2 checks.

pureRadicand(f) = {
  for(m=2,100,if(!ispower(m,3) && nfisisom(f,x^3-m),return(m)));
  error("unexpected pure field",f);
};

fields(H) = {
  my(F=List());
  forvec(v=vector(3,j,[-H,H]),
    if(!(v[2] || v[3]),next());
    my(f=x^3+Polrev(v));
    if(polisirreducible(f),listput(F,polredabs(f))));
  Set(Vec(F));
};

checkRay(F) = {
  my(B=bnfinit(y^2-y+13,1), L=select(f->quaddisc(nfdisc(f))==-51,F));
  my(C=bnrinit(B,6).cyc, cond=List());
  if(B.disc!=-51 || !bnfcertify(B) || sum(i=1,#C,C[i]%3==0)!=2,error("ray class rank"));
  if(vecsort(apply(nfdisc,L))!=[-1836,-459,-204],error("unexpected -51 fields"));
  foreach(L,f,
    my(m=sqrtint(nfdisc(f)\(-51)), c=rnfconductor(B,f,2)[1]);
    if(c[1]!=idealhnf(B,m) || #c[2],error("relative conductor",f,c));
    listput(cond,m));
  print([0,-51,2,vecsort(Vec(cond))]);
};

checkCyclic(m) = {
  for(bit=0,1,
    my(total=0, split=0);
    for(a=1,m-1,
      if(gcd(a,m)!=1 || (kronecker(a,if(m==9,3,m))==-1)!=bit,next());
      total++;
      if(Mod(a,m)^(eulerphi(m)/3)==1,split++));
    if(3*split!=total,error("cyclic independence",m,bit)));
};

brute(H,F) = {
  my(D=apply(f->quaddisc(nfdisc(f)),F), c=sum(j=1,#D,D[j]==1));
  D=select(d->d!=1,D);
  if(#Set(D)!=#D,error("multiple resolvent in brute test"));
  my(P=Set(concat(apply(d->Vec(factor(abs(d))[,1]),D))));
  P=select(p->p>3,P);
  for(branch=1,2,
    my(res=vector(4,j,chinese(Mod(2*j-1,8),Mod(branch,3))));
    foreach(P,p,
      my(g=lift(znprimroot(p)));
      res=vector(2*#res,j,chinese(res[(j+1)\2],Mod(if(j%2,1,g),p))));
    my(q=sum(i=1,#res,3^(#D-sum(j=1,#D,kronecker(D[j],lift(res[i]))==1)))
         / (#res*3^(#D+c)));
    print([-1,H,branch,numerator(q),denominator(q)]));
};

runExport() = {
  my(F=vector(5,h,fields(h)));
  checkRay(F[5]);
  foreach([7,9,13,19],m,checkCyclic(m));
  for(h=1,5,foreach(F[h],f,
    my(d=nfdisc(f));
    print([h,d,if(quaddisc(d)==-3,pureRadicand(f),0)])));
  if(getenv("CUBIC_DENSITY_BRUTE")=="1",for(h=1,2,brute(h,F[h])));
};
iferr(runExport(),E,print(E);quit(1));
quit;
