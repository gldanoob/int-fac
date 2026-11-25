\\ Numerical checks of the scalar brackets, sparse complex powers and CRT axes.
default(realprecision, 38);

bracket(a,b,m,sgn) = {
  my(z=exp(-2*Pi*I*a), w=exp(-2*Pi*I*b), za=1, wb=1);
  my(coeff=vector(m+1), t, weight);
  coeff[1]=(b-a)+sgn/(m+1);
  for(j=1,m,
    za*=z; wb*=w; t=j/(m+1);
    weight=Pi*t*(1-t)*(1/tan(Pi*t))+t;
    coeff[j+1]=weight*(za-wb)/(2*Pi*I*j)+sgn*(1-t)*(za+wb)/(2*(m+1)));
  Polrev(coeff)
};
value_at(pol,z)=2*real(subst(pol,'x,z))-real(polcoef(pol,0));

check_brackets(blocks) = {
  my(n=prod(i=1,#blocks,blocks[i]), roots=select(x->x^2%n==1,[1..n]));
  my(r=#blocks, period=16, m=1535, angles=vector(n), signals=vector(n));
  my(axes=vector(r,i,4*(n/blocks[i])*lift(Mod(n/blocks[i],blocks[i])^-1)%n));
  my(max_ratio=0, raw, z, actual, lo, hi, band, checks=0, ambiguous=0);
  for(t=0,n-1,
    raw=sum(i=1,#roots,cos(4*Pi*((t*roots[i])%n)/n));
    signals[t+1]=log(abs(raw));
    if(abs(signals[t+1]-sum(i=1,r,log(abs(2*cos(4*Pi*lift(Mod(t,blocks[i])/Mod(n/blocks[i],blocks[i]))/blocks[i])))))>1e-28,error("CRT"));
    if(abs(signals[t+1])>=period/2,error("period"));
    angles[t+1]=exp(2*Pi*I*signals[t+1]/period));
  for(qi=1,3,
    my(q=[0,-1,signals[2]][qi]);
    my(upper=bracket((q-1/1000)/period,1/2,m,1), lower=bracket((q+1/1000)/period,1/2,m,-1));
    my(center=vector(n), comp=vector(n), deviation=0, axial, approx);
    for(t=0,n-1,
      z=angles[t+1]; lo=value_at(lower,z); hi=value_at(upper,z);
      actual=exp(signals[t+1]-q); band=abs(actual-1)<=2^-12;
      if(band, ambiguous++);
      for(bit=0,1,if(band || bit==(actual>1),
        if(lo>bit+1e-25 || hi<bit-1e-25,error("one-sided bracket")); checks++));
      center[t+1]=(hi+lo)/2; deviation+=(hi-lo)/(2*n); comp[t+1]=(signals[t+1]>q));
    for(i=1,r,
      axial=sum(t=0,n-1,comp[t+1]*cos(2*Pi*t*axes[i]/n))/n;
      approx=sum(t=0,n-1,center[t+1]*cos(2*Pi*t*axes[i]/n))/n;
      if(abs(axial-approx)>deviation+1e-25,error("axis error"));
      if(qi<=2,if(axial<=0,error("axis"));max_ratio=max(max_ratio,deviation/axial))));
  [checks,ambiguous,max_ratio]
};

\\ g_t has only even harmonics. The beta integral supplies harmonic zero and
\\ successive even coefficients have ratio (it/2-j)/(1+it/2+j).
levels_on_grid(d,t,limit) = {
  my(c0=gamma(1+I*t)/gamma(1+I*t/2)^2, c=c0, jmax=2^(limit-1));
  my(coeff=vector(jmax), previous, f, out=matrix(d,limit+1), phases);
  if(abs(abs(c0)^2-2*tanh(Pi*t/2)/(Pi*t))>1e-28,error("characteristic function"));
  for(j=1,jmax,c*=(I*t/2-(j-1))/(I*t/2+j);coeff[j]=c);
  for(x=0,d-1,
    previous=0; phases=vector(d,k,2*cos(4*Pi*((k*x)%d)/d));
    for(h=0,limit,
      f=c0+sum(j=1,(2^h-1)\2,coeff[j]*(1-2*j/2^h)*phases[1+(j-1)%d]);
      out[x+1,h+1]=f-previous; previous=f));
  out
};
sparse_test(t) = {
  my(ds=[5,7,9], cutoff=12, levels=vector(3,i,levels_on_grid(ds[i],t,cutoff)));
  my(n=vecprod(ds), errors=vector(cutoff+1), approximant, total, target, x);
  for(u=0,n-1,
    x=vector(3,i,u%ds[i]);
    target=exp(I*t*sum(i=1,3,log(abs(2*cos(2*Pi*x[i]/ds[i])))));
    approximant=0;
    for(h=0,cutoff,
      total=0;
      for(j=0,h,for(k=0,h-j,total+=levels[1][x[1]+1,j+1]*levels[2][x[2]+1,k+1]*levels[3][x[3]+1,h-j-k+1]));
      approximant+=total;
      errors[h+1]+=abs(approximant-target)/n));
  if(errors[13]>=errors[9] || errors[9]>=errors[5],error("sparse error",errors));
  [errors[5],errors[9],errors[13]]
};

{
  my(count=0,amb=0,worst=0,result);
  foreach([[5,7],[7,11],[11,13],[5,7,11],[7,9,13]],ds,
    result=check_brackets(ds);count+=result[1];amb+=result[2];worst=max(worst,result[3]));
  if(amb==0,error("no ambiguous comparisons exercised"));
  print(count," scalar replies bracketed, ",amb," ambiguous grid points, largest mean-gap/axis ratio ",precision(worst,6));
  foreach([.5,2,6],t,result=sparse_test(t);print("t=",t," sparse mean errors at levels 4,8,12: ",precision(result,6)));
}
