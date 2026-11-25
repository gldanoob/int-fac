\\ Only the reference routine factors its argument. All density calculations use integer endpoints.
default(realprecision,110);

twistedPrefix(m,Y) = {
  my(local=1,euler=1.);
  forprime(p=2,Y,
    my(k=valuation(m,p)\2,chi=kronecker(-m/p^(2*k),p));
    euler*=p/(p-chi);
    if(k,local*=1+(1-chi)*(p^k-1)/(p^k*(p-1)))
  );
  3*sqrt(m)*euler*local/Pi
};

twistedReference(u) = {
  my(F=factor(u),d=prod(i=1,matsize(F)[1],F[i,1]^(F[i,2]%2)));
  my(count=if(d==3,1,3*qfbclassno(-d)));
  for(i=1,matsize(F)[1],
    my(p=F[i,1],k=F[i,2]\2);
    count*=p^k+(1-kronecker(-d,p))*(p^k-1)/(p-1)
  );
  count
};

twistedDyadStart(u,k) = {
  my(s=sqrtint((2^(2*k)-1)\u)+1);
  sqrtint((s-2)\(4*u))+1
};

\\ First j for which c*(1+4*u*j^2) is at least z*step.
twistedCrossing(u,c,z,step) = {
  my(r=ceil((z*step/c-1)/(4*u)));
  if(r<=0,0,1+sqrtint(r-1))
};

\\ Count every differing quotient, merging overlapping discrepancy intervals.
twistedDifferences(u,c,d,k,t,lo,hi) = {
  my(small=min(c,d),large=max(c,d),step=2^(k-t),last=lo-1,total=0);
  my(upper=floor(large*(1+4*u*hi^2)/step));
  for(z=1,upper,
    my(first=max(lo,twistedCrossing(u,large,z,step)));
    my(end=min(hi,twistedCrossing(u,small,z,step)-1));
    if(end>last && end>=first,total+=end-max(last+1,first)+1;last=end)
  );
  total
};

checkTwistedDigits() = {
  my(inputs=[143,187,11^3*13^2],cuts=[257,1021,4093],Ts=[0,2]);
  my(sums=matrix(#cuts,#Ts),counts=0,raw=0,maxBits=0,near=0,transfers=0);
  for(nidx=1,#inputs,
    my(n=inputs[nidx],a0=(3*n)%8);
    forprime(q=17,257,
      if(q%8!=1 || n%q==0,next);
      foreach([0,1,3],h,foreach([1,105],F,
        my(u=a0*q*n^(2*h+1)*F^2,c=twistedReference(u),k=8*(logint(u,2)+1)+16);
        my(lo=twistedDyadStart(u,k),hi=twistedDyadStart(u,k+1)-1,L=hi-lo+1);
        my(adj=twistedDifferences(u,c,c+1,k,0,lo,hi));
        if(adj/L>20*(c/sqrt(u)+1)/c,error("adjacent proportion ",u));
        if(adj,near++);
        if(u<10^7 && c!=3*qfbhclassno(u),error("independent Hurwitz reference ",u));
        for(v=1,#cuts,
          my(estimate=floor(2^80*twistedPrefix(u,cuts[v]))/2^80);
          for(w=1,#Ts,
            my(z=twistedDifferences(u,c,estimate,k,Ts[w],lo,hi));
            sums[v,w]+=1.*z/L
          );
          if(h==0 && F==1,
            my(j=(lo+hi)\2,s=1+4*u*j^2,M=u*s^2,v1=twistedPrefix(M,cuts[v]));
            if(abs(v1/s-estimate)>2^-79,error("direct padded prefix ",[M,cuts[v]]));
            if(logint(M,2)\2!=k,error("dyadic position"));
            maxBits=max(maxBits,logint(M,2)+1);transfers++
          )
        );
        counts++
      ))
    )
  );
  \\ A small dyad admits a literal complete scan for the interval union.
  foreach([3,11,19,35,59],u,
    my(c=twistedReference(u),k=14,lo=twistedDyadStart(u,k),hi=twistedDyadStart(u,k+1)-1);
    foreach([c+1,4*c/3,5*c],d,foreach([0,2,4],t,
      my(step=2^(k-t),literal=sum(j=lo,hi,floor(c*(1+4*u*j^2)/step)!=floor(d*(1+4*u*j^2)/step)));
      if(literal!=twistedDifferences(u,c,d,k,t,lo,hi),error("interval enumeration ",[u,d,t]));
      raw++
    ))
  );
  if(near<counts/2 || !transfers || !sums[1,1] || sums[3,1]>=sums[1,1],error("fixture coverage"));
  print(["structured bases",counts,"with exact adjacent-count disagreements",near,
         "direct padded prefix calls",transfers,"maximum padded bits",maxBits,"literal interval checks",raw]);
  print(["prime cutoffs",cuts,"mean wrong quotient fractions in millionths, t=0 and 2",
         matrix(#cuts,#Ts,i,j,round(10^6*sums[i,j]/counts))]);
  my(p=263,z=269,n=p*z,F=1,a0=(3*n)%8);
  forprime(r=3,257,F*=r);
  my(floorError=((1+p)*(1+z)-n)/((1+p)*(1+z)+n),roughChecks=0);
  forprime(q=17,113,
    if(q%8!=1,next);
    my(u=a0*q*n*F^2,c0=twistedReference(u),c1=twistedReference(u*n^2));
    my(E0=twistedPrefix(u,257),E1=twistedPrefix(u*n^2,257));
    if(c1!=(1+p)*(1+z)*c0 || abs(E1/(n*E0)-1)>10^-95,error("rough shared prefix ",q));
    if(max(abs(E0/c0-1),abs(E1/c1-1))+10^-95<floorError,error("unavoidable pair error"));
    roughChecks++
  );
  print(["rough twist pairs",roughChecks,"shared-prefix relative-error floor",floorError]);
};

iferr(checkTwistedDigits(),err,print(err);quit(1));
