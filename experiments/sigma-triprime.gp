\\ The roots of f have product r and product of (root-1) equal to ph.
sigmaEqualTriprime(r,ph,s,e) = {
  my(f='x^3-'t*'x^2+('t+r-1-ph)*'x-r);
  my(h=polresultant(f,sum(j=0,e,'x^j),'x)-s);
  foreach(Vec(nfroots(,h)),total,
    if(denominator(total)!=1 || total<=0,next());
    foreach(Vec(nfroots(,subst(f,'t,total))),p,
      if(denominator(p)==1 && p>1 && r%p==0 && isprime(p),return(p))
    )
  );
  0
};

sigmaTriprimeCandidate(m,s,c,d) = {
  my(p,support=gcd(m,d^logint(m,2)));
  if(support<m,
    if(isprimepower(support,&p) || isprimepower(m/support,&p),return(p));
    return(0)
  );
  my(left=m,e=0);
  while(left%d==0,left/=d;e++);
  if(left>1,
    my(g=gcd(d,left));
    if(isprimepower(g,&p) || isprimepower(d/g,&p),return(p));
    return(0)
  );
  foreach(Vec(nfroots(,'x^2-(d+1-c)*'x+d)),r,
    if(denominator(r)==1 && r>1 && d%r==0 && isprime(r),return(r))
  );
  sigmaEqualTriprime(d,c,s,e)
};

\\ Given only m and s, return a proven prime divisor, or 0 on a miss.
sigmaTriprimePrime(m,s) = {
  if(type(m)!="t_INT" || type(s)!="t_INT" || m<2 || s<1,error("expected m>=2 and s>=1"));
  my(p);
  if(isprimepower(m,&p),return(p));
  forprime(a=2,48,if(m%a==0,return(a)));
  my(cf=contfrac(m/s),v=contfracpnqn(cf,#cf-1));
  for(j=1,#v,
    my(c=v[1,j],d=v[2,j]);
    if(c>0 && d>1 && m%d==0,
      p=sigmaTriprimeCandidate(m,s,c,d);
      if(p,return(p))
    )
  );
  0
};

checkSigmaTriprimeCase(primes,powers) = {
  my(m=prod(i=1,#primes,primes[i]^powers[i]));
  my(s=prod(i=1,#primes,(primes[i]^(powers[i]+1)-1)/(primes[i]-1)));
  my(found=List());
  while(m>1,
    my(p=sigmaTriprimePrime(m,s));
    if(p<=1 || !isprime(p) || m%p,error("triprime recovery at ",[primes,powers]));
    my(e=valuation(m,p),block=p^e);
    listput(found,[p,e]);m/=block;s/=(p*block-1)/(p-1)
  );
  if(s!=1 || vecsort(Vec(found))!=vector(#primes,i,[primes[i],powers[i]]),
    error("triprime factors at ",[primes,powers]));
  1
};

checkSigmaTriprime() = {
  checkSigmaTriprimeCase([53,59,67],[28,28,28]);
  checkSigmaTriprimeCase([53,59,67],[28,30,36]);
  checkSigmaTriprimeCase([53,59,107],[28,28,28]);
  checkSigmaTriprimeCase([53,59,2147483647],[28,28,28]);
  checkSigmaTriprimeCase([53,59],[28,28]);
  \\ For equal squares the exact totient lies three integers below rounding.
  my(r=53*59*67,s=(1+53+53^2)*(1+59+59^2)*(1+67+67^2),hit=0);
  for(c=round(r^3/s)-4,round(r^3/s),
    if(sigmaEqualTriprime(r,c,s,2),hit=1;break())
  );
  if(!hit,error("comparable equal squares"));
  if(sigmaTriprimePrime(53*59,53*59)!=0,error("false triprime hit"));
  5
};
