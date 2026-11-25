read("experiments/cyclotomic-multiples.gp");

nonpureInert(f,k,p) = poldegree(f)==k && poldegree(f-x^k)>0 && polisirreducible(Mod(1,p)*f);

checkPrimeIndexPrediction(k,height,ps,qs,extras,both=0) = {
  my(L=lcm(vector(k,j,j)), rows=0,good=0,certified=0,exceptions=0,forced=0,tests=0);
  \\ Record the whole box so every proper gcd is checked, including its orientation.
  my(probes=List());
  for(s=2,k,forvec(v=vector(s,i,[-height,height]),listput(probes,x^s+Polrev(v))));
  foreach(ps,p,
    if(!isprime(p),error("nonprime"));
    my(h=subst(polcyclo(k),x,p),inert=vector(#probes,i,
      nonpureInert(probes[i],k,p)));
    foreach(qs,q,
      if(!isprime(q),error("nonprime"));if(p==q,next);
      my(g=gcd(h,q*(q^L-1)),base=h,other=vector(#probes));
      if(both,
        base=lcm(h,subst(polcyclo(k),x,q));
        other=vector(#probes,i,nonpureInert(probes[i],k,q)));

      foreach(extras,a,
        my(d=base*a>>valuation(base*a,2),n=p*q,bound=a*max(g,gcd(k,p-1)));
        if(both,my(J=lcm(vector(k-1,j,j)));
          bound=max(gcd(d,p*(p^J-1)),gcd(d,q*(q^J-1))));
        my(cert=bound<=logint(min(p,q),2) && (1+k*height)^bound<min(p,q),ok=1);
        rows++; certified+=cert;
        for(i=1,#probes,my(v=cyclotomicCoefficientGcd(n,d,probes[i]));
          my(split=(v!=1 && v!=n),want=if(inert[i]==other[i],0,if(inert[i],p,q)));
          if((split && v!=want) || (!split && want),ok=0;if(cert,error("certified discrepancy ",[k,p,q,a,probes[i]])));
          if(split && cert,forced++);tests++);
        good+=ok;exceptions+=!ok)));
  if(!certified || !forced,error("empty certificate test"));
  [k,height,rows,good,certified,exceptions,forced,tests]
};
checkCyclicPrefixes(k,conductors) = {
  my(m=#conductors,F=apply(l->polsubcyclo(l,k),conductors),Q=prod(i=1,m,conductors[i]));
  my(bad=prod(i=1,m,poldisc(F[i])),counts=vector(m),survivors=vector(m),eligible=0);
  for(i=1,m,if(polcoef(F[i],k-1)!=1 || !polisirreducible(F[i]),error("Gaussian period")));
  for(r=1,Q,if(gcd(r,Q)==1,for(i=1,m,my(l=conductors[i]);
    if(Mod(r,l)^((l-1)/k)!=1,break);counts[i]++)));
  if(counts!=vector(m,i,eulerphi(Q)/k^i),error("cyclic prefix masses"));
  forprime(p=1000,20000,if(bad%p==0,next);eligible++;
    my(miss=1);
    for(i=1,m,my(l=conductors[i],inert=Mod(p,l)^((l-1)/k)!=1);
      if(inert!=polisirreducible(Mod(1,p)*F[i]),error("cyclic Frobenius"));
      miss=miss && !inert;survivors[i]+=miss));
  ["cyclic prefixes",k,eulerphi(Q),counts,eligible,survivors]
};

checkExactCoveredPair() = {
  my(smallest=0,example=[],pairs=0,bounds=0);
  forprime(q=5,2000,forprime(p=q+1,5*q,
    my(hp=p^2+p+1,hq=q^2+q+1,d=p-q);pairs++;
    if(gcd(hp,hq)>d*(d^2+3),error("shifted cubic-order gcd"));
    if(q>d^2+d+1,
      if(gcd(hp,q*(q^2-1))>d^2*(d+1)^2+3,error("shifted reducible gcd"));bounds++);
    if(hp%hq==0 && (!smallest || hp/hq<smallest),smallest=hp/hq;example=[q,p])));
  if(smallest!=19 || example!=[37,163],error("extremal order quotient"));
  ["shifted orders",pairs,bounds,smallest,example]
};

run() = {
  my(p3=[1000003,1000033,1000037,1000039,1000081],q3=[1000099,1000117,1000121,1000133,1000151,1000159,1000171]);
  my(p5=[1000000007,1000000009,1000000021],q5=[1000000033,1000000087,1000000093]);
  print(checkExactCoveredPair());
  print(checkCyclicPrefixes(3,[7,13,19,31]));
  print(checkCyclicPrefixes(5,[11,31,41]));
  my(small=checkPrimeIndexPrediction(3,2,[41,43,47,53],[59,61,67,71,73],[1,3,5]));
  if(small[6]!=9,error("small exceptional pairs"));print(small);
  print(checkPrimeIndexPrediction(3,2,p3,q3,[1,2,3,5]));
  print(checkPrimeIndexPrediction(5,1,p5,q5,[1,2,3]));
  print(["both orders",checkPrimeIndexPrediction(3,2,p3,q3,[1,3,5],1)]);
  print(["both orders",checkPrimeIndexPrediction(5,1,p5,q5,[1,3],1)]);
};
iferr(run(),E,print(E);quit(1));quit(0);
