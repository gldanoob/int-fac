\\ Exact finite identities behind the upper/lower extremal trace mass.

units(D) = if(D==-3,6,if(D==-4,4,2));
order_mass(D) = qfbclassno(D)/units(D);

mass_check(D) = {
  my(v=coredisc(D,1),d=v[1],f=v[2],fac=factor(f),h=order_mass(d));
  my(local=1,imprimitive=1);
  for(j=1,matsize(fac)[1],
    my(ell=fac[j,1],a=fac[j,2],s=kronecker(d,ell));
    local*=ell^(-a)+(1-s/ell)*sum(b=1,a,ell^(b-a));
    imprimitive*=1-s/ell;
  );
  my(value=qfbhclassno(-D)/2);
  if(value!=h*f*local || value< h*f*imprimitive || h*f*imprimitive!=order_mass(D),
    error("order class formula",D));
  value;
}

complete_products(p) = {
  my(pr=[3,5,7],m=prod(i=1,#pr,pr[i]),count=0);
  for(k=1,4,
    my(product=1);
    for(i=1,#pr,
      my(ell=pr[i],s=sum(t=0,ell-1,kronecker(t^2-4*p,ell)));
      if(s!=-1,error("complete character"));
      product*=sum(t=0,ell-1,(1-kronecker(t^2-4*p,ell)/ell)^k)/ell;
    );
    my(direct=sum(t=0,m-1,prod(i=1,#pr,(1-kronecker(t^2-4*p,pr[i])/pr[i])^k))/m);
    if(product!=direct,error("complete product"));
    count++;
  );
  my(admissible=sum(t=0,m-1,prod(i=1,#pr,kronecker(t^2-4*p,pr[i])==-1)));
  my(expected=prod(i=1,#pr,sum(t=0,pr[i]-1,kronecker(t^2-4*p,pr[i])==-1)));
  if(admissible!=expected || admissible<prod(i=1,#pr,(pr[i]-1)/2),error("CRT signs"));
  count+1;
}

replay() = {
  my(primes=0,traces=0,subsets=0,classes=0,crt=0,small=100,large=0);
  forprime(p=11,3001,
    my(a=List(),multiplicity=Map());
    for(t=-sqrtint(p),sqrtint(p),
      my(D=t^2-4*p,d=coredisc(D));
      mapput(multiplicity,d,1+if(mapisdefined(multiplicity,d),mapget(multiplicity,d),0));
      if(t==0 || (p+1-t)%8!=4,next);
      my(h=mass_check(D),lambda=2*(h-mass_check(D/4)));
      if(lambda<h || lambda>2*h || denominator(lambda)!=1,error("Legendre interval"));
      listput(a,lambda);
      traces++;
    );
    my(mt=Mat(multiplicity));
    if(vecmax(mt[,2])>12,error("quadratic-field fibers"));
    classes+=matsize(mt)[1];
    my(v=vecsort(Vec(a)),prefix=0);
    for(m=1,#v,
      prefix+=v[m];
      my(r=prefix*log(2+log(#v/m))/(m*sqrt(p)));
      small=min(small,r);large=max(large,r);subsets++;
    );
    if(p<500,crt+=complete_products(p));
    primes++;
  );
  print("primes, traces, minimum prefix masses, field-fiber checks, CRT identities = ",
        [primes,traces,subsets,classes,crt]);
  print("observed normalized extremal ratios = ",[small,large]);
}
iferr(replay(),e,print(e);quit(1));
quit;
