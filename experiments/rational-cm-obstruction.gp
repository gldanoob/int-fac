\\ Run from the repository root with PARI/GP.
cmFields=[-1,-2,-3,-7,-11,-19,-43,-67,-163];
cmDiscs=[-3,-4,-7,-8,-11,-12,-16,-19,-27,-28,-43,-67,-163];
cmJ=apply(d->-polcoef(polclass(d),0),cmDiscs);

cmModels(j,p) = {
  my(c=ellfromj(Mod(j,p)),A=c[4],B=c[5],u=Mod(znprimroot(p),p));
  if(!B,return(vector(gcd(4,p-1),i,[u^(i-1)*A,B])));
  if(!A,return(vector(gcd(6,p-1),i,[A,u^(i-1)*B])));
  [[A,B],[u^2*A,u^3*B]]
};

cmAbscissa(A,B,t) = if(!A,t^3/B,if(!B,t^2/A,A*t/B));
cmFiber(A,B,z,p) = {
  if(!A,return(polrootsmod('x^3-z*B,p)));
  if(!B,return(polrootsmod('x^2-z*A,p)));
  [z*B/A]
};

{
  my(bins=vector(512),inert=List());
  forprime(p=100001,200000,
    my(mask=sum(i=1,#cmFields,(kronecker(cmFields[i],p)==-1)*2^(i-1)));
    bins[mask+1]++;
    if(mask==511,listput(inert,p))
  );
  if(vecsum(bins)!=8392 || #inert!=15 || vecmin(bins)!=7 || vecmax(bins)!=28,
    error("prime sign bins"));
  print(["sign masks",vecsum(bins),vecmin(bins),vecmax(bins),#inert]);
  my(checks=0,small=3167,m=24,maxWeber=0);
  foreach(concat(Vec(inert),[small,14423,18191]),p,
    foreach(cmJ,j,
      my(weber=List());
      foreach(cmModels(j,p),c,
        my(A=c[1],B=c[2],E=ellinit(c),group=ellgroup(E));
        if(ellcard(E)!=p+1 || prod(i=1,#group,group[i])!=p+1 ||
           (#group>1 && group[2]>2),error("CM trace or invariant factors"));
        checks++;
        if(p==small,
          my(killed=1,points=1);
          for(t=0,p-1,
            my(xx=Mod(t,p),ys=ellordinate(E,xx));
            points+=#ys;
            if(#ys && ellmul(E,[xx,ys[1]],m)==[0],
              killed+=#ys;listput(weber,lift(cmAbscissa(A,B,xx)))
            )
          );
          if(points!=p+1 || killed!=prod(i=1,#group,gcd(m,group[i])) ||
             killed>2*gcd(m,p+1),error("direct point count"))
        )
      );
      if(p==small,
        my(w=#Set(Vec(weber)));
        if(!w || w>m^2,error("geometric torsion abscissas"));
        maxWeber=max(maxWeber,w)
      )
    )
  );
  print(["curves, direct models, largest union",checks,2*#cmJ,maxWeber]);
}

{
  my(tested=0,hits=0);
  foreach([[[-36,0],[12,36]],[[0,-2],[3,5]]],v,
    my(E=ellinit(v[1]),P=v[2]);
    if(ellorder(E,P)!=0,error("rational mark has finite order"));
    for(m=1,30,
      my(den=denominator(ellmul(E,P,m)[1]));
      forprime(p=17,199,
        if(E.disc%p,
          my(Ep=ellinit(v[1],p),iszero=ellmul(Ep,P,m)==[0]);
          if((den%p==0)!=iszero,error("rational reduction"));
          tested++;hits+=iszero
        )
      )
    )
  );
  if(!hits,error("no exceptional rational reductions tested"));
  print(["rational reductions, identity reductions",tested,hits]);
}

{
  my(p=14423,q=18191,N=p*q,M=lcm(vector(11,i,i)));
  my(probes=0,hits=0,dead=0);
  foreach([sqrtint(N),sqrtnint(N,3),sqrtint(2*N)+1,sqrtnint(3*N,3)-1],z,
    my(localHits=0);
    foreach([p,q],t,
      if(gcd(t+1,M)!=24,error("local scalar"));
      foreach(cmJ,j,foreach(cmModels(j,t),c,
        my(A=c[1],B=c[2],E=ellinit(c));
        foreach(cmFiber(A,B,Mod(z,t),t),xx,
          my(ys=ellordinate(E,xx));
          if(#ys,
            my(P=[xx,ys[1]],k=ellmul(E,P,M)==[0]);
            if(k!=(ellmul(E,P,24)==[0]),error("kernel reduction"));
            probes+=#ys;localHits+=k*#ys
          )
        )
      ))
    );
    dead+=(localHits==0);hits+=localHits
  );
  if(!probes || !dead,error("empty floor probe example"));
  print(["floor marks, local lifts, identity lifts, complete misses",4,probes,hits,dead]);
}

{
  my(discs=apply(quaddisc,cmDiscs),orders=0,ordinary=0,inert=0,anomalous=0);
  my(fields=apply(d->nfinit(quadpoly(d)),discs),localChecks=0);
  forprime(p=167,997,
    for(i=1,#cmJ,
      my(d=discs[i],isSplit=kronecker(d,p)>0,normOrders=List(),bound=sqrtint(4*p));
      if(isSplit,
        for(t=-bound,bound,
          my(v=(t^2-4*p)/d,f);
          if(denominator(v)==1 && issquare(v,&f),
            my(n=p+1-t);
            listput(normOrders,n);
            if(p<=251,
              my(field=fields[i],pi=(t-f*(d%2))/2+'x*f);
              if(nfeltnorm(field,pi)!=p || nfeltnorm(field,1-pi)!=n,
                error("Frobenius norm",[p,d,t]));
              foreach([2,3,5,7,11,17],l,
                my(primes=idealprimedec(field,l));
                if(sum(a=1,#primes,primes[a].f*idealval(field,1-pi,primes[a]))!=valuation(n,l),
                  error("ideal valuation",[p,d,t,l]));
                localChecks++
              )
            )
          )
        ),listput(normOrders,p+1)
      );
      foreach(cmModels(cmJ[i],p),c,
        my(n=ellcard(ellinit(c)));
        if(!setsearch(Set(Vec(normOrders)),n),error("unlisted CM order",[p,d,n]));
        if(isSplit,ordinary++,inert++);
        anomalous+=(n==p);orders++
      )
    )
  );
  if(!ordinary || !inert || !anomalous || !localChecks,error("missing CM branch"));
  print(["twists, ordinary, supersingular, trace one, ideal valuations",orders,ordinary,inert,anomalous,localChecks]);
}
