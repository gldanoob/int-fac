\\ Replay the independent ramification and mark construction on small boxes.
\\ Run gp -q experiments/classical-quintic-partners.gp.

lehmer(t) = y^5+t^2*y^4-(2*t^3+6*t^2+10*t+10)*y^3+(t^4+5*t^3+11*t^2+15*t+5)*y^2+(t^3+4*t^2+10*t+10)*y+1;
branch(t) = t^4+5*t^3+15*t^2+25*t+25;
lift_simple(f,a,h) = {
  my(correction=Mod(subst(f,variable(f),a)\h,h)/subst(deriv(f),variable(f),Mod(a,h)));
  lift(Mod(a-h*lift(correction),h^2));
}

replay() = {
  my(F=lehmer(t), D=branch(t),G=4*t^6+30*t^5+65*t^4-200*t^2-125*t+125);
  if(poldisc(F,y)!=(t^3+5*t^2+10*t+7)^2*D^4,error("discriminant"));
  if(3125*subst(F,y,-t^2/5)!=D*G || gcd(G,D)!=1,error("Eisenstein constant"));
  my(w=3,rs=List(),targets=List(),hs=List());
  forprime(r=11,2000,
    if(#rs==w,break);
    my(roots=polrootsmod(D,r));
    if(!#roots || polresultant(D,G,t)%r==0,next);
    my(v=lift_simple(D,lift(roots[1]),r)+r);
    listput(rs,r);listput(targets,v%r^2);
  );
  forprime(h=11,3000,
    if(#hs==w,break);
    if(setsearch(Set(rs),h),next);
    if(#polrootsmod(lehmer(0),h)==5,listput(hs,h));
  );
  if(#rs!=w || #hs!=w,error("could not construct test primes"));
  my(moduli=concat(vector(w,i,rs[i]^2),vector(w,i,hs[i]^2)));
  my(A=prod(j=1,#moduli,moduli[j]), offsets=vector(w));
  for(i=1,w,
    offsets[i]=lift(chinese(vector(2*w,j,Mod(if(j==i,targets[i],0),moduli[j]))));
  );
  my(z=vector(w));
  for(j=1,w,
    my(h=hs[j], roots=polrootsmod(lehmer(0),h));
    my(lifts=vector(5,i,Mod(lift_simple(lehmer(0),lift(roots[i]),h),h^2)));
    my(values=[h,1,1,1,1],poly=0);
    for(i=1,5,
      my(basis=1);
      for(m=1,5,if(m!=i,basis*= (y-lifts[m])/(lifts[i]-lifts[m])));
      poly+=values[i]*basis;
    );
    my(coeff=vector(5,i,lift(chinese(vector(w,v,Mod(if(v==j,lift(polcoef(poly,i-1)),i==1),hs[v]^2))))));
    z[j]=Polrev(coeff,y); z[j]/=content(z[j]);
  );
  my(families=0, markvals=0, local_tests=0, usable=0, irred=0, pwords=0, missed=[]);
  for(tword=0,5,for(i=1,w,
    my(T0=A*tword+offsets[i],f=lehmer(T0),r=rs[i]);
    my(root=lift(Mod(-T0^2,r^2)/5), shifted=subst(f,y,y+root));
    if(valuation(polcoef(shifted,0),r)!=1,error("not Eisenstein at own prime"));
    for(k=0,4,if(polcoef(shifted,k)%r,error("Eisenstein coefficients")));
    for(v=1,w,if(v!=i && poldisc(f)%rs[v]==0,error("ramification overlap")));
    my(uu=Mod(y,f),sig=((T0+2)+T0*uu-uu^2)/(1+(T0+2)*uu));
    if(sig==uu || subst(f,y,sig)!=0,error("Galois generator"));
    families++;
    for(j=1,w,
      my(c=subst(z[j],y,sig)/subst(z[j],y,uu));
      if(norm(c)!=1,error("mark norm"));
      for(v=1,w,
        my(h=hs[v],roots=polrootsmod(f,h));
        my(vals=vector(5,k,valuation(subst(z[j],y,lift_simple(f,lift(roots[k]),h)),h)));
        if(j==v && vecsort(vals)!=[0,0,0,0,1],error("missing exclusive odd valuation"));
        if(j!=v && vecmax(vals)!=0,error("unwanted marked valuation"));
        markvals++;
      );
    );
    forprime(q=307,1800,
      my(roots=polrootsmod(f,q)); if(#roots!=5,next);
      my(hit=0);
      for(j=1,w,
        my(signs=Set(vector(5,h,kronecker(lift(subst(z[j],y,roots[h])),q))));
        if(signs==[-1,1],hit=1;break);
      );
      local_tests++; usable+=hit; if(!hit,missed=[tword,i,q]);
    );
  ));
  forprime(p=101,503,
    if(A%p==0,next);
    for(tword=0,p-1,
      my(inert=sum(i=1,w,polisirreducible(lehmer(Mod(A*tword+offsets[i],p)))));
      pwords++;if(2*inert>=w,irred++);
    );
  );
  print("ramification primes = ",Vec(rs),", mark primes = ",Vec(hs));
  print("quintic specializations = ",families,", exclusive valuations = ",markvals);
  print("all parameter words at test primes = ",pwords,", at least half inert = ",irred);
  print("split field/partner pairs = ",local_tests,", some nonsquare mark = ",usable,", missed [word,field,prime] = ",missed);
}
iferr(replay(),e,print(e);quit(1));
quit;
