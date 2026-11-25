\\ Exact local and composite checks for the two-factor genus-two model.
read("experiments/genus-two-cantor.gp");

quad_cubic(a,b,c,u,f) = (x^2+a*x+f*u^2)*(x^3+b*x^2+c*x+f*u^2);

all_models(p) = {
  my(base=Mod(1,p), selected=0, oddmarks=0, evenmarks=0, translations=0);
  for(i=0,p^5-1,
    my(f=(x^5+sum(j=0,4,(i\p^j%p)*x^j))*base);
    if(poldisc(f)==0,next);
    my(weil=hyperellcharpoly(f), n=subst(weil,x,1));
    if(n%4!=2 || polcoef(weil,3)%2==0,next);
    my(fs=factor(f)[,1]);
    if(#fs!=2 || poldegree(fs[1])!=2 || poldegree(fs[2])!=3,error("unexpected branch type",[p,i,fs]));
    selected++;
    for(a=0,p-1,
      my(s2=kronecker(lift(subst(fs[1],x,a)),p), s3=kronecker(lift(subst(fs[2],x,a)),p));
      if(s2!=s3,next);
      my(yp=sqrt(subst(f,x,a)), point=[base*(x-a),yp]);
      my(mult=multiply_divisor(point,n/2,f,p));
      if((mult[1]==1)!=(s2==1),error("quadratic pairing disagrees with Cantor",[p,i,a]));
      if(s2==1,oddmarks++,evenmarks++);
      translations++;
    );
  );
  [selected,oddmarks,evenmarks,translations];
}

scaling_checks(p) = {
  my(dict=Map(), f=Mod(4,p), cnt=0, u,v,w,coef);
  for(a=0,p-1,for(b=0,p-1,for(c=0,p-1,for(ui=1,p-1,for(vi=1,p-1,
    u=Mod(ui,p); v=Mod(vi,p); w=u/v;
    coef=[lift(w^2*a),lift(w^2*b),lift(w^4*c),lift(w^2*u)];
    if(w^2*u!=w^3*v,error("normalization"));
    my(orig=(x^2+a*x+f*u^2)*(x^3+b*x^2+c*x+f*v^2));
    if(w^10*subst(orig,x,x/w^2)!=quad_cubic(coef[1],coef[2],coef[3],coef[4],f),error("rescaled curve"));
    if(mapisdefined(dict,coef,&cnt),mapput(dict,coef,cnt+1),mapput(dict,coef,1));
  )))));
  my(lookup=Mat(dict));
  if(matsize(lookup)[1]!=p^3*(p-1),error("missing normalized chart"));
  for(i=1,matsize(lookup)[1],if(lookup[i,2]!=p-1,error("wrong orbit size")));
  matsize(lookup)[1];
}

factor_from_cantor(poly,point,ms,n) = {
  my(found=0);
  iferr(multiply_divisor([x*Mod(1,n),Mod(point,n)],ms,poly*Mod(1,n),n),e,
    if(errname(e)!="e_USER",error(e));
    my(payload=component(e,1));
    if(#payload!=2 || payload[1]!="factor ",error(e));
    found=payload[2];
  );
  found;
}

crt_checks() = {
  my(witnesses=0, smooth=0, qtypes=Map());
  for(idx=1,70,
    my(f=[2,3,5,6,7,10,14][1+(idx%7)],u=1+(idx\4%5),a=idx%5-2,b=idx\3%7-3,c=idx\7%5-2);
    my(poly=quad_cubic(a,b,c,u,f), y0=f*u^2, delta=poldisc(poly)*y0);
    if(!delta,next);
    forprime(p=5,43,
      if(delta%p==0 || kronecker(f,p)!=1,next);
      my(fp=poly*Mod(1,p),hp=hyperellcharpoly(fp),n=subst(hp,x,1));
      if(n%4!=2 || polcoef(hp,3)%2==0 || vecmax(factor(n)[,1])>19,next);
      if(multiply_divisor([x*Mod(1,p),Mod(y0,p)],n/2,fp,p)[1]!=1,error("positive Tate sign"));
      smooth++;
      forprime(q=13,109,
        if(delta%q==0 || kronecker(f,q)!=-1,next);
        my(fq=poly*Mod(1,q),qn=subst(hyperellcharpoly(fq),x,1),qm=qn/2^valuation(qn,2));
        if(multiply_divisor([x*Mod(1,q),Mod(y0,q)],qm,fq,q)[1]==1,error("negative Tate sign"));
        my(localfac=factor(fq),shape=vecsort(vector(matsize(localfac)[1],j,poldegree(localfac[j,1]))));
        mapput(qtypes,shape,1);
        my(gg=factor_from_cantor(poly,y0,n/2,p*q));
        if(gg!=p && gg!=q,error("mixed CRT",[p,q,gg]));
        witnesses++;
      );
    );
  );
  [smooth,witnesses,matsize(Mat(qtypes))[1]];
}

blind(n) = {
  my(ms=1, bits=logint(n,2)+1, fs=[2,3,5,6,7,10,14,15,21,22,26]);
  forprime(r=3,13,ms*=r^logint(4*n^2,r));
  for(stage=1,2,
    my(gen=ffgen(2^stage,'w), vals=vector(2^stage,j,gen^0*subst(Pol(digits(j-1,2),y),y,gen)));
    for(k=2,min(bits,8),for(bit=0,bits,
      my(seed=(n>>bit)%(2^(4*k)));
      for(i=1,#vals,for(j=1,#vals,
        my(shift=sum(h=0,4*k-1,2^h*lift(trace(vals[j]*vals[i]^h))),word=bitxor(seed,shift));
        my(cs=vector(4,h,(word>>(k*(h-1)))%(2^k)));
        for(fi=1,#fs,
          my(f=fs[fi],y0=f*cs[4]^2,poly=quad_cubic(cs[1],cs[2],cs[3],cs[4],f));
          my(gg=gcd(n,y0*poldisc(poly)));
          if(gg>1 && gg<n,return([gg,0]));
          if(gg==n,next);
          gg=factor_from_cantor(poly,y0,ms,n);
          if(gg>1 && gg<n,return([gg,1]));
        );
      ));
    ));
  );
  [0,0];
}

replay() = {
  forprime(p=3,7,print("p=",p,", selected monic quintics, odd/even marks, total = ",all_models(p)));
  forprime(p=3,7,print("p=",p,", normalized chart orbits = ",scaling_checks(p)));
  print("smooth p witnesses, composite gcd discrepancies, q factor patterns = ",crt_checks());
  my(samples=[143,221,323,391,437,493,529,589,667,713,899,1147,1729,2431,3927],found=0,via=0);
  for(i=1,#samples,my(hit=blind(samples[i]));if(hit[1]<=1 || samples[i]%hit[1],error("blind split",samples[i]));found++;via+=hit[2]);
  print("blind integer splits, including Cantor gcd splits = ",[found,via]);
}
iferr(replay(),e,print(e);quit(1));
quit;
