\\ Check the normalized chart, conic pencil, and two local orders independently.
read("experiments/genus-two-cantor.gp");

conic_mark(A,v,f,t) = {
  my(a=A+2*(f*v*t-A)/(1-f*t^2));
  [a,v+t*(a-A)];
}

signed(value,p) = kronecker(lift(value),p);

correlations(p,H) = {
  my(one=Mod(1,p),f=4*one,total=0,missing=0,marks=0);
  for(ei=0,p-1,
    my(e=one*ei, vals=vector(H,j,signed(e+f*j^2,p)), s=vecsum(vals));
    total+=s^2;
    if(vecmax(vals)<=0,missing++;next);
    if(signed(e,p)!=-1,next);
    my(v=select(j->vals[j]==1,[1..H])[1],A=sqrt(e+f*v^2), xs=List());
    for(t=0,min(p-1,4*H+10),
      if(1-f*t^2==0,next);
      my(az=conic_mark(A,v,f,t));
      if(az[1]^2-f*az[2]^2!=e || az[2]==0,error("conic mark"));
      listput(xs,lift(az[1]));
    );
    my(as=Set(Vec(xs)));
    if(#as*2<#xs,error("conic fiber"));
    for(B=0,p-1,
      my(ds=Set(vector(#as,i,lift(one*(as[i]^3+as[i]^2+B*as[i])))));
      if(3*#ds<#as,error("cubic fiber"));
      my(both=0,S2=0);
      for(C=0,p-1,
        my(ss=vector(#ds,i,signed(one*(ds[i]+C),p)));
        S2+=vecsum(ss)^2;
        if(vecmin(ss)==-1 && vecmax(ss)==1,both++);
      );
      if(S2!=#ds*(p-#ds),error("twist correlation"));
      if((p-both)*(#ds-1)^2>S2,error("twist miss bound"));
      marks+=#as;
    );
  );
  if(total!=H*(p-H) || missing*(H-1)^2>total,error("base correlation"));
  marks;
}

charts(p) = {
  my(one=Mod(1,p),nr=znprimroot(p),good=0,negative=0,affine=0);
  for(e=1,p-1,if(signed(e,p)!=-1,next);
    for(B=0,p-1,for(C=0,p-1,
      my(g=(x^3+x^2+B*x+C)*one);
      if(!polisirreducible(g),next);
      my(F=(x^2-e)*g);
      for(signbit=0,1,
        my(d=if(signbit,nr,one), twist=d^5*subst(F,x,x/d));
        my(W=hyperellcharpoly(twist),n=subst(W,x,1));
        if(n%4!=2 || polcoef(W,3)%2==0,next);
        good++; negative+=signbit;
        for(h=0,1,
          my(raw=d^5*subst(F,x,(x+h)/d), centered=subst(raw,x,d*x-h)/d^5);
          if(centered!=F || hyperellcharpoly(raw)!=W,error("normalized twist"));
          affine++;
        );
      );
    ));
  );
  [good,negative,affine];
}

composite_gcd(F,a,d,s,n) = {
  my(one=Mod(1,n),a0=a*one,d0=d*one, mono=d0^5*subst(F,x,x/d0));
  my(hit=0);
  iferr(multiply_divisor([one*x-d0*a0,d0^3],s,mono,n),err,
    if(errname(err)!="e_USER",error(err));
    my(payload=component(err,1));
    if(#payload!=2 || payload[1]!="factor ",error(err));
    hit=payload[2];
  );
  hit;
}

blind(n) = {
  my(s=1,b=logint(n,2)+1,fs=[2,3,5,7,11,13]);
  forprime(l=3,13,s*=l^logint(4*n^2,l));
  for(k=2,min(7,b),for(j=0,b,
    my(word=(n>>j)%(2^(3*k)),mask=2^k-1);
    my(A=bitand(word,mask),B=bitand(word>>k,mask),C=word>>(2*k));
    for(i=1,#fs,for(v=1,3,for(t=0,4,
      my(f=fs[i],e=A^2-f*v^2,az=conic_mark(A,v,f,t),a=az[1],z=az[2]);
      my(F=(x^2-e)*(x^3+x^2+B*x+C),d=subst(F,x,a));
      my(units=[1-f*t^2,numerator(z),f,poldisc(F),numerator(d)],bad=0);
      for(l=1,#units,
        my(g=gcd(n,units[l]));
        if(g>1 && g<n,return([g,0]));
        if(g==n,bad=1);
      );
      if(bad,next);
      my(g=composite_gcd(F,a,d,s,n));
      if(g,return([g,1]));
    )));
  ));
  [0,0];
}

crt_check() = {
  my(cnt=0,np=0,nt=0,primes=Map(),partners=Map());
  for(i=1,115,
    my(f=[2,3,5,7][1+i%4],A=i%7-3,v=1+i\7%3,B=i\3%7-3,C=i\5%11-5,t=i\13%4);
    my(e=A^2-f*v^2,az=conic_mark(A,v,f,t),a=az[1],z=az[2]);
    if(a^2-f*z^2!=e,error("rational conic"));
    my(F=(x^2-e)*(x^3+x^2+B*x+C),d=subst(F,x,a));
    if(!d || !z || !poldisc(F),next);
    my(bad=poldisc(F)*numerator(d)*denominator(d)*numerator(z)*denominator(z)*denominator(a));
    forprime(p=5,59,
      if(bad%p==0 || signed(f,p)!=1 || signed(e,p)!=-1,next);
      my(one=Mod(1,p),u=one*d,monic=u^5*subst(F,x,x/u));
      my(W=hyperellcharpoly(monic),n=subst(W,x,1));
      if(n%4!=2 || polcoef(W,3)%2==0 || vecmax(factor(n/2)[,1])>19,next);
      if(multiply_divisor([one*x-u*a,u^3],n/2,monic,p)[1]!=1,error("odd mark"));
      np++;nt+=(signed(u,p)==-1);mapput(primes,p,1);
      forprime(q=11,83,
        if(bad%q==0 || signed(f,q)!=-1,next);
        my(un=Mod(d,q),mono=un^5*subst(F,x,x/un),qn=subst(hyperellcharpoly(mono),x,1));
        if(multiply_divisor([Mod(x,q)-un*a,un^3],qn/2^valuation(qn,2),mono,q)[1]==1,error("even mark"));
        my(found=composite_gcd(F,a,d,n/2,p*q));
        if(found!=p && found!=q,error("CRT discrepancy"));
        cnt++;mapput(partners,q,1);
      );
    );
  );
  if(!nt || np==nt || !cnt,error("insufficient sign coverage"));
  [np,nt,cnt,#primes,#partners];
}

replay() = {
  forprime(p=5,11,print("p=",p,", good normalized twists, negative, affine checks = ",charts(p)));
  forprime(p=17,31,print("p=",p,", marks in checked fibers = ",correlations(p,3)));
  print("positive local pairings, negative twists, CRT splits, distinct p and q = ",crt_check());
  my(samples=[143,221,323,391,437,493,529,589,667,713,899,1147,1729,2431,3927],cantor=0);
  for(i=1,#samples,
    my(hit=blind(samples[i]));
    if(hit[1]<=1 || hit[1]>=samples[i] || samples[i]%hit[1],error("integer-only split",samples[i]));
    cantor+=hit[2];
  );
  print("integer-only splits, including Cantor splits = ",[#samples,cantor]);
}
iferr(replay(),e,print(e);quit(1));
quit;
