\\ Finite affine-Galois counts and actual reductions of two rational elliptic points.

indicators(ell,u,v) = {
  my(one=(u-1)*(ell^2-u)/((ell-1)*(ell^2-ell))*(1-v/ell));
  my(upper=1-(u-ell)*(u-ell^2)/((1-ell)*(1-ell^2)));
  if(one!=(u==ell && v==0) || upper!=(u>1),error("interpolation",[ell,u,v]));
  [one,upper];
}

counts(ell,choice) = {
  my(total=0,lo=0,hi=0,ns=2);
  while(kronecker(ns,ell)!=-1,ns++);
  for(a=0,ell-1,for(b=0,ell-1,for(c=0,ell-1,for(d=0,ell-1,
    if((a*d-b*c)%ell==0,next);
    if(choice==1 && (b || c),next);
    if(choice==2 && (a || d),next);
    if(choice==3 && (a!=d || (b-ns*c)%ell),next);
    if(choice==4 && ((a+d)%ell || (b+ns*c)%ell),next);
    my(image=Map());
    for(s=0,ell-1,for(t=0,ell-1,
      my(key=[((1-a)*s-b*t)%ell,(-c*s+(1-d)*t)%ell]);mapput(image,key,1);
    ));
    my(u=ell^2/matsize(Mat(image))[1]);
    for(s=0,ell-1,for(t=0,ell-1,
      my(v=if(mapisdefined(image,[s,t]),u,0), val=indicators(ell,u,v));
      total++;lo+=val[1];hi+=val[2];
    ));
  ))));
  my(expected=if(choice==0,1/ell-1/(ell^2*(ell-1)),if(choice==1,2*(ell-2)/(ell*(ell-1)),if(choice==3,0,1/ell))));
  if(lo/total!=expected,error("Galois probability",[ell,choice,lo,total,expected]));
  [total,lo,hi];
}

actual_orders(coeffs,point) = {
  my(global=ellinit(coeffs), seen=0,events=0, positive=0, certified=0, largest=0);
  if(ellorder(global,point)!=0,error("expected infinite-order point"));
  forprime(p=1009,20011,
    if(global.disc%p==0,next);
    my(curve=ellinit(coeffs,p),n=ellcard(curve),ord0=ellorder(curve,point,n));
    my(group=ellgroup(curve),is=Set(factor(n)[,1]), rough=0);
    for(j=1,#is,
      my(ell=is[j]);if(ell<=7,next);
      my(u=prod(k=1,#group,if(group[k]%ell==0,ell,1)));
      if(u==ell && valuation(ord0,ell)==valuation(n,ell),
        \\ The ell-Sylow is cyclic and the marked point is nondivisible.
        my(pair=indicators(ell,u,0));
        if(!pair[1] || ord0%ell,error("reduction witness"));
        events++;
      );
      if(ord0%ell==0,rough++);
    );
    if(rough>=2,positive++);
    largest=max(largest,rough); seen++;
    if(rough>=2 && ord0%11==0 && ord0%13==0,certified++);
  );
  [seen,events,positive,largest,certified];
}

replay() = {
  my(rows=0,groupelts=0);
  forprime(ell=3,7,for(choice=0,4,my(ans=counts(ell,choice));rows++;groupelts+=ans[1]));
  print("local Galois laws, affine maps checked = ",[rows,groupelts]);
  print("non-CM local reductions, witnesses, double-rough cases, maximum, multiples of 11*13 = ",actual_orders([0,0,1,-1,0],[0,0]));
  print("CM local reductions, witnesses, double-rough cases, maximum, multiples of 11*13 = ",actual_orders([0,0,0,0,-2],[3,5]));
}
iferr(replay(),e,print(e);quit(1));
quit;
