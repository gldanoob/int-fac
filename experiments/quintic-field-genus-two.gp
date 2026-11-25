\\ Norm quintics, ordinary order, and parity of one marked genus-two divisor.
\\ Run with gp -q experiments/quintic-field-genus-two.gp.

field_poly = y^5+y^4-4*y^3-3*y^2+3*y+1;
period5 = Mod(y, field_poly);
mark = (5-period5^2)/(3-period5);

unit_or_factor(value,n) = {
  my(g = gcd(lift(value),n));
  if(g>1 && g<n, error("factor ",g));
  g==1;
}

check_degree(f,n) = {
  if(f != 0 && !unit_or_factor(pollead(f),n), error("invalid leading coefficient"));
  poldegree(f);
}

q_and_r(f,g,n) = {
  check_degree(g,n);
  my(number = divrem(f,g));
  check_degree(number[2],n);
  number;
}

unit_monic(f,n) = {
  check_degree(f,n);
  f / pollead(f);
}

exact_quo(f,g,n) = {
  my(qr = q_and_r(f,g,n));
  if(qr[2] != 0, error("inexact Cantor polynomial division"));
  qr[1];
}

poly_bezout(f,g,n) = {
  my(a=1,b=0,c=0,d=1,qr);
  while(g != 0,
    qr=q_and_r(f,g,n);
    [f,g]=[g,qr[2]];
    [a,c]=[c,a-qr[1]*c]; [b,d]=[d,b-qr[1]*d];
  );
  check_degree(f,n);
  my(lc=pollead(f));
  [f/lc,a/lc,b/lc];
}

cantor(left,right,f,n) = {
  my(u=left[1],v=left[2],w=right[1],t=right[2]);
  if(u==1, return(right));
  if(w==1, return(left));
  my(first=poly_bezout(u,w,n), second=poly_bezout(first[1],v+t,n), d=second[1]);
  my(newu=exact_quo(u*w,d^2,n));
  my(top=second[2]*(first[2]*u*t+first[3]*w*v)+second[3]*(v*t+f));
  my(newv=q_and_r(exact_quo(top,d,n),newu,n)[2]);
  while(check_degree(newu,n)>2,
    newu=unit_monic(exact_quo(f-newv^2,newu,n),n);
    newv=q_and_r(-newv,newu,n)[2];
  );
  [newu,newv];
}

multiply_divisor(point,m,f,n) = {
  my(r=[Mod(1,n),Mod(0,n)],bits=binary(m));
  for(i=1,#bits,r=cantor(r,r,f,n); if(bits[i],r=cantor(r,point,f,n)));
  r;
}

test_fibres(p) = {
  my(t=ffgen(field_poly*Mod(1,p),'w), c=(5-t^2)/(3-t));
  my(counts=Map(), beta,poly,order,good=0,chart=0);
  for(num=1,p^5-1,
    beta=subst(Pol(digits(num,p),y),y,t);
    poly=charpoly(-c*beta^2,x);
    if(!polisirreducible(poly),next);
    if(kronecker(lift(polcoef(poly,0)),p)!=1,error("norm nonsquare"));
    if(mapisdefined(counts,poly,&order),mapput(counts,poly,order+1),mapput(counts,poly,1));
    if(num%p==1,chart++);
  );
  my(table=Mat(counts));
  for(i=1,matsize(table)[1],
    if(table[i,2]!=10,error("quintic norm fibre ",p," ",table[i,2]));
    order=subst(hyperellcharpoly(table[i,1]),x,1);
    if(order%2==0,error("irreducible branch polynomial with even Jacobian"));
    if(vecmax(factor(order)[,1])<=13,good++);
  );
  if(matsize(table)[1]!=(p^5-p)/10,error("missing irreducible polynomials"));
  [matsize(table)[1],good,chart];
}

q_accepts(q) = {
  my(roots=polrootsmod(field_poly,q));
  if(#roots!=5 || q==199,return(0));
  for(i=1,#roots, if(kronecker(lift((5-roots[i]^2)/(3-roots[i])),q)==-1,return(1)));
  0;
}

local_and_composite() = {
  my(cases=0,smooth=0,evenorders=0,fn,bnorm,pointp,pointq,pointn,n,ms);
  for(idx=1,32,
    my(beta=1+(idx%5-2)*period5+(idx\5-2)*period5^2+(idx%3)*period5^3+period5^4);
    fn=polresultant(field_poly,x+lift(mark*beta^2),y);
    bnorm=norm(beta);
    if(poldisc(fn)==0 || bnorm==0,next);
    forprime(p=3,31,
      if(!polisirreducible(field_poly*Mod(1,p)) || numerator(poldisc(fn)*bnorm)%p==0,next);
      my(fp=fn*Mod(1,p),gporder=subst(hyperellcharpoly(fp),x,1));
      if(gporder%2==0,error("inert odd Jacobian"));
      pointp=[x*Mod(1,p),Mod(bnorm,p)];
      if(multiply_divisor(pointp,gporder,fp,p)[1]!=1,error("local p order bound"));
      if(vecmax(factor(gporder)[,1])>19,next);
      smooth++;
      forprime(q=13,200,
        if(!q_accepts(q) || numerator(poldisc(fn)*bnorm)%q==0,next);
        my(fq=fn*Mod(1,q),gqorder=subst(hyperellcharpoly(fq),x,1));
        pointq=[x*Mod(1,q),Mod(bnorm,q)];
        my(odd=gqorder/2^valuation(gqorder,2));
        if(multiply_divisor(pointq,odd,fq,q)[1]==1,error("local q order is odd"));
        if(multiply_divisor(pointq,gqorder,fq,q)[1]!=1,error("local q order bound"));
        evenorders++;
        n=p*q; pointn=[x*Mod(1,n),Mod(bnorm,n)];
        my(found=0);
        iferr(multiply_divisor(pointn,gporder,fn*Mod(1,n),n),e,
          if(errname(e)!="e_USER", error(e));
          my(payload=component(e,1));
          if(#payload!=2 || payload[1]!="factor " || (payload[2]!=p && payload[2]!=q), error(e));
          found=payload[2];
        );
        if(!found,error("composite did not expose mixed Mumford identity"));
        cases++;
      );
    );
  );
  [smooth,evenorders,cases];
}

adjustable_fields() = {
  my(tested=0,maxell=0,maxshift=0);
  forprime(p=13,43,forprime(q=47,101,
    my(hit=0);
    forprime(ell=11,20000,
      if(ell%5!=1 || ell==p || ell==q,next);
      if(Mod(p,ell)^((ell-1)/5)==1 || Mod(q,ell)^((ell-1)/5)!=1,next);
      my(G=polsubcyclo(ell,5,y));
      if(!polisirreducible(G*Mod(1,p)),next);
      my(roots=polrootsmod(G,q)); if(#roots!=5,next);
      for(s=0,40,
        if(subst(G,y,-s)%p==0,next);
        my(signs=Set(vector(5,i,kronecker(lift(s+roots[i]),q))));
        if(signs==[-1,1],hit=1; maxell=max(maxell,ell); maxshift=max(maxshift,s);break(2));
      );
    );
    if(!hit,error("unfilled finite field menu ",[p,q]));
    tested++;
  ));
  [tested,maxell,maxshift];
}

public_split(nn) = {
  my(ms=1, bits=logint(nn,2)+1);
  forprime(r=3,13,ms*=r^logint(4*nn^2,r));
  for(stage=1,2,
    my(gen=ffgen(2^stage,'w));
    my(wvals=vector(2^stage,j,gen^0*subst(Pol(digits(j-1,2),y),y,gen)));
    for(k=2,min(bits,8),for(j=0,bits,
      my(seed=(nn>>j)%(2^(4*k)));
      for(i=1,#wvals,for(v=1,#wvals,
        my(shift=sum(h=0,4*k-1,2^h*lift(trace(wvals[v]*wvals[i]^h))));
        my(block=bitxor(seed,shift), coords=vector(4,h,(block>>(k*(h-1)))%(2^k)));
        for(chart=1,5,
          my(allcoords=concat(concat(coords[1..chart-1],[1]),coords[chart..4]));
          my(beta=subst(Polrev(allcoords,y),y,period5), bnorm=norm(beta));
          my(fn=polresultant(field_poly,x+lift(mark*beta^2),y));
          my(bad=gcd(numerator(poldisc(fn)*bnorm),nn));
          if(bad>1 && bad<nn,return(bad));
          if(bad==nn,next);
          my(found=0);
          iferr(multiply_divisor([x*Mod(1,nn),Mod(bnorm,nn)],ms,fn*Mod(1,nn),nn),e,
            if(errname(e)!="e_USER",error(e));
            my(payload=component(e,1));
            if(#payload!=2 || payload[1]!="factor ",error(e));
            found=payload[2]
          );
          if(found,return(found));
        );
      ));
    ));
  );
  0;
}

main() = {
  print("norm fibres, smooth orders, normalized parameters at p=3 and 5: ",test_fibres(3)," ",test_fibres(5));
  print("smooth marked cases, forced even partners, mixed Cantor gcd checks: ",local_and_composite());
  print("adjustable ordered field/mark pairs, maximum conductor, maximum shift: ",adjustable_fields());
  my(samples=[69,115,215,469,629,869,1349,2047,2809],count=0);
  for(i=1,#samples,
    my(n=samples[i],g=public_split(n));
    if(g<=1 || g>=n || n%g,error("blind norm-curve search ",[n,g]));
    count++;
  );
  print("integer-only norm-curve splits: ",count);
}
iferr(main(),e,print(e);quit(1));
quit;
