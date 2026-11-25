\\ Integer-only genus-two split replays, hidden common factors and residual charges.
read("experiments/genus-two-cantor.gp");

cc_scalar(n) = {
  my(s=1);
  forprime(l=3,13,s*=l^logint(4*n^2,l));
  s;
}

cc_model(d,A,B,C,f,v,t,s) = {
  my(den=1-f*t^2,a=A+2*(f*v*t-A)/den,z=v+t*(a-A));
  my(e=A^2-f*v^2,F=(x^2-e)*(x^3+x^2+B*x+C),u=subst(F,x,a));
  my(units=[den,numerator(z),f,poldisc(F),numerator(u)],bad=0);
  for(i=1,#units,
    my(g=gcd(units[i],d));
    if(g>1 && g<d,return([g,1]));
    if(g==d,bad=1);
  );
  if(bad,return([0,0]));
  my(one=Mod(1,d),u0=u*one,mono=u0^5*subst(F,x,x/u0),hit=0);
  iferr(multiply_divisor([one*x-u0*a,u0^3],s,mono,d),err,
    if(errname(err)!="e_USER",error(err));
    my(payload=component(err,1));
    if(#payload!=2 || payload[1]!="factor ",error(err));
    hit=payload[2];
  );
  [hit,2*(hit>0)];
}

cc_emit(p) = {
  if(setsearch(Set(Vec(ccprimes)),p),return());
  if(!isprime(p),error("uncertified prime"));
  listput(ccprimes,p);
  my(power=p^valuation(ccoriginal,p));
  ccresidual/=power;
  if(denominator(ccresidual)!=1,error("wrong original multiplicity"));
  listput(ccjobs,ccresidual);
}

cc_closure(d,A,B,C,f,s,depth) = {
  if(d==1,return([]));
  if(d!=ccoriginal && ((d>>ccshift)%ccmod)!=ccword,ccstats[5]++);
  my(p,e=isprimepower(d,&p));
  if(e,
    if(e>1,ccstats[4]++);
    cc_emit(p);return([]);
  );
  for(v=1,2,for(t=0,3,
    my(hit=cc_model(d,A,B,C,f,v,t,s),g=hit[1]);
    if(g,
      if(g<=1 || g>=d || d%g,error("invalid split"));
      ccstats[hit[2]]++;
      if(depth>0,ccstats[3]++);
      return(concat(cc_closure(g,A,B,C,f,s,depth+1),cc_closure(d/g,A,B,C,f,s,depth+1)));
    );
  ));
  [d];
}

cc_blind(n,rounds) = {
  ccoriginal=n;ccresidual=n;ccjobs=List([n]);ccprimes=List();ccstats=[0,0,0,0,0];
  my(u=[n],s=cc_scalar(n),b=logint(n,2)+1,wordct=0,fs=[2,3,5,7,11]);
  for(k=2,min(5,b),for(j=0,b,
    my(w=(n>>j)%(2^(3*k)),mask=2^k-1,A=bitand(w,mask),B=bitand(w>>k,mask),C=w>>(2*k));
    ccshift=j;ccmod=2^(3*k);ccword=w;
    for(i=1,#fs,
      my(nxt=List());
      for(l=1,#u,
        my(d=u[l]);
        my(blocks=cc_closure(d,A,B,C,fs[i],s,0));
        for(z=1,#blocks,listput(nxt,blocks[z]));
      );
      u=Vec(nxt);wordct++;
      if(!#u || wordct>=rounds,return([Vec(ccprimes),Vec(ccjobs),ccstats]));
    );
  ));
  [Vec(ccprimes),Vec(ccjobs),ccstats];
}

\\ A deterministic complete background job at the finite replay scales.
cc_trial(d) = {
  my(rest=d,tests=0,ps=List(),p=2);
  while(p^2<=rest,
    tests++;
    if(rest%p==0,
      listput(ps,p);
      while(rest%p==0,rest/=p;tests++);
    );
    p=if(p==2,3,p+2);
  );
  if(rest>1,listput(ps,rest));
  [Set(Vec(ps)),tests+1];
}

cc_inputs() = {
  my(Ks=[5*7*11,5^2*11,7^2*13,11*13*17,13^2*17^2],total=0,stats=[0,0,0,0,0],shared=0,resjobs=0,unfinished=0);
  for(kidx=1,#Ks,
    my(K=Ks[kidx],kps=factor(K)[,1]);
    for(m=11,28,
      my(n=K*m,out=cc_blind(n,6),ps=out[1],jobs=out[2],found=0,d=0);
      stats+=out[3];shared+=(gcd(K,m)>1);
      if(#jobs!=#ps+1 || jobs[1]!=n,error("missing residual job"));
      for(h=1,#jobs,
        my(cert=if(h==1,[],Set(ps[1..h-1])));
        my(job=cc_trial(jobs[h]),allp=Set(concat(cert,job[1])));
        if(prod(i=1,#allp,allp[i]^valuation(n,allp[i]))!=n,error("incomplete residual"));
        if(!found && #setminus(Set(Vec(kps)),cert)==0,
          found=1;d=jobs[h];
          if(m%d,error("residual must divide the partner"));
          resjobs+=(d>1);
        );
      );
      if(!found,unfinished++);
      total++;
    );
  );
  if(!stats[1]||!stats[2]||!stats[3]||!stats[4]||!stats[5]||!resjobs||!shared,error("missing branch coverage ",[stats,resjobs,shared]));
  [total,stats,shared,resjobs,unfinished];
}

cc_interval_counts() = {
  my(checks=0,collisions=0);
  for(K=2,40,for(k=1,2,for(r=1,2,
    my(j=logint(K,2),Q=2^(3*k*r));
    for(ai=1,3,
      my(A=[0,9001,2^89+127][ai],H=169,ct=vector(Q),last=-1);
      for(m=A+1,A+H,
        my(z=(K*m)>>j);
        if(z<=last,error("noninjective word map"));
        last=z;ct[z%Q+1]++;
      );
      if(vecmax(ct)>1+(2*H)\Q,error("joint-word fiber"));
      collisions+=(vecmax(ct)>1);checks++;
    );
  )));
  [checks,collisions];
}

cc_residual_charge() = {
  my(checks=0);
  for(Z=2,100,
    my(cost=vector(2*Z,d,cc_trial(d)[2]));
    my(lhs=sum(m=Z+1,2*Z,vecmax(vector(#divisors(m),j,cost[divisors(m)[j]]))));
    my(over=sum(d=1,2*Z,cost[d]*((2*Z)\d)));
    if(lhs>over || over>2*Z*sum(d=1,2*Z,cost[d]/d),error("residual charge"));
    checks++;
  );
  checks;
}

cc_main() = {
  print("inputs, unit/Cantor splits, repeated splits, prime powers, retained original starts; shared factors, nontrivial post-extraction jobs, cutoff misses = ",cc_inputs());
  print("shifted interval checks, with repeated joint words = ",cc_interval_counts());
  print("exact divisor-charge comparisons = ",cc_residual_charge());
}
iferr(cc_main(),e,print(e);quit(1));
quit;
