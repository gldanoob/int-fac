\\ Exact rank witness for binary digit splits of n -> sigma_j(n) modulo q.
\\ The prime search constructs test inputs; sigma is used as a reference value.
coefficientCut(p, q, j) = {
  if(!isprime(p) || !isprime(q) || q <= 2 || p == 2 || p%q != q-1 || j < 1 || j%2 == 0,
    error("expected an odd exponent and odd primes p = -1 (mod q)"));
  my(lows = vector(p,i,1+2*q*p*(i-1)), Q = 2^logint(lows[p],2) * 2);
  my(highs = vector(p));
  for(v = 1,p,
    my(c = chinese(Mod(lows[v],Q) / p^2, Mod(1,q*p)), ell = lift(c));
    while(!isprime(ell), ell += c.mod);
    highs[v] = (p^2*ell-lows[v])/Q
  );
  my(A = matrix(p,p,u,v,Mod(sigma(Q*highs[v]+lows[u],j),q)));
  if(A != 2*matid(p) || matrank(A) != p, error("cut witness failed"));
  [p, Q, logint(Q*vecmax(highs)+lows[p],2)+1, matrank(A)]
};


\\ Test the three menus on a small semiprime set. The probing code sees only n.
progressionProbe(n, mode) = {
  my(exponents = Map());
  for(u=0,1, for(w=-1,1,
    if((mode == 0 && w != 0) || (mode == 1 && u*w != 0), next());
    for(i=0,2, for(d=-2,2,
      my(e = 420*abs(u*(n-1)+w*sqrtint(2^i*n)+d));
      if(e, mapput(exponents,e,1))
    ))
  ));
  my(es = Mat(exponents)[,1], indirect = 0);
  for(a=2,7, for(i=1,#es,
    my(e = es[i], g = gcd(lift(Mod(a,n)^e)-1,n));
    if(g>1 && g<n, return([1,1]));
    if(g==n && !indirect,
      forprime(l=2,7,
        my(k=e);
        while(k%l==0, k /= l; my(v=gcd(lift(Mod(a,n)^k)-1,n)); if(v>1 && v<n, indirect=1; break()))
      )
    )
  ));
  [0,indirect]
};

checkProgressions() = {
  my(counts = matrix(3,2), inputs=0);
  forprime(p=1000,1099,forprime(q=1500,1599,
    inputs++;
    for(mode=0,2,
      my(row = progressionProbe(p*q,mode));
      for(i=1,2, counts[mode+1,i] += row[i])
    )
  ));
  if(inputs != 192 || counts != [64,66;105,106;139,140], error("progression sweep failed"));
  counts
};


\\ Check the forward products/partial inverse against the exact coefficient
\\ formula, and check all half-row Vandermonde determinants are units.
checkTransforms() = {
  my(counts=List());
  for(s=0,2,
    my(A=2^(s+1), h=A/2, L=A*h, B=2^L, M=B^4+1, om=Mod(16,M), eta=om^A);
    my(f=vector(L/2,i,B-i), g=vector(L/2,i,2*i-1));
    my(C=vector(L,i,sum(j=1,#f,if(i+1-j>=1 && i+1-j<=#g,f[j]*g[i+1-j],0))));
    my(values=vector(A^2,i,subst(Polrev(f)*Polrev(g),x,om^(i-1))));
    for(k=0,A-1, for(j=0,A-1,
      my(left=om^(-k*j)*sum(l=0,A-1,values[k+A*l+1]*om^(-A*l*j)));
      my(right=A*sum(t=0,h-1,C[j+A*t+1]*eta^(k*t)));
      if(left!=right,error("partial inverse"))
    ));
    my(tests=0);
    for(mask=0,2^A-1, if(hammingweight(mask)!=h,next());
      my(points=select(i->bittest(mask,i),vector(A,j,j-1)));
      my(V=matrix(h,h,i,j,eta^(points[i]*(j-1))));
      if(gcd(lift(matdet(V)),M)!=1,error("nonunit determinant")); tests++
    );
    listput(counts,tests)
  );
  Vec(counts)
};


\\ Exact prime-field orders for independently scoring the composite-modulus tests.
cmOrders(p) = {
  my(v = List());
  for(f=1,2,for(s=2,5,
    my(x=if(f==1,s,s-1), d=if(f==1,x^3-x,x^3+1));
    my(a=if(f==1,-d^2,0), c=if(f==1,0,d^3));
    my(curve=ellinit([a,c],p));
    listput(v,ellorder(curve,[d*x,d^2]))
  ));
  Vec(v)
};

maxPrimePower(n) = {
  if(n==1,return(1)); my(F=factor(n)); vecmax(vector(matsize(F)[1],i,F[i,1]^F[i,2]))
};

cmSweep(primes, restrict4=0) = {
  my(orders=vector(#primes,i,cmOrders(primes[i])), hits=vector(5));
  for(i=1,#primes,for(j=i+1,#primes,
    if(restrict4 && primes[i]*primes[j]%4!=3,next());
    hits[1]++;
    my(row=vector(4));
    for(t=1,8,
      my(a=orders[i][t],c=orders[j][t],u=maxPrimePower(a),v=maxPrimePower(c));
      if(u!=v,row[1]=1);
      for(h=2,4, if(a!=c && min(u,v)<=2^(h+2),row[h]=1))
    );
    for(h=1,4,hits[h+1]+=row[h])
  ));
  hits
};

checkTwists() = {
  my(small=primes([101,211]), inert=select(p->p%444==443,primes([1000,20000])));
  my(rows=[cmSweep(small,1),cmSweep(small),cmSweep(inert)]);
  if(rows!=[[120,120,120,120,120],[231,231,231,231,231],[78,63,12,33,78]],error("twist sweep"));
  rows
};


\\ Kummer-line scalar multiplication on d*y^2=x^3+a*x^2+c*x.
\\ z and x are units for the initial point on the two good twists below.
xMultiple(m, x, z, a, c) = {
  my(R=[1,0], S=[x,z], bits=binary(m));
  for(i=1,#bits,
    my(T=[(R[1]*S[1]-c*R[2]*S[2])^2*z,(R[1]*S[2]-S[1]*R[2])^2*x]);
    my(bit=bits[i], V=if(bit,S,R), X=V[1], Z=V[2]);
    my(D=[(X^2-c*Z^2)^2,4*X*Z*(X^2+a*X*Z+c*Z^2)]);
    if(bit,R=T;S=D,R=D;S=T)
  );
  R
};

twistProbe(n,B,starts) = {
  my(M=1, es=List());
  forprime(l=2,B,M*=l^logint(B,l));
  listput(es,M);
  forprime(l=2,B,for(j=1,logint(B,l),listput(es,M/l^j)));
  my(tagged=0);
  for(f=1,2,for(i=1,#starts,
    my(s=starts[i],a=if(f==1,0,-3),c=if(f==1,-1,3),d=s*(s^2+a*s+c));
    my(bad=gcd(6*d,n));
    if(bad>1,if(bad<n,return([bad,bad]),next()));
    my(roots=if(f==1,[0,1,-1],[0]));
    for(j=1,#es,
      my(P=xMultiple(es[j],Mod(s,n),Mod(1,n),a,c), e=gcd(lift(P[2]),n));
      if(e>1 && e<n,return([e,e]));
      if(!tagged,
        for(t=1,#roots,
          e=gcd(lift(P[1]-roots[t]*P[2]),n);
          if(e>1 && e<n,tagged=e;break())
        )
      )
    )
  ));
  [1,if(tagged,tagged,1)]
};

checkAdaptiveTwists() = {
  my(ps=select(p->p%444==443,primes([1000,20000])), counts=matrix(3,6));
  for(i=1,#ps,for(j=i+1,#ps,
    my(n=ps[i]*ps[j],s=sqrtint(n));
    for(h=1,3,
      my(B=2^(h+3), fixed=twistProbe(n,B,[2,3,4,5]), adaptive=twistProbe(n,B,vector(4,t,s+t-1)));
      for(k=1,2,
        if(n%fixed[k] || n%adaptive[k] || fixed[k]>=n || adaptive[k]>=n,error("invalid factor"));
        counts[h,k] += fixed[k]>1;
        counts[h,k+2] += adaptive[k]>1;
        counts[h,k+4] += (fixed[k]>1 || adaptive[k]>1)
      )
    )
  ));
  if(counts!=[12,12,16,16,25,25;33,33,24,25,47,48;78,78,78,78,78,78],error("adaptive sweep"));
  counts
};

checkEqualOrders() = {
  my(n=10403, primes=[101,103]);
  for(i=1,2,
    if(ellorder(ellinit([-36,0],primes[i]),[12,36])!=52,error("point order"))
  );
  my(P=lift(xMultiple(26,Mod(2,n),Mod(1,n),0,-1)));
  my(g=[gcd(P[2],n),gcd(P[1],n),gcd(P[1]+P[2],n)]);
  if(g!=[1,101,103],error("torsion split"));
  [P,g]
};

\\ Monic product and remainder trees work over Z/nZ, including at zero divisors.
productTree(values, lo, hi) = {
  if(lo==hi,return(['T-values[lo]]));
  my(mid=(lo+hi)\2, left=productTree(values,lo,mid), right=productTree(values,mid+1,hi));
  [left[1]*right[1],left,right]
};

treeValues(poly,node,~values) = {
  my(rem=poly%node[1]);
  if(#node==1,listput(values,polcoef(rem,0));return());
  treeValues(rem,node[2],~values);
  treeValues(rem,node[3],~values)
};

\\ Return [proper divisor,0], [1,global exponent for a], or [1,0].
orderRectangle(n,a,A,U,H) = {
  if(n<=2 || gcd(a,n)!=1 || A<1 || U<1 || H<0 || H>=n-1,error("invalid rectangle"));
  my(s=n-1, x=Mod(a,n)^A, base=s-H, short=2*H+1, long=U, stride=s, step=1);
  if(long<short, long=short; short=U; stride=1; step=s);
  my(width=sqrtint(long\short), blocks=long\width, tail=long%width, witness=0);
  for(part=1,2,
    my(rows=if(part==1,blocks,1), cols=if(part==1,width,tail));
    if(cols==0,next());
    my(start=base+if(part==1,0,blocks*width*stride), roots=Map());
    my(dr=x^(-stride), dj=x^(-step), zr=Mod(1,n));
    for(r=0,cols-1,
      my(z=zr);
      for(j=0,short-1,mapput(roots,lift(z),r*stride+j*step); z*=dj);
      zr*=dr
    );
    my(rootKeys=Mat(roots)[,1], zs=vector(#rootKeys,i,Mod(rootKeys[i],n)));
    my(poly=productTree(zs,1,#zs)[1], ys=vector(rows), y=x^start, dy=x^(width*stride));
    for(i=1,rows,ys[i]=y;y*=dy);
    my(tree=productTree(ys,1,rows), vals=List(), slopes=List());
    treeValues(poly,tree,~vals); treeValues(deriv(poly,'T),tree,~slopes);
    for(i=1,rows,
      my(off, g);
      if(mapisdefined(roots,lift(ys[i]),&off),
        witness=A*(start+(i-1)*width*stride+off);
        g=gcd(lift(slopes[i]),n),
        g=gcd(lift(vals[i]),n)
      );
      if(g==n,
        for(j=1,#zs,if(zs[j]!=ys[i],my(h=gcd(lift(ys[i]-zs[j]),n));if(h>1,return([h,0]))));
        error("unresolved product gcd")
      );
      if(g>1,return([g,0]))
    )
  );
  [1,witness]
};

checkRectangles() = {
  my(tested=0);
  for(n=4,50,if(isprime(n),next());
    for(a=2,min(7,n-1),if(gcd(a,n)>1,next());
      for(A=1,2,for(U=1,5,for(H=0,min(3,n-2),
        my(result=orderRectangle(n,a,A,U,H), proper=0, exps=List(), base=Mod(a,n)^A);
        for(u=1,U,for(d=-H,H,
          my(e=u*(n-1)+d,g=gcd(lift(base^e)-1,n));
          if(g==n,listput(exps,A*e),if(g>1,proper=1))
        ));
        if(proper,
          if(result[1]<=1 || result[1]>=n || n%result[1],error("missed proper gcd")),
          if(result[1]!=1 || if(#exps,!setsearch(Set(Vec(exps)),result[2]),result[2]!=0),error("global witness"))
        );
        tested++
      )))
    )
  );
  tested
};

\\ Look for an odd annihilator K*(a+2*j) with 0 <= j < W, without a class order.
oddWindow(h,K,a,W) = {
  if(K<1 || K%2!=1 || a<1 || a%2!=1 || W<1,error("invalid odd window"));
  my(x=h^K,s=sqrtint(W-1)+1, baby=Map(), z=x^0, step=x^-2);
  for(r=0,s-1,
    if(!mapisdefined(baby,Vec(z)),mapput(baby,Vec(z),r));
    z*=step
  );
  my(giant=x^a, jump=x^(2*s), r);
  for(i=0,(W-1)\s,
    if(mapisdefined(baby,Vec(giant),&r) && i*s+r<W,
      return(K*(a+2*(i*s+r)))
    );
    giant*=jump
  );
  0
};

checkDeepRoot() = {
  my(N=14111, D=-4*N, L=logint(-D,2)+1, g=qfbred(qfbprimeform(D,3)));
  my(h=g^(2^L), M=oddWindow(h,1,87,6));
  if(M!=95 || oddWindow(h,1,89,3)!=0,error("incorrect shifted search"));
  my(c=lift(1/Mod(2^(2*L),M)), z=h^c, w=g*(z^(2^L))^-1, t=w^4);
  if(z^(2^(2*L))!=h || (g^M)^4!=t || t^2!=g^0 || t==g^0,error("root projection"));
  my(v=Vec(t));
  if(v!=[103,0,137] || v[1]*v[3]!=N,error("factor witness"));
  [M,c,Vec(z),Vec(w),v]
};



checkFaithfulCut() = {
  my(p=13,q=7,W=210,Q=32768,low=vector(p,i,1+W*p*(i-1)), high=vector(p));
  my(w=ffgen(ffinit(2,2,'t),'w), eta=vector(6,i,w^znlog(Mod(i,7),Mod(3,7),6)));
  for(j=1,p,
    my(c=chinese([Mod(low[j],Q)/p^2, Mod(3,q), Mod(1,p)]), ell=lift(c));
    while(!isprime(ell),ell+=c.mod);
    high[j]=(p^2*ell-low[j])/Q
  );
  my(raw=matrix(p,p), normalized=matrix(p,p), largest=0);
  for(i=1,p,for(j=1,p,
    my(n=Q*high[j]+low[i],v=0*w);
    if(n<1 || gcd(n,W)!=1,error("roughness promise"));
    fordiv(n,d,v+=eta[d%q]);
    raw[i,j]=v; normalized[i,j]=eta[n%q]^-2*v;
    largest=max(largest,n)
  ));
  if(raw!=(1+w)*matid(p) || normalized!=matid(p),error("field coefficient"));
  [Q,largest,matrank(normalized)]
};



\\ 0->1 event positions derived from the pinned upstream orbit, in traversal order.
\\ Verify the exact Fourier ranks via integral energies at each character order.
eventGap(e,h,t) = {
  my(v=vecsort(vector(#e,i,(t*e[i])%h)));
  vecmax(vector(#v,j,if(j==#v,h+v[1],v[j+1])-v[j]))
};

archivedEvents() = {
  [[673,1354,2620,3298,19968,20646,21915,22589,23264,23945,
    25890,42561,43234,43915,45858,46536,63210,63888,65153,65827,
    66503,67183,69128,85803,86476,87157,88423,89096,89775,90455,
    108395,109069,109744,110425,111693,112366,113047,129718,131661,132334,
    133013,133693,134962,135638,152310,152986,154931,155604,156285,172960,
    174903,175576,176255,176935,178200,178876,195552,196228,197496,198169,
    198842],
    [3830,4005,7839,8017,11847,12028,15856,16040,19692,19867,
    23700,23879,27709,27890,31717,35729,39562,39740,43571,43752,
    47579,51591,55424,55602,59433,63441,67453,71464,71962,75294,
    79303,83314,87823,91156,95165,99176,99674,103683,107694,111026,
    115534,119543,123554,126888,127386,131395,135403,139415,143246,143426,
    147255,151263,155098,155275,159106,159286,163115,167123,170958,171135,
    174967,175146,178975,179158,182810,182984,186818,186995,190827,191007,
    194835,195018,198844]]
};

checkEventRanks(full=0) = {
  my(h=198850, events=archivedEvents(), rows=List(), ds=divisors(h));
  for(i=1,#events,
    my(e=events[i], energy=Map(), rk=0, d=if(i==1,10,25));
    for(j=1,#ds,
      my(m=ds[j],cnt=vector(m));
      for(k=1,#e,cnt[1+e[k]%m]++);
      my(v=m*(cnt*cnt~));
      fordiv(m,t,if(t<m,v-=mapget(energy,t)));
      if(v<0,error("negative energy"));
      mapput(energy,m,v);
      if(v,rk+=eulerphi(m))
    );
    my(gap=eventGap(e,h,1));
    listput(rows,[#e,rk,gap,#Set(vector(#e,j,e[j]%d))])
  );
  rows=Vec(rows);
  if(rows!=[[61,198850,17940,10],[73,198850,4509,25]],error("upstream events"));
  my(best=vector(2,i,eventGap(events[i],h,if(i==1,53,953))), joint=vector(2,i,eventGap(events[i],h,157)));
  if(best!=[4541,3886] || joint!=[5047,6336],error("strided gaps"));
  if(full,
    my(opt=[h,h,h], count=0);
    for(t=1,h/2,if(gcd(t,h)!=1,next());
      count++;
      my(g1=eventGap(events[1],h,t),g2=eventGap(events[2],h,t));
      opt=[min(opt[1],g1),min(opt[2],g2),min(opt[3],max(g1,g2))]
    );
    if(opt!=[4541,3886,6336] || count!=38400,error("unit stride optimum"))
  );
  [rows,best,joint]
};

checkConvexCuts() = {
  my(K=675,n=77,t=45,u=select(x->gcd(x,K)==1,vector(K,i,i)), M=#u);
  my(inv=vector(M,i,lift(Mod(n,K)/u[i])), compatible=0);
  for(i=1,M,for(j=1,M,
    my(ok=((u[i]+u[j])*(inv[i]+inv[j])-4*n)%K==0);
    if(ok != ((u[i]-u[j])%t==0),error("midpoint classes"));
    compatible+=ok
  ));
  my(P=prod(i=1,16,prime(i)), small=P^49, large=P^51, ds=divisors(P));
  my(balanced=0);
  for(i=1,#ds,my(v=ds[i]^100); if(small<=v && v<=large,balanced++));
  [M,eulerphi(t),compatible,logint(P,2)+1,#ds,balanced]
};
