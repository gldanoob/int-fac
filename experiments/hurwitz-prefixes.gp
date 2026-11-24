\\ Cover all roots of a monic integer polynomial modulo 2^k, stopping at ceil(k/e) bits.
\\ Some prefixes may admit no full root. Their number is bounded by the degree.
hurwitzRootPrefixes(P,k) = {
  my(e = poldegree(P));
  if(k < 1 || e < 1 || pollead(P) != 1, error("expected positive k and a monic polynomial"));
  my(nodes = [0], M = 1, depth = ceil(k/e));
  for(j = 1, depth,
    my(children = List());
    foreach(nodes, r,
      my(G = subst(P,x,r+M*x), w = valuation(content(G),2));
      if(w >= k, error("monic term lost before stopping depth"));
      G /= 2^w;
      for(bit = 0, 1,
        if(subst(G,x,bit)%2 == 0, listput(children,r+M*bit))
      )
    );
    M *= 2;
    nodes = Vec(children);
    if(#nodes > e, error("prefix count exceeds degree"))
  );
  [M,nodes]
};

checkHurwitzPrefixes() = {
  \\ Compare each cover with full residue enumeration on small singular polynomials.
  for(e = 1, 7,
    my(F = sum(i=1,e,x^i));
    for(k = 1, 8,
      foreach(Set([0,1,3,2^k-1]), a,
        my(P = F-a, [M,cover] = hurwitzRootPrefixes(P,k));
        for(y = 0, 2^k-1,
          if(subst(P,x,y)%2^k == 0 && !setsearch(Set(cover),y%M),
            error("missing modular root at ",[e,k,a,y]))
        )
      )
    )
  );
  \\ Use only the residues at 3 and 3*n^2. The exponent and size guesses here
  \\ are the successful iterations of the all-input decoder.
  my(n = 902393, e = 3, k = 7, prec = 2^(k+1));
  my(ratio = Mod(3*qfbhclassno(3*n^2),prec)/Mod(3*qfbhclassno(3),prec));
  my(A = lift(ratio-n)/2, target = lift(Mod(A,2^k)/n));
  my([M,cover] = hurwitzRootPrefixes(sum(i=1,e,x^i)-target,k), found=Set([]));
  foreach(cover, root,
    if(root%2 == 0,next);
    my(r = lift(1/Mod(root,M)), P = (x+lift(Mod(r,n)/M))^e);
    foreach(zncoppersmith(P,n,4,16384), y,
      my(p = M*y+r);
      if(p > 1 && p < n && n%p^e == 0, found=setunion(found,[p]))
    )
  );
  if(found != [29] || n/29^3 != 37,error("prime-power residue recovery"));
  found
};

\\ On odd x write x=1+2*y. After scaling, the map in y has odd
\\ derivative everywhere and is a bijection modulo every power of two.
oddHurwitzRoots(e,k,target) = {
  if(e < 1 || e%2 == 0 || k < 1,error("odd positive exponent and positive precision required"));
  my(h = valuation(e+1,2), targetMod = 2^k);
  if((target-e)%2^min(k,h),return([]));
  if(k <= h,return(vector(targetMod/2,i,2*i-1)));
  my(G = sum(j=1,e, 2^j*binomial(e+1,j+1)*x^j)/2^h);
  my(value = (target-e)/2^h, y = 0, M = 1);
  for(j=1,k-h,
    if((subst(G,x,y)-value)%(2*M), y+=M);
    M *= 2
  );
  vector(2^(h-1),i,1+2*y+(i-1)*2*M)
};

checkOddHurwitzRoots() = {
  forstep(e=1,31,2,
    my(F=sum(i=1,e,x^i));
    for(k=1,8,
      my(M=2^k, table=vector(M,i,List()));
      forstep(y=1,M-1,2,listput(table[1+subst(F,x,y)%M],y));
      for(z=0,M-1,
        if(oddHurwitzRoots(e,k,z) != Vec(table[1+z]),error("odd-root mismatch ",[e,k,z]))
      )
    )
  );
  my(n=902393, k=5, E=3, modulus=2^k);
  my(A=lift(Mod(3*qfbhclassno(3*n^2),2*modulus)-n)/2, value=lift(Mod(A,modulus)/n));
  my(found=Set([]));
  foreach(oddHurwitzRoots(E,k,value), inv,
    my(r=lift(1/Mod(inv,modulus)));
    if(r>1 && n%r^E==0,found=setunion(found,[r]))
  );
  if(found != [29],error("quarter-bit odd-root test"));
  found
};

\\ Split using only n and one twist's two truncated counts. Try every odd
\\ exponent and dyadic divisor size. PARI's B parameter is a lower divisor bound.
splitHurwitzTwist(n,base,count) = {
  my(bits = logint(n,2)+1, k = ceil(bits/4), M = 2^k);
  my(A = lift(Mod(count,2*M)/Mod(base,2*M) - n)/2);
  if(type(A) != "t_INT" || A%2 == 0,return(1));
  my(target = lift(Mod(A,M)/n));
  forstep(e=1,bits,2,
    foreach(oddHurwitzRoots(e,k,target), inv,
      my(p0=lift(1/Mod(inv,M)));
      for(liftIndex=0,3,
        my(r=p0+liftIndex*M, step=4*M);
        if(r>1 && r<n && n%r==0,return(r));
        for(i=1,bits-1,
          my(B=2^i, bound=(2*B-1-r)\step);
          if(bound<1,next);
          foreach(zncoppersmith(step*x+r,n,bound,B), y,
            my(d=step*y+r);
            if(d>1 && d<n && n%d==0,return(d))
          )
        )
      )
    )
  );
  1
};

checkHurwitzSplits() = {
  my(count=0);
  foreach([7199,902393,1009*1013,11^2*17^3,3^4*5^3*7^2], n,
    my(bits=logint(n,2)+1, M=2^(ceil(bits/4)+1), found=0);
    forprime(ell=3,251,
      if(ell%8!=3 || gcd(ell,n)>1,next);
      my(base=lift(Mod(3*qfbhclassno(ell),M)));
      my(value=lift(Mod(3*qfbhclassno(ell*n^2),M)));
      my(d=splitHurwitzTwist(n,base,value));
      if(d>1 && d<n && n%d==0,found=1;break)
    );
    if(!found,error("quarter-bit decoder failed at ",n));
    count++
  );
  count
};

checkHurwitzSigns() = {
  my(cases=vector(4));
  forprime(p=5,53,
    if(p%4!=1,next);
    forprime(q=3,47,
      if(q%4!=3,next);
      my(n=p*q);
      forprime(ell=3,83,
        if(ell%8!=3 || n%ell==0,next);
        my(ratio=Mod(3*qfbhclassno(ell*n^2),8)/Mod(3*qfbhclassno(ell),8));
        my(delta=lift(ratio-n), signP=if(delta>=4,-1,1), signQ=if(delta==2 || delta==4,-1,1));
        if(delta%2 || [signP,signQ]!=[kronecker(p,ell),kronecker(q,ell)],
          error("mod-eight prime labels at ",[n,ell]));
        cases[1+delta/2]++
      )
    )
  );
  if(vecmin(cases)==0,error("missing sign pair"));
  cases
};
