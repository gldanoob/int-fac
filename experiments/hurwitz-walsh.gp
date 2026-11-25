\\ Load this file and run checkHurwitzWalsh(). Bit i-1 labels the twist prime s[i].
\\ For m = 3 mod 8 all coordinates are odd. With z fixed, the two-square
\\ divisor sum counts ordered positive pairs (the four sign choices removed).
walshThreeH(m) = {
  my(count = 0);
  forstep(z = 1, sqrtint(m), 2,
    count += sumdiv(m-z^2, a, kronecker(-4,a))
  );
  if(count != 3*qfbhclassno(m), error("three-square count at ",m));
  count
};

walshDiscriminants(s) = {
  vector(2^#s,t,3*prod(i=1,#s,if(bittest(t-1,i-1),s[i],1)))
};

\\ low contains only the least K bits of each count. Remove the base's
\\ power of two in the integers before inverting its odd part.
walshUnits(n, base, low, K) = {
  my(v = vector(#base,i,valuation(base[i],2)), loss = vecmax(v));
  if(K <= loss, error("no common precision at ",[K,loss]));
  my(M = 2^(K-loss));
  vector(#base,i, Mod(low[i]/2^v[i],M) / (n*(base[i]/2^v[i])))
};

walshProduct(units, S) = {
  prod(t=0,#units-1, units[t+1]^((-1)^hammingweight(bitand(t,S))))
};

\\ Rank two, exponent one. In the isolated channel one orientation of W is
\\ (1+2/p)^2. Its root congruent to 3 mod 4 determines p modulo 2^(k-2).
\\ Try its least residue and verify it, which suffices for the finite fixtures.
walshSplit(n, base, low, K) = {
  my(u = walshUnits(n,base,low,K), k = logint(u[1].mod,2));
  if(#u != 4 || k < 3, error("rank two and three common bits required"));
  for(S=1,3,
    my(w = walshProduct(u,S));
    foreach([w,1/w], square,
      my(root = sqrt(lift(square) + O(2^k)));
      if(lift(root)%4 == 1, root = -root);
      my(r = lift(2/(root-1)));
      if(r > 1 && r < n && n%r == 0, return(r))
    )
  );
  1
};

checkWalshCase(n, s, {splitK=0}) = {
  my(d = #s, size = 2^d);
  if(n < 1 || gcd(n,6) != 1 || d < 1 || #Set(s) != d, error("bad fixture ",[n,s]));
  foreach(s,q, if(q%8 != 1 || !isprime(q) || n%q == 0, error("bad twist ",[n,q])));
  my(D = walshDiscriminants(s));
  my(base = vector(size,t,walshThreeH(D[t])), counts = vector(size,t,walshThreeH(D[t]*n^2)));
  my(exact = vector(size,t,counts[t]/(base[t]*n)), loss = vecmax(vector(size,t,valuation(base[t],2))));

  \\ Only the expectation sees factor(n). Each bin starts at the empty product.
  my(f = factor(n), expected = vector(size-1,S,1));
  for(i=1,matsize(f)[1],
    my(p = f[i,1], e = f[i,2], S = sum(j=1,d, 2^(j-1)*(kronecker(s[j],p) == -1)));
    if(S,
      my(localUnit = 1 + 2*sum(j=1,e,p^(-j)));
      expected[S] *= localUnit^(-kronecker(-3,p)*2^(d-1))
    )
  );
  for(S=1,size-1,
    if(walshProduct(exact,S) != expected[S], error("exact Walsh product at ",[n,s,S]))
  );
  for(k=1,10,
    my(K = k+loss, M = 2^k, low = vector(size,t,counts[t]%2^K));
    my(u = walshUnits(n,base,low,K));
    for(t=1,size,
      if(u[t].mod != M || u[t] != Mod(exact[t],M), error("truncated unit at ",[n,s,t-1,K]))
    );
    for(S=1,size-1,
      if(walshProduct(u,S) != Mod(expected[S],M), error("truncated Walsh product at ",[n,s,S,K]))
    )
  );
  if(splitK,
    if(vecmin(counts) < 2^splitK, error("split fixture needs wrapped counts"));
    return(walshSplit(n,base,vector(size,t,counts[t]%2^splitK),splitK))
  );
  1
};

\\ At rank four each nonzero coefficient is an eighth power. For k >= 5
\\ its 16 odd roots modulo 2^k are the eight lifts of each sign modulo 2^(k-3).
walshEighthGcds(n, w) = {
  my(M = w.mod, k = logint(M,2), hits = List());
  if(k < 5, error("five common bits required for sixteen roots"));
  my(z = lift(sqrtn(lift(w)+O(2^k),8)), step = M/8);
  \\ All roots agree up to sign modulo step. With 2*B^2 < step at most one
  \\ positive fraction of height <= B can survive across all sixteen lifts.
  my(B = sqrtint((step-1)\2));
  for(j=0,7,
    foreach([z,-z], a,
      my(root = Mod(a+j*step,M));
      if(root^8 != w, error("invalid eighth root"));
      my(r = bestappr(root,B));
      if(r == [] || r <= 0 || numerator(r) > B, next);
      my(g = gcd(n,numerator(r)), h = gcd(n,denominator(r)));
      if((g > 1 && g < n) || (h > 1 && h < n), listput(hits,[r,g,h]))
    )
  );
  Set(hits)
};

checkWalshSignedCell() = {
  my(primes = [7,11,19,23,29,31,37,43,47,53,59,61,67,71,79,83,89]);
  my(n = vecprod(primes), s = [17,41,73,113], D = walshDiscriminants(s));
  my(K = ceil((logint(n,2)+1)/4), base = vector(16,t,3*qfbhclassno(D[t])));
  \\ For this 90-bit fixture PARI supplies the low counts directly to the decoder.
  my(low = vector(16,t,(3*qfbhclassno(D[t]*n^2))%2^K));
  my(u = walshUnits(n,base,low,K), w = vector(15,S,walshProduct(u,S)));
  my(hits = vector(15,S,walshEighthGcds(n,w[S])));

  \\ The decoder above never receives these labels, the cell product or its height.
  my(cell = select(p->vector(4,i,kronecker(s[i],p)) == [-1,-1,-1,1],primes));
  if(cell != [7,11] || vector(2,i,kronecker(-3,cell[i])) != [1,-1], error("signed mask 7"));
  my(P = vecprod(cell), ratio = (1+2/11)/(1+2/7));
  if(K != 23 || w[7].mod != 2^19 || lift(w[7]) != 232513 || Mod(ratio,2^19)^8 != w[7],
    error("quarter-bit signed coefficient"));
  if(max(numerator(ratio),denominator(ratio)) > 2*P || 2*(2*P)^2 >= w[7].mod/8,
    error("signed cell reconstruction height"));
  hits[7]
};

\\ All twelve prime divisors survive trial division through 8*b. The first
\\ occurs twice. The recovery step receives only n, small bases and low counts.
checkWalshResidual() = {
  my(n = 12307449425254612247075244953265945809281861054667267, bits = logint(n,2)+1);
  my(f = factor(n), D = walshDiscriminants([17,41,73,113]), K = ceil(bits/4)+1);
  if(#f[,1] != 12 || vecmin(f[,1]) <= 8*bits || vecmax(f[,2]) != 2, error("residual fixture"));
  my(base = vector(16,i,3*qfbhclassno(D[i])), low = vector(16,i,3*qfbhclassno(D[i]*n^2)%2^K));
  my(u = walshUnits(n,base,low,K));
  my(hits = select(h->#h, vector(15,S,walshEighthGcds(n,walshProduct(u,S)))));
  if(#hits != 11 || hits[1] != [[10039/10041,10039,1]], error("residual reconstruction"));
  #hits
};

checkHurwitzWalsh() = {
  my(s = [17,41]);
  checkWalshCase(1,[17]);
  checkWalshCase(5^3*7,[17]);
  checkWalshCase(5^2*7,s);
  checkWalshCase(5*7,[17,41,73]);
  \\ Masks 1,2,3 give (7/5)^2, 1, (91/99)^2. The 7 and 11 share mask 3.
  if(checkWalshCase(5*7*11,s,7) != 5, error("seven-bit Walsh split"));
  \\ 59 has mask zero and contributes the same nontrivial unit to every twist.
  if(checkWalshCase(13*59,s,8) != 13, error("eight-bit inverse Walsh split"));
  checkWalshResidual();
  if(checkWalshSignedCell() != [[91/99,7,11]], error("signed cell reconstruction and gcds"));
  print("Passed 18 exact and 180 truncated Walsh products, splits 385 -> 5 and 767 -> 13,",
        " and the 90-bit signed cell 91/99 -> [7,11] from 23-bit counts.")
};
