\\ From the repository root, load experiments/seed-powers.gp and run checkSeedPowers().
read("experiments/represented-squares.gp");

\\ For discriminant -n, return [even exponent, reduced p-power, primitive witness].
seedEvenPowerWitness(n, p) = {
  if(n < 3 || (n%4 != 0 && n%4 != 3) || !isprime(p) || kronecker(-n,p) != 1,
    error("expected a negative order discriminant and a split prime"));
  my(A = 1, exponent = 0, seed = qfbprimeform(-n,p));
  while(3*A^2 <= n, A *= p^2; exponent += 2);
  my(raw = qfbpowraw(seed,exponent), [f,M] = qfbredsl2(raw), a = Vec(f)[1]);
  if(Vec(raw)[1] != A || f != qfbred(seed)^exponent,
    error("wrong prime-power representative at ", [-n,p]));
  \\ PARI gives f(x) = raw(M*x), so raw's first basis vector pulls back by M^-1.
  if(matdet(M) != 1 || M~*Mat(raw)*M != Mat(f), error("reduction matrix at ", [-n,p]));
  my(w = M^-1*[1,0]~, u = w[1], v = w[2]);
  if(qfeval(f,w) != A || gcd(u,v) != 1 || v == 0,
    error("invalid transported representation at ", [-n,p]));
  \\ sqrt(3n)/(4p^2) <= a <= sqrt(n/3), |v| <= 2p/sqrt(3), |u| < 2p^2.
  if(16*p^4*a^2 < 3*n || 3*a^2 > n || 3*v^2 > 4*p^2 || abs(u) >= 2*p^2,
    error("even-power bounds at ", [-n,p]));
  [exponent,f,w]
};

\\ Compare roots on this single reduced form in the repository's height-16 box.
seedPowerBoxDivisor(n, f) = {
  my(coeff = Vec(f), first = 0);
  if(gcd(coeff[1],n) != 1, return(1));
  for(u = -16, 16, for(v = 0, 16,
    my(r = representedSquareRoot(n,coeff,u,v));
    if(r,
      if(first && r != first, return(gcd(r-first,n)));
      first = r
    )
  ));
  1
};

checkLaterSeedPowers() = {
  my(total = 0, counts = [0,0,0], misses = List());
  forprime(p = 101, 211, forprime(q = p+1, 211,
    my(n = p*q, best = 4);
    if(n%4 != 3, next());
    total++;
    forprime(seedPrime = 2, 19,
      if(kronecker(-n,seedPrime) != 1, next());
      my(f = qfbred(qfbprimeform(-n,seedPrime)));
      for(depth = 1, best-1,
        f = f^2;
        my(d = seedPowerBoxDivisor(n,f));
        if(d == 1, next());
        if(d != p && d != q, error("invalid divisor at ", [n,seedPrime,depth]));
        best = depth; break()
      )
    );
    for(depth = best, 3, counts[depth]++);
    if(best == 4, listput(misses,n))
  ));
  if(total != 120 || counts != [110,118,119] || Vec(misses) != [13843],
    error("later-power sweep ", [total,counts,Vec(misses)]));
  concat(total,counts)
};

\\ Return [crossing/even-power seed pairs, sharp orbits, [semiprimes, hits through depths 1,2,3]].
checkSeedPowers() = {
  my(pairs = 0);
  for(n = 500, 10000,
    if(n%4 != 0 && n%4 != 3, next());
    forprime(p = 2, 19,
      if(kronecker(-n,p) != 1 || 4*p^3 >= n, next());
      my(A = p, f = qfbred(qfbprimeform(-n,p)));
      while(4*A^3 < n,
        if(Vec(f)[1] != A, error("before cube-root crossing at ", [-n,p,A]));
        A = A^2; f = f^2
      );
      my(a = Vec(f)[1]);
      if(4*a^3 < n || a < min(A,n/(4*A)) || a > A,
        error("missed cube-root crossing at ", [-n,p,A]));
      seedEvenPowerWitness(n,p);
      pairs++
    )
  );
  if(pairs != 7863, error("unexpected seed count ", pairs));

  for(h = 1, 8,
    my(s = 3^(2^h), n = 4*s^3-1, f = qfbprimeform(-n,3), A = 3);
    for(j = 1, h,
      if(Vec(f)[1] != A || A >= s, error("unexpected early peak at ", [h,j]));
      f = f^2; A = A^2
    );
    if(f != Qfb(s,1,s^2) || f^2 != Qfb(s,-1,s^2) || (f^2)^2 != f,
      error("sharp orbit at ", h))
  );

  \\ A non-dyadic example where using M instead of its inverse gives the wrong value.
  my(n = 10000000551^2+2, [exponent,f,w] = seedEvenPowerWitness(n,13));
  if(exponent != 10 || abs(w[2]) != 4 || qfeval(f,w) != 13^10,
    error("near-square example"));
  [pairs,8,checkLaterSeedPowers()]
};
