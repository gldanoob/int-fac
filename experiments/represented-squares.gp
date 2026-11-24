\\ From the repository root, load this file and call checkRepresentedSquares().
read("experiments/square-walk.gp");

\\ For gcd(f[1],n)=1, return the least of the two signs of the root, or 0 for a miss.
representedSquareRoot(n, f, u, v) = {
  if(gcd(u,v) != 1, return(0));
  my(a = f[1], b = f[2], k);
  if(!issquare(a*u^2 + b*u*v + f[3]*v^2, &k) || gcd(k,2*n) != 1, return(0));
  my(r = lift(Mod(2*a*u + b*v,n) / (2*k)));
  if((r^2-a) % n != 0, error("invalid modular root"));
  min(r,n-r)
};

\\ Assume n is squarefree. Only compare witnesses on the same reduced first square.
representedSquareDivisor(n, primeBound = 19, height = 16) = {
  if(n < 3 || n % 4 != 3 || primeBound < 2 || height < 0, error("invalid input"));
  forprime(p = 2, primeBound,
    if(kronecker(-n,p) != 1, next());
    my(f = Vec(qfbred(qfbprimeform(-n,p))^2), first = 0);
    if(gcd(f[1],n) != 1, next());
    for(u = -height, height,
      for(v = 0, height,
        my(r = representedSquareRoot(n,f,u,v));
        if(!r || r == first, next());
        if(first,
          my(d = gcd(r-first,n));
          if(d <= 1 || d >= n, error("invalid witness pair"));
          return(d)
        );
        first = r
      )
    )
  );
  1
};

\\ Return [eligible inputs, represented-square splits, collision splits, union splits].
checkRepresentedSquares() = {
  my(n = 17947, g = qfbred(qfbprimeform(-n,7)), f = Vec(g^2));
  if(f != [49,43,101] || g^11 != g^0, error("unexpected norm-7 seed at -17947"));
  my(r = representedSquareRoot(n,f,1,0), s = representedSquareRoot(n,f,4,3));
  if([r,s,gcd(r-s,n),gcd(r+s,n)] != [7,6295,131,137],
    error("unexpected witnesses at -17947"));
  if(representedSquareDivisor(n,7,4) != 131 || squareCollision(n,19)[1] != 1,
    error("unexpected split at -17947"));

  my(total = 0, represented = 0, collision = 0, combined = 0, missed = List());
  forprime(p = 101, 211,
    forprime(q = p+1, 211,
      n = p*q;
      if(n % 4 != 3, next());
      my(d = representedSquareDivisor(n), e = squareCollision(n,19)[1]);
      if((d != 1 && d != p && d != q) || (e != 1 && e != p && e != q),
        error("invalid factor for ", n));
      total++;
      represented += d > 1;
      collision += e > 1;
      if(d > 1 || e > 1, combined++, listput(missed,n))
    )
  );
  my(counts = [total,represented,collision,combined]);
  if(counts != [120,110,113,119] || Vec(missed) != [13843],
    error("unexpected sweep ", counts, " with misses ", Vec(missed)));
  counts
};

checkNearSquareObstruction() = {
  my(m = 10000000551, n = m^2+2);
  if(representedSquareDivisor(13843,23,4) != 127, error("height-four split at 13843"));
  if(n != 1381662089*72376604827 || !isprime(1381662089) || !isprime(72376604827),
    error("near-square semiprime"));
  if((9*19^4+2)*16^2 >= 2*m, error("height inequality"));
  forprime(p = 3, 19,
    if(kronecker(-n,p) == 1,
      my(f = Vec(qfbprimeform(-n,p)^2), k);
      if(f[1] != p^2, error("unexpected leading coefficient at ",p));
      for(u = -16, 16, for(v = 1, 16,
        if(issquare(f[1]*u^2 + f[2]*u*v + f[3]*v^2, &k), error("unexpected square"))
      ))
    )
  )
};
