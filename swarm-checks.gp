\\ Run from the workspace root with gp -fq swarm-checks.gp.
read("square-walk.gp");

sharedPowerFactor(n, primeBound, radius) = {
  my(identity = Qfb(1, 1, (1+n)/4), bySquare = Map());
  mapput(bySquare, Vec(identity), identity);
  forprime(p = 2, primeBound,
    if(kronecker(-n,p) != 1, next());
    my(g = qfbred(qfbprimeform(-n,p)), power = identity);
    for(k = 1, radius,
      power *= g;
      forstep(sign = -1, 1, 2,
        my(root = power^sign, key = Vec(root^2), old);
        if(mapisdefined(bySquare, key, &old),
          if(old != root,
            my(d = ambiguousDivisor(n, root * old^(-1)));
            if(d <= 1 || d >= n || n%d != 0, error("invalid split"));
            return(d)
          ),
          mapput(bySquare, key, root)
        )
      )
    )
  );
  1
};

checkSharedPowers() = {
  my(radii = [1,2,4,5,8], totals = vector(#radii), inputs = 0);
  forprime(p = 101, 211, forprime(q = p+1, 211,
    my(n = p*q);
    if(n%4 != 3, next());
    inputs++;
    for(i = 1, #radii,
      my(d = sharedPowerFactor(n,19,radii[i]));
      if(d != 1 && d != p && d != q, error("invalid factor"));
      totals[i] += (d > 1)
    )
  ));
  if(inputs != 120 || totals != [20,68,105,112,113], error("sweep mismatch"));
  my(x = qfbprimeform(-24823,11)^5, y = qfbprimeform(-24823,2));
  if(x == y || x^2 != y^2 || ambiguousDivisor(24823,x*y^(-1)) != 103, error("witness mismatch"));
  totals
};

\\ After stripping the factor base, a square residual is a usable row.
checkSieve() = {
  my(inputs = 0, noSmooth = 0, noRow = 0);
  forprime(p = 10000, 10099, forprime(q = 13500, 14000,
    my(n = p*q, a = sqrtint(n)+1, smooth = 0, row = 0);
    for(j = 0, if(n == 136225291, 129, 63),
      my(m = (a+j)^2-n);
      forprime(l = 2,31, m /= l^valuation(m,l));
      if(j < 64, smooth += (m == 1); row += issquare(m));
      if(n == 136225291 && issquare(m) != (j == 129), error("offset mismatch"))
    );
    inputs++; noSmooth += (smooth == 0); noRow += (row == 0)
  ));
  my(counts = [inputs, noSmooth, noRow]);
  if(counts != [572,275,225], error("sieve sweep mismatch"));
  counts
};

\\ An odd-difference match is possible exactly for an odd order within the cap.
oddDifference(z, width) = {
  my(step = z^2, current = z^0, table = Map());
  for(j = 0, width-1,
    if(!mapisdefined(table, Vec(current)), mapput(table, Vec(current), j));
    current *= step
  );
  my(jump = current, probe = jump*z^(-1), j);
  for(i = 1, width,
    if(mapisdefined(table, Vec(probe), &j), return(2*i*width-1-2*j));
    probe *= jump
  );
  0
};

checkOrderRoutes() = {
  my(n = 13694761, orders = [1308,436]);
  for(a = 2,3,
    my(r = orders[a-1], g = Mod(a,n));
    if(g^r != 1, error("order witness"));
    forprime(p=2,r, if(r%p == 0 && gcd(lift(g^(r/p))-1,n) != 1, error("gcd test")))
  );
  if(digits(n,1308) != [8,6,1] || n != (1+2*1308)*(1+4*1308), error("digit recovery"));
  my(g = qfbprimeform(-24823,11), d = oddDifference(g^2,4));
  if(d != 29 || ambiguousDivisor(24823,g^d) != 103, error("odd-difference witness"));
  [orders, d]
};

\\ Fixture for the missing scalar provider. The caller supplies all divisors.
\\ Evaluate the formal divisor-character sum at the requested primitive root.
fixtureScalar(divs, q, j) = {
  my(g = znprimroot(q), root = g^j);
  sum(i = 1, #divs, root^znlog(Mod(divs[i],q),g))
};

oddMoment(n, j, provider) = {
  my(residue = Mod(0,1), limit = n^(j+1), q = 4*j-1);
  while(residue.mod <= limit,
    if(q >= 7 && n%q != 0 && isprime(q),
      residue = chinese(residue, provider(q,j))
    );
    q += 4*j
  );
  lift(residue)-1
};

factorFromMoments(n, provider) = {
  if(n < 2, error("expected n >= 2"));
  my(moments = List(), size = 0);
  while(1,
    size++;
    while(#moments < 2*size-1,
      listput(moments, oddMoment(n,2*#moments+1,provider))
    );
    if(matdet(matrix(size,size,i,j,moments[i+j-1])) == 0, size--; break())
  );
  my(lo = 1, hi = n);
  while(lo+1 < hi,
    my(y = (lo+hi)\2, positive = 1);
    for(k = 1, size,
      if(matdet(matrix(k,k,i,j,2*moments[i+j]-(2*y^2+1)*moments[i+j-1])) <= 0,
        positive = 0; break()
      )
    );
    if(positive, lo = y, hi = y)
  );
  hi
};

checkMoments() = {
  for(n = 2, 64,
    my(divs = divisors(n), provider = (q,j) -> fixtureScalar(divs,q,j));
    my(found = factorFromMoments(n,provider));
    if(found != divs[2], error("moment reconstruction failed at ",n))
  );
  63
};

checkOddDifferences() = {
  my(cases = 0, solved = 0);
  forprime(p = 101, 211, forprime(q = p+1, 211,
    my(n = p*q, hit = 0);
    if(n%4 != 3, next());
    forprime(l = 2, 19,
      if(kronecker(-n,l) != 1, next());
      my(g = qfbred(qfbprimeform(-n,l)), id = g^0, x = g, order = 1);
      while(x != id, x *= g; order++);
      my(e = valuation(order,2), m = order / 2^e, h = g^15);
      for(s = 0, 6, for(L = 1, 4,
        my(d = oddDifference(h^(2^s),L));
        if((d != 0) != (s >= e && m/gcd(m,15) <= 2*L^2-1), error("match criterion"));
        cases++
      ));
      my(d = oddDifference(h^64,8));
      if(d,
        my(root = h^d);
        while(root^2 != id, root = root^2);
        if(root != id,
          my(f = ambiguousDivisor(n,root));
          if(f != p && f != q, error("invalid split"));
          hit = 1
        )
      )
    );
    solved += hit
  ));
  if([cases,solved] != [13384,113], error("odd-difference sweep mismatch"));
  [cases,solved]
};
