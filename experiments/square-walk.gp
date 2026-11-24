\\ Load with gp -fq experiments/square-walk.gp and run checkWalks().
\\ Experiments assume n is odd, squarefree and congruent to 3 modulo 4.
\\ For an odd fundamental discriminant -n, a nonidentity ambiguous form splits n.
ambiguousDivisor(n, z) = {
  my(t = Vec(z), a = t[1], b = t[2], c = t[3]);
  if(a != c && b != a && b != 0, error("expected a reduced ambiguous form"));
  gcd(n, if(a == c, 2*a-b, a))
};

\\ Try each split prime separately. A zero cap runs until the orbit closes.
\\ Return [factor, starting prime, squarings on that prime] or [1,0,0].
squareCollision(n, bound, depth = 0) = {
  if(n < 3 || n % 4 != 3 || bound < 2 || depth < 0, error("invalid input"));
  forprime(p = 2, bound,
    if(kronecker(-n, p) != 1, next());
    my(z = qfbred(qfbprimeform(-n,p)), roots = Map(), steps = 0);
    while(depth == 0 || steps < depth,
      my(h = z^2, key = Vec(h), previous);
      steps++;
      if(mapisdefined(roots, key, &previous),
        if(previous != z,
          my(t = z * previous^(-1), d = ambiguousDivisor(n,t));
          if(t^2 != h^0 || d <= 1 || d >= n, error("invalid collision witness"));
          return([d,p,steps])
        );
        break()
      );
      mapput(roots, key, z);
      z = h
    )
  );
  [1,0,0]
};

\\ Deterministic relation-search experiment for odd squarefree n = 3 (mod 4).
\\ Calls with depth = 0 exhaust the finite squaring orbits (small tests only).
\\ Return [divisor or 1, distinct roots, smooth rows, binary nullity].
squareWalk(n, bound, depth = 0, pairs = 0) = {
  if (n < 3 || n % 4 != 3 || bound < 2 || depth < 0, error("invalid input"));
  my(D = -n, primes = List());
  forprime(p = 2, bound, if(kronecker(D, p) == 1, listput(primes, p)));
  my(k = #primes, forms = vector(k, i, qfbprimeform(D, primes[i])));
  my(identity = Qfb(1, 1, (1-D)/4), frontier = List());
  for(i = 1, k, listput(frontier, qfbred(forms[i])));
  if(pairs, for(i = 1, k, for(j = i+1, k, listput(frontier, forms[i]*forms[j]))));
  my(seen = Map(), roots = List(), rows = List(), level = 0);
  while(#frontier && (depth == 0 || level < depth),
    my(following = List());
    for(i = 1, #frontier,
      my(z = frontier[i], key = Vec(z));
      if(mapisdefined(seen, key), next());
      mapput(seen, key, 1);
      my(h = z^2, coeff = Vec(h), a = coeff[1], v = vector(k));
      listput(following, h);
      for(j = 1, k,
        my(p = primes[j], e = valuation(a, p));
        if(e,
          a /= p^e;
          v[j] = if((coeff[2]-Vec(forms[j])[2]) % (2*p) == 0, e, -e)
        )
      );
      if(a == 1,
        if(h != identity * prod(j = 1, k, forms[j]^v[j]), error("invalid signed row"));
        listput(rows, v~);
        listput(roots, z)
      )
    );
    frontier = following;
    level++
  );
  if(!#rows, return([1, #seen, 0, 0]));
  my(A = Mat(Vec(rows)), basis = lift(matker(Mod(A,2))), d = matsize(basis)[2]);
  for(i = 1, d,
    my(bits = basis[,i], halves = (A*bits)/2, z = identity);
    for(j = 1, #roots, if(bits[j], z *= roots[j]));
    for(j = 1, k, z *= forms[j]^(-halves[j]));
    if(z^2 != identity, error("dependency did not yield 2-torsion"));
    my(divisor = ambiguousDivisor(n,z));
    if(divisor > 1 && divisor < n, return([divisor, #seen, #rows, d]))
  );
  [1, #seen, #rows, d]
};

\\ Enumerate all 120 eligible pairs. Known prime factors are used only to score.
checkWalks() = {
  my(total = 0, single = 0, mixed = 0, collision = 0);
  forprime(p = 101, 211,
    forprime(q = p+1, 211,
      my(n = p*q);
      if(n % 4 != 3, next());
      total++;
      my(results = [squareWalk(n,19)[1], squareWalk(n,19,0,1)[1], squareCollision(n,19)[1]]);
      for(i = 1, 3,
        if(results[i] != 1 && results[i] != p && results[i] != q, error("invalid factor"))
      );
      single += results[1] > 1;
      mixed += results[2] > 1;
      collision += results[3] > 1
    )
  );
  my(counts = [total, single, mixed, collision]);
  if(counts != [120,108,111,113], error("unexpected sweep totals"));
  if(squareWalk(11227,19) != [1,7,4,3] || squareWalk(11227,19,0,1)[1] != 103,
    error("mixed-seed example failed"));
  if(squareWalk(24823,19,0,1) != [1,30,12,11] || squareCollision(24823,19) != [103,11,29],
    error("discarded collision example failed"));
  if(squareCollision(17947,19)[1] != 1 || squareCollision(17947,43)[1] != 131,
    error("odd-order subgroup example failed"));
  counts
};
