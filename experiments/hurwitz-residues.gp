\\ Load this file and run checkHurwitzResidues().
oddPrimitiveClassNumber(d) = {
  my(m = -d);
  if(m == 4 || m == 8 || m == 16, return(1));
  if(m % 4 == 0, m /= 4);
  m % 4 == 3 && isprimepower(m) != 0
};

\\ Each content gives a primitive order discriminant; only -3 and -4 have extra units.
weightedClassCount(m) = {
  my(total = 0);
  fordiv(m, f,
    if(m % f^2, next);
    my(d = -m / f^2);
    if(d % 4 > 1, next);
    my(weight = if(d == -3, 4, if(d == -4, 6, 12)));
    total += weight * qfbclassno(d)
  );
  total
};

threeH(m) = {
  my(twelveH = 12*qfbhclassno(m));
  if(type(twelveH) != "t_INT" || twelveH % 4, error("nonintegral 3H at ", m));
  twelveH / 4
};

\\ At m = 3 mod 8 all coordinates are odd. Signs give eight copies of each positive triple.
positiveTriples(m) = {
  my(count = 0);
  forstep(x = 1, sqrtint(m), 2,
    forstep(y = 1, sqrtint(m-x^2), 2,
      if(issquare(m-x^2-y^2), count++)
    )
  );
  count
};

checkClassNumbers() = {
  my(norms = [3, 4, 12, 28], expected = [4, 6, 16, 24], count = 0);
  for(i = 1, #norms,
    my(m = norms[i]);
    if(qfbclassno(-m) != 1 || 12*qfbhclassno(m) != expected[i],
      error("class-number normalization at ", -m))
  );
  for(m = 3, 500,
    if((-m) % 4 > 1, next);
    if(oddPrimitiveClassNumber(-m) != qfbclassno(-m) % 2, error("parity at ", -m));
    if(weightedClassCount(m) != 12*qfbhclassno(m), error("12H at ", m));
    if(m % 8 == 3 && threeH(m) != positiveTriples(m), error("three squares at ", m));
    count++
  );
  count
};

checkModFour() = {
  my(count = 0);
  forstep(a = 3, 127, 4,
    forstep(f = 1, 55, 2,
      if(gcd(a,f) > 1, next);
      if((threeH(a*f^2) - threeH(a)*f*kronecker(-a,f)) % 4, error("lift ", [a,f]));
      count++
    )
  );
  count
};

\\ Factorization labels the expected successful twists for this finite comparison.
checkIsolation(n, factors, target) = {
  my(p = factors[target,1], e = factors[target,2], c = n/p^e);
  forprime(ell = 3, 2000,
    if(ell % 8 != 3 || gcd(ell,n) > 1, next);
    my(signs = vector(matsize(factors)[1], i, kronecker(-ell, factors[i,1])));
    if(signs != vector(#signs, i, if(i == target, -1, 1)), next);
    my(base = threeH(ell), h1 = threeH(ell*n^2), h2 = threeH(ell*n^4));
    my(raw = sumdiv(n,f,qfbclassno(-ell*f^2)));
    if(3*raw-if(ell==3,2,0) != h1,error("unweighted form count ",[n,ell]));
    my(a = c*(p^e-1)/(p-1));
    if(base % 2 != 1 || h1 != base*(n+2*a) || h2 != base*(n^2+2*a*(n+c)),
      error("exact twist ", [n,p,ell]));
    for(k = 1, 8,
      my(s = 2^k, inputMod = 2*s, inv = Mod(base % inputMod,inputMod)^-1);
      my(delta1 = lift((h1 % inputMod)*inv - n), delta2 = lift((h2 % inputMod)*inv - n^2));
      if(delta1 % 2 || delta2 % 2, error("halving ", [n,p,ell,k]));
      my(aLow = delta1/2, bLow = delta2/2);
      if(aLow % 2 != 1 || lift(bLow/Mod(aLow,s) - n) != c % s,
        error("residue recovery ", [n,p,ell,k]));
      if(e == 1 && aLow != c % s, error("single ratio ", [n,p,ell,k]))
    );
    return()
  );
  error("finite twist search exhausted ", [n,p])
};

checkHurwitzResidues() = {
  my(classes = checkClassNumbers(), lifts = checkModFour(), cases = 0, squarefree = 0);
  forstep(n = 15, 151, 2,
    my(factors = factor(n), t = matsize(factors)[1]);
    if(t < 2, next);
    for(i = 1, t,
      if(factors[i,2] % 2 == 0, next);
      checkIsolation(n, factors, i);
      cases++;
      if(issquarefree(n), squarefree++)
    )
  );
  print("Passed: ", classes, " primitive parity and 12H comparisons, ", lifts,
        " mod-four lifts, ", cases, " isolated-prime cases at eight precisions (",
        squarefree, " squarefree).")
};
