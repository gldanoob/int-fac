\\ Run from the repository root with
\\ gp -fq experiments/hurwitz-three-bits.gp <<<'checkHurwitzThreeBits()'

\\ For prime ell = 3 mod 8, predict 3H(ell*n^(2*t)) mod 8 from exponent bits.
threeBitsPrediction(ell,n,t,base) = {
  my(v = valuation(n,2), w = valuation(n,ell));
  my(u = n/(2^v*ell^w), factors = factor(u), A = 1, B = 1);
  for(i = 1, matsize(factors)[1],
    my(p = factors[i,1], e = factors[i,2]);
    if(p%4 != 1, next);
    if(e%2, A *= p);
    if((e\2)%2, B *= p)
  );
  my(d = [1,A*B,A,B][1+t%4]);
  my(unit = Mod(u*kronecker(u,ell),8)^t * (3-2*kronecker(d,ell)));
  my(atTwo = 3*Mod(2,8)^(v*t)-2, atEll = (ell^(w*t+1)-1)/(ell-1));
  lift(base*unit*atTwo*atEll)
};

\\ Enumerate all reduced forms at m = ell*f^2, including imprimitive ones.
\\ The only exceptional weight here is 3H's weight 1 for a = b = c.
threeBitsFormCount(m) = {
  my(total = 0);
  forstep(b = m%2, sqrtint(m\3), 2,
    my(ac = (m+b^2)/4);
    fordiv(ac,a,
      if(a < b || a^2 > ac, next);
      my(boundary = b == 0 || a == b || a^2 == ac);
      total += if(a == b && a^2 == ac, 1, if(boundary,3,6))
    )
  );
  total
};

checkThreeBitsCase(ell,n,t,base) = {
  my(m = ell*n^(2*t), actual = threeBitsFormCount(m)%8);
  my(predicted = threeBitsPrediction(ell,n,t,base));
  if(actual != predicted,
    error("3H mismatch at [ell,n,t,actual,predicted] = ", [ell,n,t,actual,predicted]))
};

checkHurwitzThreeBits() = {
  read("experiments/hurwitz-residues.gp");
  my(cases = 0, triples = 0);
  forprime(ell = 3, 83,
    if(ell%8 != 3, next);
    my(base = 3*qfbhclassno(ell));
    for(n = 1, 180,
      for(t = 1, 6,
        if(n^t > 180 || (n == 1 && t > 1), break);
        checkThreeBitsCase(ell,n,t,base);
        my(m = ell*n^(2*t));
        if(m%8 == 3 && m <= 50000,
          if(positiveTriples(m)%8 != threeBitsPrediction(ell,n,t,base),
            error("three-square mismatch at ", [ell,n,t]));
          triples++
        );
        cases++
      )
    )
  );
  \\ A full nonconstant period and both steps after the wrap.
  for(t = 1, 6, checkThreeBitsCase(3,5,t,1); cases++);
  \\ At n = 5^2*13 the exponent bits select A = 13 and B = 5.
  \\ These twists realize all four pairs of signs.
  foreach([3,11,67,131], ell,
    checkThreeBitsCase(ell,325,1,3*qfbhclassno(ell));
    cases++
  );
  \\ The public Jacobi symbol and the first query agree; the second query differs.
  foreach([11,43], ell,
    my(n = 375, base = 3*qfbhclassno(ell), J = kronecker(n,ell));
    my(observed = vector(2,t,lift(Mod(threeBitsFormCount(ell*n^(2*t)),8)/(base*(n*J)^t))));
    if(J != 1 || observed != [1,if(ell == 11,1,5)], error("second power at ",ell))
  );
  print("Passed ", cases, " form-count comparisons, ", triples,
        " three-square comparisons, and the second-power example.")
};
