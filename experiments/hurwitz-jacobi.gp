\\ Load this file and run checkHurwitzJacobi().
checkHurwitzJacobi() = {
  my(quarticCases = 0, valuationCases = 0);
  forprime(ell = 3, 83,
    if(ell % 8 != 3, next);
    my(base = qfbhclassno(ell));
    forstep(n = 1, 151, 2,
      if(n % ell == 0 || !issquarefree(n), next);
      my(quartic = 1, ratio = qfbhclassno(ell*n^2)/base);
      \\ Test fourth-power membership directly in each prime field.
      foreach(factor(n)[,1], p,
        if(Mod(ell^2,p)^((p-1)/gcd(4,p-1)) != 1, quartic = -quartic)
      );
      if((ratio - n*kronecker(-ell,n)*(3-2*quartic)) % 8,
        error("quartic residue mismatch at ", [ell,n]));
      quarticCases++
    )
  );
  forprime(p = 3, 167,
    for(e = 1, 24,
      my(inertFactor = p^e + 2*(p^e-1)/(p-1));
      my(expected = 1 + valuation(p+1,2) + valuation(ceil(e/2),2));
      if(valuation(inertFactor - (-p)^e,2) != expected,
        error("inert local valuation mismatch at ", [p,e]));
      valuationCases++
    )
  );
  my(counts = [quarticCases,valuationCases]);
  if(counts != [405,912], error("unexpected case counts ", counts));
  counts
};
