assert_equal(actual, expected) = {
  if(actual != expected, error("expected ", expected, ", got ", actual));
}

weight_sum(decomp) = {
  sum(j = 1, #decomp, decomp[j].e * decomp[j].f / 2^valuation(decomp[j].e, 2));
}

{
base = nfinit(x^2 + 1);
for(i = 0, 2,
  q = (11 * 19^2)^(2^i);
  mark = Mod(q*x, base.pol);
  assert_equal(norm(mark), q^2);
  extension = nfinit(x^4 + q^2);
  z_min = 0;
  remaining = q;
  while(issquare(remaining),
    remaining = sqrtint(remaining);
    z_min++;
  );
  assert_equal(z_min, i);
  passes = (4 / 2^max(0, 1 - z_min) == 4);
  all_even = 1;
  forprime(p = 11, 19,
    if(q % p, next);
    downstairs = idealprimedec(base, p);
    upstairs = idealprimedec(extension, p);
    assert_equal(weight_sum(downstairs), 2);
    z = valuation(valuation(q, p), 2);
    assert_equal(weight_sum(upstairs), 4 / 2^max(0, 1 - z));
    for(j = 1, #downstairs,
      if(idealval(base, mark, downstairs[j]) % 2, all_even = 0);
    );
  );
  assert_equal(passes, all_even);
  print("square norm, minimum exponent ", z_min, ", private ideal parity passes: ", passes);
);
}
