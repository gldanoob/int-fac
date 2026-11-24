\\ Count witnesses for the six products in the primitive-form description.
\\ Bound variables directly so a second witness would be counted.
primitiveWitnessCount(a, middle, c) = {
  my(count = 0);
  fordiv(a, d,
    if(middle % d, next);
    my(x = a / d, y = middle / d);
    for(u = 0, x - 1,
      if((y*u + 1) % x, next);
      for(w = 0, c - 1, if((d*w + 1) % c == 0, count++))
    )
  );
  count
};

checkPrimitiveForms(limit = 400) = {
  my(tested = 0);
  for(n = 3, limit,
    if(n % 4 != 0 && n % 4 != 3, next);
    my(raw = 0, certified = 0);
    for(a = 1, sqrtint(n \ 3),
      for(b = -a, a,
        if((b^2 + n) % (4*a), next);
        my(c = (b^2 + n) / (4*a));
        if(c < a || (b < 0 && (abs(b) == a || a == c)), next);
        my(count = primitiveWitnessCount(a, abs(b), c));
        if(count != (gcd(gcd(a, abs(b)), c) == 1),
          error("witness count for ", [a,b,c], " is ", count));
        raw++;
        certified += count
      )
    );
    if(certified != qfbclassno(-n), error("class number at ", -n));
    if(n == 99 && [raw, certified] != [3, 2], error("discriminant -99"));
    tested++
  );
  if(Vec(qfbprimeform(-175,23)^3) != [7,7,8], error("split at -175"));
  if(Vec(qfbprimeform(-975,11)^4) != [16,7,16], error("split at -975"));
  tested
};
