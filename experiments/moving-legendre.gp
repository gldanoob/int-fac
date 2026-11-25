\\ Exact local checks for the moving Legendre parameter proof.
\\ Run with gp -q experiments/moving-legendre.gp.

check_masses() = {
  my(models = 0, traces = 0, full = 0);
  forprime(p = 5, 97,
    my(width = 2*p + 3, total = vector(width), split = vector(width));
    for(a = 0, p-1, for(b = 0, p-1,
      if((4*a^3 + 27*b^2) % p == 0, next);
      my(e = ellinit([a,b],p), n = ellcard(e)); models++;
      total[n+1]++;
      if(n % 8 != 4, next);
      my(g = ellgroup(e));
      if(#g == 2 && g[2] % 2 == 0, split[n+1]++; full++);
    ));
    forstep(n = 4, width-1, 8,
      my(t = p+1-n, disc = 4*p-t^2);
      if(t == 0 || disc <= 0, next);
      my(h = qfbhclassno(disc), hs = qfbhclassno(disc/4));
      if(2*total[n+1] != (p-1)*h, error("ordinary mass ",[p,n,h,total[n+1]]));
      if(2*split[n+1] != (p-1)*hs, error("two-torsion mass ",[p,n,hs,split[n+1]]));
      if(h > 4*hs, error("conductor inequality ",[p,n,h,hs]));
      traces++;
    );
  );
  print("ordinary orders checked = ",traces,", nonsingular models = ",models,", full-two models at valuation two = ",full);
}

marks(p,c) = {
  my(answer = List(), seen = vector(p));
  for(t = 4, 2*p+5,
    my(bottom = (c-1)*t^2-c);
    if(bottom % p == 0, next);
    my(u = Mod((c-1)*(t-1)^2+1,p)/bottom, a = lift(c*u^2));
    if(a == 0 || a == 1 || seen[a+1], next);
    seen[a+1] = 1;
    listput(answer,a);
  );
  Vec(answer);
}

check_marks() = {
  my(points = 0, odd_hits = 0, even_hits = 0, correlations = 0);
  forprime(p = 11, 47, for(c = 2, min(p-1,9),
    my(v = marks(p,c), total = 0);
    for(lam = 0, p-1,
      my(s = sum(i=1,#v,kronecker(v[i]-lam,p)));
      total += s^2;
    );
    if(total != #v*(p-#v), error("offset correlation ",[p,c,total,#v]));
    correlations++;
    for(lam = 2, p-1, for(i=1,#v,
      my(a = v[i], d = Mod(a*(a-1)*(a-lam),p));
      if(d == 0, next);
      my(e = ellinit([0,-d*(1+lam),0,d^2*lam,0],p), point = [d*a,d^2]);
      if(!ellisoncurve(e,point), error("point equation ",[p,c,lam,a]));
      my(order = ellorder(e,point), size = ellcard(e));
      my(twice = 0, z1 = kronecker((a-1)*(a-lam),p), z2 = kronecker(a*(a-lam),p), z3 = kronecker(a*(a-1),p));
      for(x=0,p-1,
        my(ys = ellordinate(e,x));
        for(k=1,#ys, if(ellmul(e,[x,ys[k]],2) == point, twice = 1; break(2)));
      );
      if(twice != (z1 == 1 && z2 == 1 && z3 == 1), error("two-descent ",[p,c,lam,a]));
      if(kronecker(c*(c-1),p) == -1,
        if(order % 2, error("complementary mark has odd order")); even_hits++;
      );
      my(sign = kronecker(c,p));
      if(kronecker(c-1,p) == sign && kronecker(a-lam,p) == sign && size % 8 == 4,
        if(kronecker(lift(d),p) != sign || (size\4) % order || order % 2 == 0, error("target mark ",[p,c,lam,a,size,order]));
        odd_hits++;
      );
      points++;
    ));
  ));
  print("marked points = ",points,", odd-order targets = ",odd_hits,", forced even points = ",even_hits,", character identities = ",correlations);
}

iferr(check_masses(); check_marks(), e, print(e); quit(1));
quit;
