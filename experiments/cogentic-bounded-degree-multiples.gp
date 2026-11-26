check_multiple_bounds(n, m, d, e, q, k, ell) = {
  my(f=q*x^d+(q+1)*x^(d-1), g=(q+2)*x^e-x^(e-1));
  f+=k*n-subst(f,x,m);
  g+=ell*n-subst(g,x,m);
  if(subst(f,x,m)!=k*n || subst(g,x,m)!=ell*n, error("bad evaluated multiple"));
  my(r=polresultant(f,g));
  my(f_norm=sum(i=0,d,polcoeff(f,i)^2), g_norm=sum(i=0,e,polcoeff(g,i)^2));
  if(!r || r%n || r^2>f_norm^e*g_norm^d, error("bad resultant bound"));
  for(a=-12,12, for(b=1,12,
    if(gcd(a,b)!=1, next);
    my(delta=abs(b*m-a));
    if(!delta || gcd(b,delta)!=1, error("bad replay mark"));
    if((b^d*(subst(f,x,a/b)-k*n))%delta ||
      (b^e*(subst(g,x,a/b)-ell*n))%delta, error("bad marked norm congruence"));
  ));
}

iferr({
  check_multiple_bounds(1387,37,2,2,3,5,7);
  check_multiple_bounds(901,17,2,3,13,6,11);
  check_multiple_bounds(1022117,101,3,4,5,19,3);
  print("Verified marked congruences and resultants on three nonmonic pairs");
}, err, print(err); quit(1));
