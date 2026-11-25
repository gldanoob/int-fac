\\ Checks all quartics of a box at each selected prime past the lifting bound.
check(H,p) = {
  my(f,e=(p^2+1)/2,s,expected,actual,count=0,hits=0);
  if(p<=H^3+H^2 || !isprime(p), error("invalid fixture"));
  for(a=-H,H, for(b=-H,H, for(c=-H,H, for(d=-H,H,
    if(d==0, next);
    f=x^4+a*x^3+b*x^2+c*x+d;
    if(poldegree(lift(Mod(x,f)^65))<=0, next);
    expected=0;
    if(a && c^2==d*a^2,
      s=c/a;
      expected=(kronecker(s,p)==1 && kronecker(a^2-4*(b-2*s),p)==-1 && kronecker((b+2*s)^2-4*s*a^2,p)==-1)
    );
    actual=poldegree(lift(Mod(x,f*Mod(1,p))^e))<=0;
    if(actual!=expected, error([H,p,f,actual,expected]));
    count++;
    hits+=actual;
  ))));
  print([H,p,count,hits]);
};
runQuarticChecks()={
forprime(p=5,43, check(1,p));
forprime(p=13,43, check(2,p));
check(3,41);
check(4,83);
check(5,157);
check(5,167);
check(5,173);
};
iferr(runQuarticChecks(),E,print(E);quit(1));quit(0);
