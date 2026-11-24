\\ Load this file and run checkTwistedConvergents().
\\ Return [X,Y,Q,root] for each hit, with Q >= 0 and the smaller root up to sign.
twistedConvergents(n,h,t,H) = {
  foreach([n,h,t,H], v, if(type(v) != "t_INT", error("expected integer inputs")));
  if(n < 3 || n%2 == 0 || h < 1 || t < 1 || H < 1 || gcd(h*t,n) != 1,
    error("invalid modulus, twist or bound"));
  if(!issquarefree(h), error("expected squarefree h"));
  my(D = h*t*n, a0 = sqrtint(D));
  if(a0^2 == D, error("square radicand"));

  my(m = 0, d = 1, digit = a0, prev = [1,0], xy = [a0,1], hits = List());
  while(xy[2] <= H,
    my([x,y] = xy, R = x^2-D*y^2, Q);
    if(R >= 0 && issquare(h*R,&Q) && gcd(x,n) == 1,
      my(r = lift(Mod(Q,n)/x));
      if((r^2-h)%n, error("invalid modular root"));
      listput(hits,[x,y,Q,min(r,n-r)])
    );
    m = d*digit-m;
    d = (D-m^2)/d;
    digit = (a0+m)\d;
    [prev,xy] = [xy,digit*xy+prev]
  );
  Vec(hits)
};

checkTwistedConvergents() = {
  \\ Choose [h,z,b,u,v,k,t], then solve F(u,v)=k^2 and disc(F)=-t*n for c,n.
  my(cases = [[2,1,1,0,1,30,1], [2,1,1,0,1,283,89], [5,3,-1,-1,4,200001,41]]);
  my(rows = List());
  for(i = 1, #cases,
    my([h,z,b,u,v,k,t] = cases[i], a = h*z^2, H = v);
    my(c = (k^2-a*u^2-b*u*v)/v^2, n = (4*a*c-b^2)/t);
    if(type(c) != "t_INT" || type(n) != "t_INT" || abs(b) > a || abs(u) > H ||
       gcd(u,v) != 1 || gcd(2*a*k,n) != 1 || 81*h*a^4*H^4 >= t*n,
      error("invalid bounded witness ", cases[i]));

    my(s = 2*a*u+b*v, t0 = gcd(2*h*z*k,v));
    my(r = lift(Mod(s,n)/(2*z*k)));
    my(hit = [2*h*z*k/t0, v/t0, abs(h*s)/t0, min(r,n-r)]);
    if(twistedConvergents(n,h,t,H) != [hit], error("witness mismatch at ", n));
    listput(rows,concat([n,t,t0],hit))
  );
  rows = Vec(rows);
  my(factorFound = gcd(rows[2][7]-rows[1][7],7199));
  if(rows != [[7199,1,1,120,1,2,120], [7199,89,1,1132,1,2,1132],
              [10975719499,41,2,3000015,2,235,5371032946]] || factorFound != 23,
    error("unexpected regression result ", rows));
  \\ 12/1 gives a square residual at 135, but its numerator has gcd 3.
  if(#twistedConvergents(135,1,1,1), error("accepted a noninvertible numerator"));
  [rows,factorFound]
};
