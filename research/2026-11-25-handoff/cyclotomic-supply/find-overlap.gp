seen=Map();
{
forprime(p=101,1000000,
  my(f=p^2+p+1, d=f/3^valuation(f,3));
  foreach(divisors(d),g,
    if(g*100<p^2,next);
    foreach(divisors(g),a,
      my(c=g/a,q);
      if(gcd(a,c)>1,next);
      q=lift(chinese(Mod(p,a),Mod(-p-1,c)));
      q+=g*max(0,1+(p-q)\g);
      if(q>p && q<=2*p && !mapisdefined(seen,[p,q]) && isprime(q),
        my(D=gcd(f,q^2+q+1), D0=D/3^valuation(D,3));
        mapput(seen,[p,q],1);
        if(g==D0,print([p,q,D,gcd(q-p,D0),gcd(q+p+1,D0),p*q/D]))
      )
    )
  )
)
}
