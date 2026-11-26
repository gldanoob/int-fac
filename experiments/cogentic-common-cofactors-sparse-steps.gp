\\ Replay exact cofactors, prescribed target reductions, and widened steps.
{
m = 1000; n = m^4-11; cd = 215233605; k = 213088919; p0 = 30;
targets = [83, 89]; marks = [1..20];
for(a=1,20,if(gcd(n,m-a)!=1,error("mark is not a unit")));
forprime(p=2,101,if(k%p==0,error("cofactor touches factor base")));
if(gcd(k,prod(a=1,20,m-a))!=1 || k*n%p0!=1,error("cofactor constraints"));
nominal = cd*prod(j=1,4,x-j);
start = floor(subst(nominal,x,m)/n)+1;
start += (lift(Mod(n,p0)^-1)-start)%p0;
forstep(candidate=start,k-1,p0,
  if(gcd(candidate,prod(a=1,20,m-a)*prod(i=1,26,prime(i)))==1,error("earlier cofactor"))
);

polys = [
  cd*x^4-2152208970*x^3+7533722190*x^2-10759700955*x+5166976891,
  cd*x^4-2152209540*x^3+7534291800*x^2-10759311705*x+5167726891,
  cd*x^4-2152209570*x^3+7534322280*x^2-10759790625*x+5166646891,
  cd*x^4-2152208610*x^3+7533362370*x^2-10759881915*x+5167936891
];
for(j=1,4,
  ell=targets[(j+1)\2];
  f=polys[j];
  if(subst(f,x,m)!=k*n || !polisirreducible(Mod(1,2)*f),error("evaluation or binary reduction"));
  roots=polrootsmod(f,ell);
  if(#roots!=if(j%2,4,0),error("target splitting type"));
  for(i=1,#roots,if(subst(deriv(f),x,roots[i])==0,error("repeated target root")));
  g=p0*ell; D=2^20; U=2^32; Up=U/D;
  sparse=f+g*D*(x-m)*(15+3*x);
  dense=f+g*(x-m)*(15*D+3*D*x);
  if(sparse!=dense || subst(sparse,x,m)!=k*n,error("sparse evaluation"));
  for(a=1,20,
    q=g*(m-a); qp=q*D;
    if(q/eulerphi(q)!=qp/eulerphi(qp),error("coprime density"));
    if(subst(sparse,x,a)%2!=1,error("parity"));
    for(b=a+1,20,
      if(g*U*(m-b)*(b-a)!=g*D*Up*(m-b)*(b-a),error("two-point width"));
    );
  );
);
print("Verified four fields, two target primes, 80 marked classes and 760 two-point scale identities");
}
