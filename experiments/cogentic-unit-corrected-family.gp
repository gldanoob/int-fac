\\ Recognize the degree-six family and recompute its corrected square certificates.
unit_family_split(n) = {
  my(w=sqrtnint(4*n,6), u, h, j, m, k, l, f, g, a, b, uf, ug, r, s);
  for(v=max(w,3),w+1,
    if(v%2 && (v^6-v^4+4*v^3-v^2+1)==4*n, u=v;break)
  );
  if(!u,return([]));
  h=(u-1)/2; j=(u^3+1)/2; m=(n-h^2)/u; k=m+j; l=m+h;
  f=x^2+x-k^2; g=x^2-x-l^2;
  a=Mod(x,f); b=Mod(x,g);
  uf=2*k-1-2*a; ug=2*l+1-2*b;
  if(denominator(m)!=1 || subst(f,x,m)!=-(1+u^2)*n || subst(g,x,m)!=-n,error("field map"));
  if(norm(-a)!=-k^2 || norm(-b)!=-l^2 || norm(uf)!=-1 || norm(ug)!=-1,error("norm"));
  if((k-a)^2!=-a*uf || ((l-b)*ug)^2!=-b*ug^3,error("corrected field square"));
  r=lift(Mod(subst(lift(k-a),x,m),n));
  s=lift(Mod(subst(lift((l-b)*ug),x,m),n));
  if((r^2-s^2)%n || gcd(r*s,n)!=1,error("modular roots"));
  my(d=gcd(r-s,n), e=gcd(r+s,n));
  if(d<=1 || e<=1 || d*e!=n || gcd(d,e)!=1,error("coprime factors"));
  [u,d,e]
};
{
  forstep(u=3,501,2,
    my(a=(u^3-u^2+u+1)/2,b=(u^3+u^2-u+1)/2,n=a*b);
    if(unit_family_split(n)!=[u,a,b] || unit_family_split(n+1)!=[],error("recognition"))
  );
  my(u=2^512+1,a=(u^3-u^2+u+1)/2,b=(u^3+u^2-u+1)/2);
  if(unit_family_split(a*b)!=[u,a,b],error("large input"));
  print("250 odd parameters, 250 neighboring integers, and one ", logint(a*b,2)+1, "-bit input verified")
}
