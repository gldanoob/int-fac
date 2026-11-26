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

\\ Build the two quadratic power orders at an arbitrary eligible input and parameter.
unit_parameter_chart(n,t) = {
  if(n<3 || n%2==0,error("expected odd N >= 3"));
  my(pieces=[t,t-1,t+1,t^2+1],d);
  for(i=1,#pieces,d=gcd(pieces[i],n);if(d>1 && d<n,return([d,n/d])));
  if(gcd(prod(i=1,#pieces,pieces[i]),n)!=1,return([]));
  my(v=Mod(t,n), a=v*(v-1)/(v+1), b=a/v^2);
  my(m=lift(-(v^2+1)^2/(4*v*(v^2-1))), d1=(a+1)/2, d2=(b-1)/2);
  my(l=2*n+lift(m+d2), k=l+1+lift(Mod(m,n)+d1-l-1));
  my(f=x^2+x-k^2,g=x^2-x-l^2,alpha=Mod(x,f),beta=Mod(x,g));
  my(uf=2*k-1-2*alpha,vg=2*l+1-2*beta);
  if(!(l<k && k<2*l) || subst(f,x,m)%n || subst(g,x,m)%n,error("parametric orders"));
  if(norm(uf)!=-1 || norm(vg)!=-1 || (k-alpha)^2!=-alpha*uf || (l-beta)^2!=-beta*vg,error("units"));
  if(Mod(k-m,n)/Mod(l-m,n)!=-v || Mod(2*k-1-2*m,n)!=a || Mod(2*l+1-2*m,n)!=b,error("chart residues"));
  [m,k,l,lift(a),lift(b)]
};
unit_parameter_match(n,t,i,j) = {
  my(chart=unit_parameter_chart(n,t));
  if(#chart<5,return(chart));
  my(a=Mod(chart[4],n),b=Mod(chart[5],n),r=(a+1)/2*a^i,s=(b-1)/2*b^j);
  if(r^2!=s^2,return([]));
  my(d=gcd(lift(r-s),n));
  if(d==1 || d==n,[],[d,n/d]);
};
{
  my(count=0);
  forstep(n=3,255,2,for(t=2,9,if(#unit_parameter_chart(n,t)==5,count++)));
  if(unit_parameter_match(341,2,2,2)!=[11,31],error("parameter split"));
  if(unit_parameter_match(341,2,0,0)!=[] || unit_parameter_match(35,2,2,2)!=[5,7],error("controls"));
  print(count," eligible charts checked; the fixed t=2 unit comparison splits 341")
}

\\ Test the compact equal-power certificate on the public repeated-squaring list.
unit_chart_odd_exponent(n,e) = {
  if(n<3 || n%2==0 || e<1 || e%2==0,error("expected odd N and a positive odd exponent"));
  my(bits=logint(n,2)+1, i=(e-1)/2);
  for(a=2,min(n-1,3*bits^2),
    my(d=gcd(a,n));
    if(1<d && d<n,return(["base-gcd",a,d,n/d]));
    my(t=Mod(a,n));
    for(j=0,bits-1,
      my(v=lift(t),g);
      if(v==1 || v==n-1,break);
      foreach([v-1,v+1,v^2+1],z,g=gcd(z,n);if(1<g && g<n,return(["parameter-gcd",a,j,g,n/g])));
      if(gcd(v^2+1,n)==1,
        my(s=t^e);
        if(s^2==1 && s!=1 && s!=-1,
          my(parts=unit_parameter_match(n,v,i,i));
          if(#parts!=2,error("unit certificate mismatch"));
          return(["unit-powers",a,j,i,parts[1],parts[2]])
        )
      );
      t=t^2
    )
  );
  []
};
{
  my(n=1000036000099,e=15625531251,res=unit_chart_odd_exponent(n,e));
  if(res[1]!="unit-powers" || res[2]!=2 || res[3]!=2 || res[5]*res[6]!=n,error("uniform chart library"));
  if(unit_chart_odd_exponent(101,25)!=[],error("unexpected prime split"));
  print("Equal unit powers split ",n," using a public chart at t=16 and the supplied odd exponent")
}
