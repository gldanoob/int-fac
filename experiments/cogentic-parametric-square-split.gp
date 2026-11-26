monic_parametric_square(u, v, c) = {
  my(n=2*u*v, w=u^2+2*v^2);
  if(u<1 || v<1 || c<1 || u^2-2*v^2!=-1 || c%2!=1 ||
    c%(n*w/2^valuation(n*w,2)), error("invalid Pell parameters"));
  my(m=1+c^2*n^2, input=m^2+2*c^2);
  my(base=sqrtint(input), carry);
  if(base%2==0, base--);
  carry=(input-base^2)/2;
  if(base!=m || carry!=c^2 || carry>=m || carry%2!=1, error("wrong manual carry"));

  my(f=x^2+2*carry, g=f+(x-m)*x^2);
  my(marks=[[2*c*n,1],[-2*c*n,1],[2*c^2*n^4-1,2*n^2]]);
  my(signed_product=-prod(i=1,#marks,marks[i][1]-marks[i][2]*x));
  my(l=2*n^2*(x+1-m)+1, roots=[w*x*(1+n^2*x),x*l], fields=[f,g]);
  for(i=1,#marks,
    my(a=marks[i][1], b=marks[i][2]);
    if(gcd(a,b)!=1 || gcd(a-b*m,input)!=1, error("inadmissible mark"));
  );
  for(i=1,2,
    my(field=fields[i], root=roots[i], norm_product=polresultant(field,signed_product));
    if(subst(field,x,m)!=input || polcoeff(field,0)%4!=2 ||
      sum(j=0,poldegree(field)-1,polcoeff(field,j)%2),
      error("invalid monic pair"));
    if((root^2-signed_product)%field || norm_product!=polresultant(field,root)^2,
      error("invalid polynomial or norm square"));
  );
  my(r=Mod(subst(roots[1],x,m),input), s=Mod(subst(roots[2],x,m),input));
  my(p=gcd(lift(r-s),input), q=gcd(lift(r+s),input));
  if(r^2!=s^2 || s^2!=Mod(subst(signed_product,x,m),input) ||
    p<=1 || q<=1 || p*q!=input || gcd(p,q)!=1 ||
    p!=m+4*c^2*v^2 || q!=m-2*c^2*u^2, error("invalid modular split"));
  [input,p,q]
}

iferr({
  if(monic_parametric_square(1,1,3)!=[1387,73,19], error("first split changed"));
  forstep(c=3,63,6, monic_parametric_square(1,1,c));
  monic_parametric_square(7,5,3465);
  print("Verified 11 one-parameter splits and a second Pell solution");
}, err, print(err); quit(1));
