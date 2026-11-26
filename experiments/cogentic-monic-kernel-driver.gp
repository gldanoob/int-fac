\\ Exact square root in a monic quotient using rational polynomial factorization.
kernel_root(P, product) = {
  my(q=lift(product), e=poldegree(P), norm, t);
  for(choice=0,binomial(2*e,2),
    t=choice;
    norm=polresultant(P,(y-t*x)^2-q,x);
    if(poldegree(norm)==2*e && gcd(norm,deriv(norm))==1, break);
  );
  if(poldegree(norm)!=2*e || gcd(norm,deriv(norm))!=1, error("no separating generator"));
  my(factors=factor(norm));
  if(matsize(factors)[1]==1, return(0));
  if(matsize(factors)[1]!=2 || poldegree(factors[1,1])!=e || poldegree(factors[2,1])!=e,
    error("invalid square algebra decomposition"));
  my(z=Mod(y,factors[1,1]), linear=gcd(P,(z-t*x)^2-q));
  if(poldegree(linear,x)!=1, error("square algebra generator recovery failed"));
  my(alpha=-polcoef(linear,0,x)/polcoef(linear,1,x));
  my(values=vector(e,j,lift(alpha^(j-1))), beta=lift(z-t*alpha));
  my(powers=matrix(e,e,i,j,polcoef(values[j],i-1,y)));
  my(root=Mod(Polrev(Vec(matsolve(powers,vector(e,i,polcoef(beta,i-1,y))~)),x),P));
  if(root^2!=product, error("invalid square root recovered"));
  root;
};

kernel_reduce(n,m,P,root) = {
  my(D=deriv(P), numerator=lift(D*root), divisor=subst(D,x,m));
  if(denominator(numerator,1)!=1 || gcd(divisor,n)!=1, error("invalid derivative-cleared evaluation"));
  Mod(subst(numerator,x,m),n)/divisor;
};

kernel_roots(n,m,fields,points,sign) = {
  my(result=vector(2));
  for(i=1,2,
    my(P=fields[i], product=sign*prod(j=1,#points,Mod(points[j][1]-points[j][2]*x,P)));
    my(root=kernel_root(P,product));
    if(root==0, return([]));
    result[i]=lift(kernel_reduce(n,m,P,root));
  );
  result;
};
