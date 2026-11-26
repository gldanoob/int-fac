\\ Lattices are columns, in the coordinates of the supplied order basis.
order_operator(operators,v) = sum(i=1,#operators,v[i]*operators[i]);

order_quotient(operators,A,B) = {
  my(inv=A^-1, constraints=matconcat(vector(#operators,j,(inv*order_operator(operators,B[,j]))~)));
  my(h=denominator(constraints), dual=mathnf(h*constraints)/h, result=(dual^-1)~);
  if(denominator(result)!=1,error("expected an integral ideal quotient"));
  mathnf(result);
};

order_data(P,basis) = {
  my(d=poldegree(P));
  if(d<1 || #basis!=d || pollead(P)!=1 || denominator(P)!=1 || !polisirreducible(P),
    error("expected a monic irreducible integral polynomial and a full basis"));
  basis=apply(z->lift(Mod(z,P)),basis);
  my(change=matrix(d,d,i,j,polcoef(basis[j],i-1)), inv=change^-1);
  my(operators=vector(d,j,
    my(images=apply(z->lift(Mod(z*basis[j],P)),basis));
    inv*matrix(d,d,i,k,polcoef(images[k],i-1))));
  if(denominator(inv[,1])!=1 || !prod(i=1,d,denominator(operators[i])==1),
    error("basis did not define a unital order"));
  my(traces=matrix(d,d,i,j,trace(operators[i]*operators[j])));
  my(different=order_quotient(operators,matid(d),traces^-1));
  [inv,operators,different];
};

order_product(operators,A,B) = {
  mathnf(matconcat(vector(#operators,j,order_operator(operators,A[,j])*B)));
};

order_square_data(P,basis) = {
  my(data=order_data(P,basis), operators=data[2], different=data[3]);
  my(d=#basis, unit=matid(d), tame=matsnf(different)[1], small=unit);
  my(one=data[1][,1]);
  forprime(p=2,d,
    if(tame%p==0,
      tame/=p^valuation(tame,p);
      my(bound=p);
      while(bound<d,bound*=p);
      my(images=matconcat(vector(d,j,(Mod(1,p)*operators[j])^bound*one)));
      my(nilradical=mathnf(matconcat([p*unit,lift(matker(images))])));
      small=order_product(operators,small,nilradical);
    );
  );
  my(tame_part=mathnf(matconcat([different,tame*unit])));
  my(radical=order_product(operators,small,order_quotient(operators,tame*unit,tame_part)));
  concat(data,[radical]);
};

order_ideal_square_root(data,A) = {
  my(operators=data[2], radical=data[4], d=#operators, unit=matid(d));
  if(matsize(A)!=[d,d] || denominator(A)!=1 || matdet(A)==0,
    error("expected a full integral ideal lattice"));
  A=mathnf(A);
  my(inv=A^-1);
  if(!prod(j=1,d,denominator(inv*operators[j]*A)==1),error("input is not an order ideal"));
  my(rest=A, half=unit);
  while(1,
    my(first=mathnf(matconcat([rest,radical])));
    if(first==unit,break);
    rest=order_quotient(operators,rest,first);
    my(second=mathnf(matconcat([rest,radical])));
    if(second!=first,return(0));
    half=order_product(operators,half,first);
    rest=order_quotient(operators,rest,second);
  );
  my(smith=matsnf(rest,1), diagonal=smith[3], roots=vector(d));
  for(i=1,d,
    my(root);
    if(!issquare(diagonal[i,i],&root),return(0));
    roots[i]=root;
  );
  my(unramified=mathnf(smith[1]^-1*matdiagonal(roots)));
  my(result=order_product(operators,half,unramified));
  if(order_product(operators,result,result)!=A,error("ideal square-root reconstruction failed"));
  result;
};
