\\ Bounded reference using exact maximal-order arithmetic and integer factorization.
all_ideal_reference(coefficients, points, bound) = {
  my(norm_primes=primes([2,bound]), parts=vector(#points,k,List()));
  my(even=vector(#points,k,vector(#coefficients,i,1)), labels=List());
  for(i=1,#coefficients,
    my(P=Polrev(coefficients[i]), nf=nfinit(P), catalog=Map());
    for(k=1,#norm_primes,
      my(p=norm_primes[k], primes_above=idealprimedec(nf,p), roots=lift(polrootsmod(P,p)));
      mapput(catalog,p,primes_above);
      for(j=1,#primes_above,
        my(pr=primes_above[j], root=-1);
        for(r=1,#roots,
          if(idealval(nf,x-roots[r],pr)>0, root=roots[r]; break);
        );
        listput(labels,[i,p,j,root,pr.e,pr.f]);
      );
    );
    for(k=1,#points,
      my(a=points[k][1], b=points[k][2], element=a-b*x, value=nfeltnorm(nf,element));
      if(value!=sum(j=0,poldegree(P),polcoef(P,j)*a^j*b^(poldegree(P)-j)) || !value,
        error("reference norm disagrees"));
      my(factors=factor(abs(value)));
      for(j=1,matsize(factors)[1],
        my(p=factors[j,1], sumv=0);
        if(!isprime(p),error("reference factor is not prime"));
        my(primes_above=if(p<=bound,mapget(catalog,p),idealprimedec(nf,p)));
        for(l=1,#primes_above,
          my(pr=primes_above[l], exponent=idealval(nf,element,pr));
          sumv+=pr.f*exponent;
          if(exponent%2,
            if(p<=bound,listput(parts[k],[i,p,l]),even[k][i]=0);
          );
        );
        if(sumv!=factors[j,2],error("reference ideal exponents disagree with the norm"));
      );
    );
  );
  [Vec(labels),apply(Vec,parts),even];
};

all_ideal_weights(primes_above) = {
  sum(j=1,#primes_above,primes_above[j].e*primes_above[j].f/2^valuation(primes_above[j].e,2));
};

all_ideal_private_control(coefficients,a,b,bound) = {
  my(P=Polrev(coefficients), d=poldegree(P), base=nfinit(P), element=a-b*x);
  my(factors=factor(abs(nfeltnorm(base,element))), data=List());
  my(poly=(-b)^d*subst(P,x,(a-x^2)/b), split=!polisirreducible(poly), ext);
  if(!split,ext=nfinit(poly));
  for(j=1,matsize(factors)[1],
    my(p=factors[j,1]);
    if(p<=bound,next);
    my(down=idealprimedec(base,p), weights=2*all_ideal_weights(down));
    my(vals=vector(#down,k,idealval(base,element,down[k])));
    my(up_weight=if(split,weights,all_ideal_weights(idealprimedec(ext,p))));
    if((sum(k=1,#vals,vals[k]%2)==0)!=(up_weight==weights),
      error("quadratic ramification disagrees with private ideal parity"));
    listput(data,[p,select(e->e>0,vals),weights,up_weight]);
  );
  Vec(data);
};
