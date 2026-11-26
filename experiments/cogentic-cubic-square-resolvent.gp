\\ An exact quartic square test and a factor-free ideal kernel in Q(cuberoot(2)).
cubic_resolvent_root(P, value) = {
  my(plain=lift(value), root, t);
  if(poldegree(plain)<=0, return(if(issquare(plain,&root),Mod(root,P),0)));
  my(M=charpoly(value,y), s1=-polcoef(M,2), s2=polcoef(M,1));
  if(!issquare(-polcoef(M,0),&t),return(0));
  my(R=y^4-2*s1*y^2-8*t*y+s1^2-4*s2, F=factor(R));
  for(j=1,matsize(F)[1],
    my(linear=F[j,1]);
    if(poldegree(linear)!=1,next);
    my(w=-polcoef(linear,0)/polcoef(linear,1));
    root=2*(w*value+t)/(w^2-s1+2*value);
    if(root^2!=value,error("bad resolvent root"));
    return(root);
  );
  0;
};

pure_cubic_matrix(v) = {
  my(a=v[1],b=v[2],c=v[3]);
  [a,2*c,2*b; b,a,2*c; c,b,a];
};

pure_cubic_quotient(A,B) = {
  my(inv=A^-1, constraints=matconcat(vector(3,j,(inv*pure_cubic_matrix(B[,j]))~)));
  my(h=denominator(constraints), dual=mathnf(h*constraints)/h, result=(dual^-1)~);
  if(denominator(result)!=1,error("expected integral ideal quotient"));
  mathnf(result);
};

pure_cubic_ideal_even(A) = {
  my(area=matdet(A));
  if(valuation(area,2)%2 || valuation(area,3)%2,return(0));
  my(invariants=matsnf(A));
  for(j=1,#invariants,
    my(q=invariants[j]);
    if(!issquare(q/(2^valuation(q,2)*3^valuation(q,3))),return(0));
  );
  1;
};

pure_cubic_ideal_kernel(elements) = {
  my(unit=matid(3), ideals=vector(#elements), signs=vector(#elements));
  for(j=1,#elements,
    my(z=lift(elements[j]), h=denominator(z,1));
    ideals[j]=mathnf(pure_cubic_matrix(vector(3,k,polcoef(h^2*z,k-1))~));
    signs[j]=norm(elements[j])<0;
  );
  my(atoms=Set(select(H->H!=unit,ideals)));
  while(1,
    my(changed=0);
    for(i=1,#atoms,for(j=i+1,#atoms,
      my(A=atoms[i],B=atoms[j],C=mathnf(matconcat([A,B])));
      if(C==unit,next);
      atoms=Set(select(H->H!=unit,concat(select(H->H!=A && H!=B,atoms),
        [C,pure_cubic_quotient(A,C),pure_cubic_quotient(B,C)])));
      changed=1;
      break(2);
    ));
    if(!changed,break);
  );
  my(bits=matrix(1+#atoms,#elements), bad=apply(A->!pure_cubic_ideal_even(A),atoms));
  for(j=1,#elements,
    my(remaining=ideals[j]);
    bits[1,j]=signs[j];
    for(i=1,#atoms,
      my(A=atoms[i], inv=A^-1, odd=0);
      while(denominator(inv*remaining)==1,
        remaining=pure_cubic_quotient(remaining,A);
        odd=1-odd;
      );
      bits[i+1,j]=odd*bad[i];
    );
    if(remaining!=unit,error("gcd-free ideal atoms did not recover a column"));
  );
  matker(Mod(bits,2));
};

pure_cubic_product(elements, bits) = {
  prod(j=1,#elements,if(bits[j],elements[j],1));
};

pure_cubic_square_kernel(polynomials) = {
  my(P=x^3-2, unit=Mod(x-1,P), elements=apply(z->Mod(z,P),polynomials));
  if(!#elements || !prod(j=1,#elements,elements[j]!=0),error("expected nonempty list of nonzero elements"));
  my(first=pure_cubic_ideal_kernel(elements), m=matsize(first)[2]);
  if(!m,return([first,[]]));
  my(last=matrix(1,m));
  for(j=1,m,
    my(product=Mod(pure_cubic_product(elements,lift(first[,j])),P));
    if(!cubic_resolvent_root(P, product),
      if(!cubic_resolvent_root(P,product*unit),error("norm-one unit class did not exhaust the obstruction"));
      last[1,j]=1;
    );
  );
  my(basis=lift(first*matker(Mod(last,2))));
  my(roots=vector(matsize(basis)[2],j,
    cubic_resolvent_root(P,Mod(pure_cubic_product(elements,basis[,j]),P))));
  if(!prod(j=1,#roots,roots[j]!=0),error("square basis lost a root"));
  [basis,roots];
};

cubic_resolvent_replay() = {
  my(P=x^3-2, cyclic=x^3-3*x+1);
  if(cubic_resolvent_root(P,Mod(x-1,P)) || cubic_resolvent_root(cyclic,Mod(-x,cyclic)),
    error("accepted a nonsquare norm-one unit"));
  if(polgalois(x^4+6*x^2-8*x-3)[1]!=24 || polgalois(x^4-8*x+12)[1]!=12,
    error("incorrect quartic Galois group"));
  my(nf=nfinit(P), tested=0);
  for(s=1,3,
    my(inputs=[[-1,2,x,x-1,1-x,1+x,x^2+x+1,1+x^2,x/3,(x-1)^2,(x+1)^2],
      [1,-1,x-5,x-11,13,19/25,(x^2-x+1)/11,(1+x)^2/7,(x-1)^3,(x-1)^4],
      [2+x,2-x,3+x^2,3-x^2,7/11,7/13,11/13,-7/11,(-3+x+x^2)^2]][s]);
    my(result=pure_cubic_square_kernel(inputs), basis=result[1], k=matsize(basis)[2]);
    my(elements=apply(z->Mod(z,P),inputs));
    my(span=Set(vector(2^k,idx,
      my(bits=vector(k,j,bittest(idx-1,j-1))~, original=(basis*bits)%2);
      sum(j=1,#inputs,original[j]*2^(j-1)))));
    for(mask=0,2^#inputs-1,
      my(bits=vector(#inputs,j,bittest(mask,j-1)));
      if(nfeltissquare(nf,pure_cubic_product(elements,bits))!=!!setsearch(span,mask),
        error("wrong pure cubic square mask"));
      tested++;
    );
    print([s,#inputs,k]);
  );
  print(["verified square masks",tested]);
};

if(type(cogentic_as_library)!="t_INT",iferr(cubic_resolvent_replay(),err,print(err);quit(1)));
