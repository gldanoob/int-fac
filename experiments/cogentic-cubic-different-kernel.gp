\\ Signed square kernels in a supplied maximal cubic order, without norm factoring.
cogentic_as_library=1;
read("cogentic-cubic-square-resolvent.gp");

read("cogentic-order-lattices.gp");

cubic_different_ideal_even(data,A) = {
  my(operators=data[2], R=mathnf(matconcat([A,data[3]])));
  my(bound=logint(matdet(A),2)+1, exponent=1);
  while(exponent<bound,
    my(next_R=mathnf(matconcat([A,order_product(operators,R,R)])));
    if(next_R==R,break);
    R=next_R;
    exponent*=2;
  );
  if(!issquare(matdet(R)),return(0));
  my(U=order_quotient(operators,A,R), invariants=matsnf(U));
  prod(i=1,#invariants,issquare(invariants[i]));
};

cubic_different_first(data,elements) = {
  my(unit=matid(3), ideals=vector(#elements), signs=vector(#elements), operators=data[2]);
  for(j=1,#elements,
    my(z=lift(elements[j]), coords=data[1]*vector(3,k,polcoef(z,k-1))~);
    my(h=denominator(coords));
    ideals[j]=mathnf(order_operator(operators,h^2*coords));
    signs[j]=norm(elements[j])<0;
  );
  my(atoms=Set(select(A->A!=unit,ideals)));
  while(1,
    my(changed=0);
    for(i=1,#atoms,for(j=i+1,#atoms,
      my(A=atoms[i],B=atoms[j],common=mathnf(matconcat([A,B])));
      if(common==unit,next);
      atoms=Set(select(lattice->lattice!=unit,concat(select(lattice->lattice!=A && lattice!=B,atoms),
        [common,order_quotient(operators,A,common),order_quotient(operators,B,common)])));
      changed=1;
      break(2);
    ));
    if(!changed,break);
  );
  my(bits=matrix(1+#atoms,#elements), bad=apply(A->!cubic_different_ideal_even(data,A),atoms));
  for(j=1,#elements,
    my(remaining=ideals[j]);
    bits[1,j]=signs[j];
    for(i=1,#atoms,
      my(A=atoms[i], inv=A^-1, odd=0);
      while(denominator(inv*remaining)==1,
        remaining=order_quotient(operators,remaining,A);
        odd=1-odd;
      );
      bits[i+1,j]=odd*bad[i];
    );
    if(remaining!=unit,error("gcd-free ideal atoms did not recover a column"));
  );
  my(vectors=lift(matker(Mod(bits,2))));
  vector(matsize(vectors)[2],j,sum(i=1,#elements,vectors[i,j]*2^(i-1)));
};

cubic_different_squares(P,basis,polynomials,{cap=-1}) = {
  if(type(cap)!="t_INT" || cap< -1,error("expected a nonnegative cap or -1 for unlimited"));
  my(elements=apply(z->Mod(z,P),polynomials));
  if(!prod(i=1,#elements,elements[i]!=0),error("expected nonzero cubic entries"));
  if(!#elements,return([1,[],0,0,0]));
  my(first=cubic_different_first(order_data(P,basis),elements));
  my(pivots=List(), answers=List(), tests=0);
  for(i=1,#first,
    my(matched=0);
    for(j=0,2^#pivots-1,
      if(tests==cap,return([0,Vec(answers),#pivots,tests,#first]));
      my(mask=first[i]);
      for(k=1,#pivots,if(bittest(j,k-1),mask=bitxor(mask,pivots[k])));
      my(product=Mod(prod(k=1,#elements,if(bittest(mask,k-1),elements[k],1)),P));
      my(root=cubic_resolvent_root(P,product));
      tests++;
      if(!root,next);
      listput(answers,[mask,root]);
      matched=1;
      break;
    );
    if(!matched,listput(pivots,first[i]));
  );
  [1,Vec(answers),#pivots,tests,#first];
};

cubic_different_check(P,basis,primes,polynomials) = {
  my(nf=nfinit(P), data=order_data(P,basis));
  my(C=matrix(3,3,i,j,polcoef(nf.zk[j],i-1)), map=data[1]*C, tested=0);
  if(denominator(map)!=1 || abs(matdet(map))!=1,error("fixture basis not maximal"));
  for(j=1,#primes,
    my(decomp=idealprimedec(nf,primes[j]), d=#decomp);
    for(code=0,4^d-1,
      my(exponents=digits(code+4^d,4)[2..d+1]);
      my(A=idealhnf(nf,1));
      for(k=1,d,A=idealmul(nf,A,idealpow(nf,decomp[k],exponents[k])));
      if(cubic_different_ideal_even(data,mathnf(map*A))!=prod(k=1,d,exponents[k]%2==0),
        error("wrong prime-ideal exponent check ",[primes[j],exponents]));
      tested++;
    );
  );
  my(result=cubic_different_squares(P,basis,polynomials), elements=apply(z->Mod(z,P),polynomials));
  my(k=#result[2], masks=vector(k,j,result[2][j][1]));
  if(!result[1] || k+result[3]!=result[5],error("full cubic kernel not exhausted"));
  my(span=Set(vector(2^k,j,
    my(word=0); for(l=1,k,if(bittest(j-1,l-1),word=bitxor(word,masks[l]))); word)));
  if(#span!=2^k,error("cubic kernel output not independent"));
  for(j=0,2^#elements-1,
    my(product=prod(l=1,#elements,if(bittest(j,l-1),elements[l],1)));
    if(nfeltissquare(nf,product)!=!!setsearch(span,j),error("wrong cubic square kernel"));
  );
  [nf.disc,nf.index,tested,2^#elements,k,result[4]];
};

cubic_different_replay() = {
  my(inputs=[-1,2,x,x-1,1-x,1+x,1+x+x^2,x/3,(x-1)^2,(x+1)^2]);
  print(cubic_different_check(x^3-5*x^2-8*x-12,[1,(x^2-5*x-6)/2,x-2],[2,3,5,7,31],inputs));
  print(cubic_different_check(x^3-3*x^2-6*x-12,[1,x-1,(x^2-3*x-4)/2],[2,3,5,7,73],inputs));
  print(cubic_different_check(x^3-28*x^2+54,[1,x,(x^2-x+3)/15],[2,3,5,7,11,157],inputs));
  if(cubic_different_squares(x^3-2,[1,x,x^2],[-1,x-1],0)!=[0,[],0,0,1],
    error("wrong square-query cap behavior"));
};

if(type(cogentic_different_as_library)!="t_INT",iferr(cubic_different_replay(),err,print(err);quit(1)));
