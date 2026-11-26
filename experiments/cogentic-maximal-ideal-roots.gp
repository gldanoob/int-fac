\\ Independent ideal decompositions are used only to make and verify the fixtures.
read("cogentic-order-lattices.gp");

check_ideal_roots(P,primes) = {
  my(nf=nfinit(P), d=poldegree(P), basis=nf.zk, data=order_square_data(P,basis));
  my(tested=0, positive=0, unit=matid(d));
  for(j=1,#primes,
    my(p=primes[j], parts=idealprimedec(nf,p), n=#parts, count=min(4^n,128));
    for(code=0,count-1,
      my(exps=vector(n,k,(code\4^(k-1))%4));
      if(count<4^n,exps=vector(n,k,(code*(2*k+1)+code\(2*k))%4));
      my(A=unit, expected=unit, even=1);
      for(k=1,n,
        A=idealmul(nf,A,idealpow(nf,parts[k],exps[k]));
        expected=idealmul(nf,expected,idealpow(nf,parts[k],exps[k]\2));
        if(exps[k]%2,even=0);
      );
      my(got=order_ideal_square_root(data,A));
      if(got!=if(even,expected,0),error("ideal root mismatch ",[P,p,exps]));
      positive+=even;tested++;
    );
  );
  print([d,nf.disc,tested,positive]);
  tested;
};

check_large_tame_radical() = {
  my(p=2^61-1,q=2^89-1,D=p*q,P=x^2-x+(1-D)/4);
  my(data=order_square_data(P,[1,x]),ops=data[2],unit=matid(2));
  my(theta=order_operator(ops,[-1,2]~));
  my(Jp=mathnf(matconcat([p*unit,theta])),Jq=mathnf(matconcat([q*unit,theta])));
  if(matsnf(data[3])[1]!=D || data[4]!=order_product(ops,Jp,Jq),error("wrong tame radical"));
  my(root=order_product(ops,Jp,q*unit),A=order_product(ops,root,root));
  if(order_ideal_square_root(data,A)!=root || order_ideal_square_root(data,order_product(ops,A,Jq))!=0,
    error("wrong mixed ideal root"));
  print("150-bit composite tame support and unequal ramified exponents verified");
};

maximal_ideal_root_replay() = {
  my(tested=0);
  for(i=1,5,
    my(P=[x^2-5,x^3-3*x^2-6*x-12,x^4-32*x^2+36,x^5-2,x^6-2][i]);
    tested+=check_ideal_roots(P,[2,3,5,7,11,13,17,31]);
  );
  check_large_tame_radical();
  print(tested," ideal exponent arrays compared with PARI");
};

iferr(maximal_ideal_root_replay(),err,print(err);quit(1));
