/* Half-ideal class witnesses and a new unit-corrected split. */
read("cogentic-order-lattices.gp");
read("cogentic-monic-kernel-driver.gp");

half_check(ok,label)=if(!ok,error(label));

half_residual(data,I,v) = {
  my(ops=data[2], A=mathnf(order_operator(ops,v)), J=order_quotient(ops,A,I));
  half_check(order_product(ops,I,J)==A,"bad residual quotient");
  J;
};

half_class_rows(A,relations) = {
  my(H=mathnf(if(#relations,matconcat([relations,2*A]),2*A)));
  if(!#H,return(matrix(0,matsize(A)[2])));
  my(Y=matinverseimage(H,2*A));
  half_check(denominator(Y)==1 && H*Y==2*A,"missing doubled exponents");
  Mod(1,2)*Y;
};

half_generators(data,I,bound) = {
  my(ops=data[2], found=List());
  forvec(c=vector(#ops,i,[-bound,bound]),
    my(j=1);
    while(j<=#c && c[j]==0,j++);
    if(j<=#c && c[j]>0,
      my(v=I*c~);
      if(mathnf(order_operator(ops,v))==I,listput(found,v));
    );
  );
  Vec(found);
};

half_imag_minimum(data,I) = {
  my(ops=data[2], index=abs(matdet(I)), v=I[,1], w=I[,2]);
  while(1,
    my(a=matdet(order_operator(ops,v))/index,
       c=matdet(order_operator(ops,w))/index,
       b=matdet(order_operator(ops,v+w))/index-a-c);
    half_check(a>0 && denominator([a,b,c])==1,"expected an integral positive norm form");
    w-=floor((b+a)/(2*a))*v;
    if(matdet(order_operator(ops,w))/index>=a,return([a,v]));
    [v,w]=[w,-v];
  );
};

half_class_fixture() = {
  my(P=x^2+5,data=order_square_data(P,[1,x]),ops=data[2]);
  my(B=[Mod(2+x,P),Mod(2,P)]);
  my(I=vector(2,i,
    order_ideal_square_root(data,order_operator(ops,vector(2,j,polcoef(lift(B[i]),j-1))~))));
  half_check(matdet(I[1])==3 && matdet(I[2])==2,"wrong nonprincipal half ideals");
  my(minima=vector(2,i,half_imag_minimum(data,I[i])));
  half_check(minima[1][1]==2 && minima[2][1]==2,"nonprincipal norm minima failed");
  my(J1=half_residual(data,I[1],minima[1][2]), J2=half_residual(data,I[2],minima[2][2]));
  half_check(J1==J2 && J1==I[2],"expected equal residual ideals");
  half_check(half_class_rows(Mat([1,1]),[])==Mod(1,2)*Mat([1,1]),
             "wrong binary row for the shared residual");
  my(generator=Mod(Polrev(Vec(minima[1][2]))*Polrev(Vec(minima[2][2])),P)/B[2]);
  my(coeffs=vector(2,i,polcoef(lift(generator),i-1))~);
  half_check(order_product(ops,I[1],I[2])==mathnf(order_operator(ops,coeffs)),
             "missing exact principal relation");
  half_check(generator^2==-B[1]*B[2] && B[1]*B[2]/generator^2==-1,
             "wrong unit residual");
  print("Q(sqrt(-5)): two nonprincipal halves cancel, with residual unit -1");
};

half_four_torsion_fixture() = {
  my(P=x^2+14,data=order_square_data(P,[1,x]),ops=data[2]);
  my(p=mathnf(matconcat([3*matid(2),order_operator(ops,[1,1]~)])), v=[5,2]~);
  my(I=order_ideal_square_root(data,order_operator(ops,v)));
  half_check(matdet(p)==3 && I==order_product(ops,p,p) && half_residual(data,I,v)==I,
             "wrong halves for the explicit fourth ideal power");
  half_check(half_imag_minimum(data,I)[1]>1,"squared prime ideal should be nonprincipal");
  half_check(half_class_rows(Mat(2),[])==Mod(1,2)*Mat(1),
             "ordinary atom parity would miss the four-torsion obstruction");
  print("Q(sqrt(-14)): the doubled atom has a nonzero class row");
};

half_unit_options(P,data,m,n,mark,bound) = {
  my(d=poldegree(P), ops=data[2], value=Mod(mark,P));
  my(v=vector(d,i,polcoef(lift(value),i-1))~);
  my(I=order_ideal_square_root(data,order_operator(ops,v)));
  half_check(I!=0,"expected integral ideal square");
  my(generators=half_generators(data,I,bound), roots=vector(#generators,i,
    Mod(Polrev(Vec(generators[i])),P)));
  vector(#roots,i,
    my(r=roots[i],u=r^2/value,c=vector(d,j,polcoef(lift(u),j-1))~);
    half_check(denominator(c)==1 && abs(matdet(order_operator(ops,c)))==1,
               "correction was not a unit");
    [r,u,kernel_reduce(n,m,P,r),kernel_reduce(n,m,P,u)]
  );
};

half_split_fixture() = {
  my(n=371,m=20,fields=[x^2+x-49,x^2-x-9], options);
  options=vector(2,i,
    my(P=fields[i],data=order_square_data(P,[1,x]));
    half_check(isprime(poldisc(P)) && subst(P,x,m)==n && gcd(subst(deriv(P),x,m),n)==1,
               "bad maximal basis or modular branch");
    half_check(polresultant(P,-x)<0,"ordinary signed word should fail the norm test");
    half_unit_options(P,data,m,n,-x,1)
  );
  for(h=0,4,for(i=1,#options[1],for(j=1,#options[2],
    my(a=options[1][i],b=options[2][j]);
    for(e=-h,h,for(f=-h,h,
      if(abs(e)+abs(f)!=h,next);
      my(A=a[3]*a[4]^e,B=b[3]*b[4]^f);
      if(A^2!=B^2,next);
      my(divisor=gcd(lift(A-B),n));
      if(divisor<=1 || divisor>=n,next);
      my(r=a[1]*a[2]^e,s=b[1]*b[2]^f);
      half_check(r^2==-Mod(x,fields[1])*a[2]^(1+2*e)
                 && s^2==-Mod(x,fields[2])*b[2]^(1+2*f)
                 && kernel_reduce(n,m,fields[1],r)==A && kernel_reduce(n,m,fields[2],s)==B,
                 "square or reduction failed");
      half_check(n%divisor==0 && n/divisor!=1,"invalid gcd");
      print([n,vector(2,k,#options[k]),[lift(a[1]),lift(b[1])],[e,f],
             [lift(A),lift(B)],divisor,n/divisor]);
      return(divisor);
    ));
  )));
  error("no productive unit word in the declared box");
};

iferr(half_class_fixture();half_four_torsion_fixture();half_split_fixture(),err,print(err);quit(1));
