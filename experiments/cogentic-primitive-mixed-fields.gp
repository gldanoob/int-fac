/* Build the four fields and verify their square-class and sign certificates. */
check(condition, label) = {
  if(!condition, print("Failed: ", label); quit(1));
};

primitive_mixed_fields(degree, v, marks, roots, auxiliary) = {
  my(m=2*v^2, n=m^2+1, cuts, modulus=2, ratio=Mod(1,n), qvalues, q, h0, h, f);
  cuts=vector(4,i,-polcoef(marks[i],0)/polcoef(marks[i],1));
  for(i=1,4, for(j=1,2, modulus*=auxiliary[i][j][2]^2));
  check(gcd(modulus,n)==1 && gcd(m-3,n)==1, "inversion mod N");
  for(i=1,4,
    my(next=(i%4)+1, degree_i=degree+i-1, edge=marks[i]*marks[next],
       coeffs, p, j, t, values, interpolant, desired, radix);
    check(gcd(polcoef(marks[i],0),polcoef(marks[i],1))==1
          && Mod(roots[i]^2-marks[i],x^2+1)==0, "primitive Gaussian mark");
    check(gcd(lift(Mod(subst(marks[i],x,m),n)),n)==1, "mark unit");
    qvalues=Mod(subst(roots[i]*roots[next],x,m),n);
    if(i==1, qvalues*=Mod(1+m,n)/Mod(2*v,n));

    coeffs=vector(degree_i-1,k,Mod(1,2));
    for(k=1,2,
      [j,p,t]=auxiliary[i][k];
      check(isprime(p) && t^2%p==lift(Mod(subst(edge,x,cuts[j]),p)), "auxiliary square");
      if(Mod(t^2-subst(edge,x,cuts[j]),p^2)==0,t+=p);
      values=vector(4,l,if(l==j,t,if(l==i || l==next,1,0)));
      for(l=1,4,
        values[l]=Mod(values[l],p^2)/Mod(cuts[l]-3,p^2)-Mod(cuts[l],p^2)^(degree_i-1)
      );
      interpolant=polinterpolate(vector(4,l,Mod(cuts[l],p^2)),values,x);
      for(l=1,degree_i-1,
        coeffs[l]=chinese(coeffs[l],Mod(lift(polcoef(interpolant,l-1)),p^2))
      );
    );

    h0=x^(degree_i-1)+sum(l=1,degree_i-1,lift(coeffs[l])*x^(l-1));
    p=2*prod(k=1,2,auxiliary[i][k][2]^2);
    desired=lift((qvalues/Mod(m-3,n)-subst(h0,x,m))/Mod(p,n));
    radix=(desired%m)+((desired\m)%m)*x+(desired\m^2)*x^2;
    h=h0+p*radix;
    q=(x-3)*h;
    f=q^2-edge;
    desired=lift((1-Mod(subst(deriv(f),x,m),n))/Mod(4*m*(m-3)*p*subst(q,x,m),n));
    radix=if(desired==m^2,-1,(desired%m)+(desired\m)*x);
    q+=(x-3)*p*(x^2+1)*radix;
    f=q^2-edge;
    check(poldegree(f)==2*degree_i && Mod(f-x^(2*degree_i),2)==0
          && subst(f,x,0)%4==2, "Eisenstein");
    check(Mod(subst(f,x,m),n)==0 && subst(f,x,3)<0, "selected and real branches");
    check(Mod(subst(deriv(f),x,m),n)==1, "simple branch");
    for(k=1,2,
      j=auxiliary[i][k][1]; p=auxiliary[i][k][2];
      for(l=1,4,
        check(valuation(subst(f,x,cuts[l]),p)==(j==l), "isolated norm valuation")
      );
    );
    ratio*=Mod(subst(q,x,m),n)/Mod(subst(marks[i],x,m),n);
  );
  check(ratio^2==1 && gcd(lift(ratio)-1,n)==m+1-2*v, "productive sign");
  print("Verified degree parameters ", degree, "–", degree+3,
        " at a ", logint(n,2)+1, "-bit input");
};

marks=[3-4*x,-3-4*x,15-8*x,5-12*x];
roots=[2-x,1-2*x,4-x,3-2*x];
auxiliary=[[[3,37,1],[4,19,6]],[[1,11,1],[4,23,9]],[[1,29,14],[2,43,6]],[[2,41,17],[3,59,8]]];
v=5*13*17*prod(i=1,4,prod(k=1,2,auxiliary[i][k][2]));
forstep(degree=5,13,4,primitive_mixed_fields(degree,v,marks,roots,auxiliary));
