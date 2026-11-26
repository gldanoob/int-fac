\\ Bounded follow-up to monic_square_replay on the same five fixtures.
monic_power_unit(field, element) = {
  my(poly=lift(element));
  denominator(poly,1)==1 && abs(polresultant(field,poly))==1;
}

monic_unit_base_root(field, product) = {
  my(root=Mod(1,field));
  if(monic_power_unit(field,root^2/product), return(root));
  for(c=-8,8,
    root=Mod(x+c,field);
    if(monic_power_unit(field,root^2/product), return(root));
  );
  0;
}

monic_unit_reduce(element,m,n) = {
  my(poly=lift(element));
  if(denominator(poly,1)!=1, error("element outside the power order"));
  Mod(subst(poly,x,m),n);
}

monic_unit_search(n,m,fields,mark) = {
  my(a=mark[1], b=mark[2]);
  if(prod(i=1,2,subst(fields[i],x,m)==n)!=1, error("bad evaluation map"));
  my(products=vector(2,i,Mod(a-b*x,fields[i])));
  my(roots=vector(2,i,monic_unit_base_root(fields[i],products[i])));
  my(base_count=sum(i=1,2,roots[i]!=0), units=List(), tested=0);
  if(base_count!=2, return([base_count,0,0,[]]));
  for(i=1,2,for(j=1,2,
    my(unit=Mod((3-2*j)*a-b*x,fields[i]));
    if(monic_power_unit(fields[i],unit), listput(units,[i,unit,monic_unit_reduce(unit,m,n)]));
  ));
  if(!#units, return([base_count,0,0,[]]));
  my(base=vector(2,i,monic_unit_reduce(roots[i],m,n)));
  if(gcd(n,lift(base[1]*base[2]))!=1, error("nonunit base root residue"));
  for(h=0,8,forvec(exponents=vector(#units,j,[-h,h]),
    if(sum(j=1,#units,abs(exponents[j]))!=h, next);
    tested++;
    my(ratio=base[1]/base[2]*prod(j=1,#units,units[j][3]^((3-2*units[j][1])*exponents[j])));
    if(ratio^2!=1 || ratio==1 || ratio==-1, next);
    my(corrected=vector(2,i,roots[i]*prod(j=1,#units,if(units[j][1]==i,units[j][2]^exponents[j],1))));
    my(corrections=vector(2,i,corrected[i]^2/products[i]));
    if(prod(i=1,2,monic_power_unit(fields[i],corrections[i]))!=1, error("bad exact unit correction"));
    my(values=vector(2,i,monic_unit_reduce(corrected[i],m,n)), common=values[1]^2);
    if(monic_unit_reduce(corrections[1],m,n)!=monic_unit_reduce(corrections[2],m,n) ||
      common!=values[2]^2 || common!=monic_unit_reduce(corrections[1],m,n)*(a-b*m),
      error("bad modular square congruence"));
    my(divisor=gcd(lift(values[1]-values[2]),n));
    if(divisor<=1 || divisor>=n || n%divisor, error("bad gcd certificate"));
    return([base_count,#units,tested,[divisor,n/divisor,lift(values),lift(common),exponents]]);
  ));
  [base_count,#units,tested,[]];
}

monic_unit_holdout(n,m,coefficients) = {
  my(parity=monic_square_replay(n,m,coefficients), search=[]);
  my(singleton=parity[3]==1 && parity[4]==1 && #parity[5][1]==1);
  if(singleton && !#parity[6],
    search=monic_unit_search(n,m,apply(Polrev,coefficients),parity[5][1][1]));
  [n,parity[2],parity[3],parity[4],singleton,search,parity[6]];
}

monic_unit_fixture(n,m,coefficients) = {
  my(run=monic_unit_holdout(n,m,coefficients));
  my(result=[n,run[3],if(#run[6],run[6][4],[])]);
  my(expected=if(n==323,[323,1,[17,19,[72,4],16,[-2,1]]],[n,0,[]]));
  if(result!=expected, error("unit-correction fixture changed ",result));
  result;
}
