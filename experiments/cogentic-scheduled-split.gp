scheduled_root(nf, product) = {
  my(root);
  if(!nfeltissquare(nf,product,&root), return(0));
  root=nfbasistoalg(nf,root);
  if(root^2!=product, error("incorrect exact square root"));
  root;
}

scheduled_reduce(n,m,field,root) = {
  my(derivative=deriv(field), numerator=lift(Mod(derivative*lift(root),field)));
  if(denominator(numerator)!=1, error("derivative failed to clear a denominator"));
  Mod(subst(numerator,x,m),n)/subst(derivative,x,m);
}

scheduled_certificate(n,values,common) = {
  if(values[1]^2!=common || values[2]^2!=common, error("incorrect modular square"));
  my(divisor=gcd(lift(values[1]-values[2]),n));
  if(divisor==1 || divisor==n, return([]));
  [divisor,lift(values),lift(common)];
}

scheduled_units(n,m,fields,products,points,sign_roots,common) = {
  my(roots=vector(2,i,
    if(sign_roots[2,i]!=0, sign_roots[2,i],
      if(sign_roots[1,i]!=0, sign_roots[1,i], monic_unit_base_root(fields[i],products[i])))));
  if(!roots[1] || !roots[2], return([0,0,[]]));
  my(units=List(), tested=0);
  for(i=1,2,for(k=1,#points,for(j=1,2,
    my(unit=Mod((3-2*j)*points[k][1]-points[k][2]*x,fields[i]));
    if(monic_power_unit(fields[i],unit) && !sum(l=1,#units,units[l][1]==i && units[l][2]==unit),
      listput(units,[i,unit,monic_unit_reduce(unit,m,n)]));
    if(#units==4, break(3));
  )));
  if(!#units, return([1,0,[]]));
  my(base=vector(2,i,scheduled_reduce(n,m,fields[i],roots[i])));
  for(h=0,8,forvec(exponents=vector(#units,j,[-h,h]),
    if(sum(j=1,#units,abs(exponents[j]))!=h, next);
    if(tested==128, return([1,tested,[]]));
    tested++;
    my(ratio=base[1]/base[2]*prod(j=1,#units,units[j][3]^((3-2*units[j][1])*exponents[j])));
    if(ratio^2!=1 || ratio==1 || ratio==-1, next);
    my(corrected=vector(2,i,roots[i]*prod(j=1,#units,if(units[j][1]==i,units[j][2]^exponents[j],1))));
    my(corrections=vector(2,i,corrected[i]^2/products[i]));
    if(!prod(i=1,2,monic_power_unit(fields[i],corrections[i])), error("incorrect unit correction"));
    if((corrections[1]==1 && corrections[2]==1) || (corrections[1]==-1 && corrections[2]==-1), next);
    my(value=monic_unit_reduce(corrections[1],m,n));
    if(value!=monic_unit_reduce(corrections[2],m,n), error("unequal correction residues"));
    my(values=vector(2,i,scheduled_reduce(n,m,fields[i],corrected[i])));
    my(certificate=scheduled_certificate(n,values,common*value));
    if(!#certificate, error("unit word lost its proper gcd"));
    return([1,tested,concat(certificate,[exponents,Vec(units)])]);
  ));
  [1,tested,[]];
}

scheduled_split(n,degree,m,t,coefficients) = {
  my(fields=apply(Polrev,coefficients), orders=apply(nfinit,fields));
  my(excluded=prod(i=1,2,poldisc(fields[i])), primeset=primes([2,151]));
  my(marks=List(), rows=Map(), rowcount=0, direct_count=0, direct=[]);
  for(i=1,2,
    if(poldegree(fields[i])!=degree+i-1 || subst(fields[i],x,m)!=n ||
      gcd(subst(deriv(fields[i]),x,m),n)!=1, error("invalid repaired field"));
  );
  for(a=-64,64,for(b=1,64,
    if(gcd(a,b)!=1, next);
    my(divisor=gcd(a-b*m,n));
    if(divisor!=1,
      if(divisor!=n, direct_count++; if(!#direct, direct=[divisor,a,b]));
      next;
    );
    my(left=monic_norm_data(fields[1],a,b,excluded,primeset));
    my(right=monic_norm_data(fields[2],a,b,excluded,primeset));
    if(type(left)!="t_VEC" || type(right)!="t_VEC", next);
    monic_check_ideals(orders[1],a,b,left);
    monic_check_ideals(orders[2],a,b,right);
    my(entries=[left[2],right[2]]);
    for(i=1,2,for(j=1,#entries[i],
      my(entry=entries[i][j], key=[i,entry[1],entry[3]]);
      if(!mapisdefined(rows,key), rowcount++; mapput(rows,key,rowcount));
    ));
    listput(marks,[a,b,entries]);
  ));
  if(!#marks, return([n,degree,m,t,[direct_count,direct],0,0,0,[0,0,[]],[0,0,0,[]],0]));
  my(M=matrix(rowcount,#marks));
  for(k=1,#marks,for(i=1,2,for(j=1,#marks[k][3][i],
    my(entry=marks[k][3][i][j]);
    M[mapget(rows,[i,entry[1],entry[3]]),k]=entry[2]%2;
  )));
  my(kernel=if(rowcount,lift(matker(Mod(M,2))),matid(#marks)), dim=matsize(kernel)[2]);
  my(tested=min(255,2^dim-1), multi=0, square_count=0, square_splits=0, square=[]);
  my(unit_bases=0, unit_words=0, unit_splits=0, corrected=[]);
  for(mask=1,tested,
    my(weights=(kernel*vector(dim,i,bittest(mask,i-1))~)%2);
    my(support=select(k->weights[k],[1..#marks]));
    if(!#support || (rowcount && (M*weights)%2!=0), error("bad parity dependency"));
    if(#support>1, multi++);
    my(points=apply(k->marks[k][1..2],support));
    my(products=vector(2,i,prod(j=1,#points,Mod(points[j][1]-points[j][2]*x,fields[i]))));
    my(common=prod(j=1,#points,Mod(points[j][1]-m*points[j][2],n)));
    my(roots=matrix(2,2,j,i,scheduled_root(orders[i],(2*j-3)*products[i])));
    for(j=1,2,
      if(!roots[j,1] || !roots[j,2], next);
      square_count++;
      my(values=vector(2,i,scheduled_reduce(n,m,fields[i],roots[j,i])));
      my(certificate=scheduled_certificate(n,values,(2*j-3)*common));
      if(#certificate, square_splits++; if(!#square, square=concat(certificate,[2*j-3,points])));
    );
    my(unit=scheduled_units(n,m,fields,products,points,roots,common));
    unit_bases+=unit[1]; unit_words+=unit[2];
    if(#unit[3], unit_splits++; if(!#corrected, corrected=concat(unit[3],[points])));
  );
  [n,degree,m,t,[direct_count,direct],#marks,dim,tested,
    [square_count,square_splits,square],[unit_bases,unit_words,unit_splits,corrected],multi];
}
