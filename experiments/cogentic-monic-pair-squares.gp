\\ Status 0 means nonsquare, 1 means a nonunit denominator, 2 includes a residue.
monic_square_root(n, m, nf, product) = {
  my(root);
  if(!nfeltissquare(nf,product,&root), return([0]));
  root = nfbasistoalg(nf,root);
  if(root^2 != product, error("incorrect field square root"));
  my(poly=lift(root), den=denominator(poly,1));
  if(gcd(den,n)!=1, return([1]));
  [2,lift(Mod(subst(den*poly,x,m),n)/den)];
}

monic_check_square_denominators() = {
  my(F=x^3-28*x^2+54, nf=nfinit(F), beta=Mod((x^2-x+3)/15,F));
  if(monic_square_root(895,29,nf,beta^2)!=[1], error("nonunit denominator passed"));
  my(result=monic_square_root(8629,35,nf,beta^2));
  if(result[1]!=2 || Mod(result[2],8629)^2!=(Mod(1193,8629)/15)^2,
    error("unit denominator failed"));
}

monic_square_replay(n,m,coefficients) = {
  my(fields=apply(Polrev,coefficients), orders=apply(nfinit,fields));
  my(discs=apply(poldisc,fields), primeset=primes([2,151]), marks=List(), rows=Map(), rowcount=0);
  my(excluded=discs[1]*discs[2]);
  monic_check_square_denominators();
  if(monic_square_root(n,m,orders[1],Mod(x,fields[1])^2)[1]!=2,error("square-root control failed"));
  for(a=-64,64,for(b=1,64,
    if(gcd(a,b)!=1 || gcd(a-b*m,n)!=1, next);
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
  if(!#marks, error("no simultaneous marks in square-search fixture ", n));
  my(M=matrix(rowcount,#marks));
  for(k=1,#marks,for(i=1,2,for(j=1,#marks[k][3][i],
    my(entry=marks[k][3][i][j]);
    M[mapget(rows,[i,entry[1],entry[3]]),k]=entry[2]%2;
  )));
  my(kernel=lift(matker(Mod(M,2))), dim=matsize(kernel)[2], tested=0, witness=[], certificate=[]);
  for(mask=1,min(2^dim-1,1023),
    my(weights=(kernel*vector(dim,i,bittest(mask,i-1))~)%2);
    my(support=select(k->weights[k],[1..#marks]));
    if(!#support || (M*weights)%2!=0, error("bad parity dependency"));
    my(products=vector(2,i,prod(j=1,#support,my(mark=marks[support[j]]); Mod(mark[1]-mark[2]*x,fields[i]))));
    my(common=prod(j=1,#support,my(mark=marks[support[j]]); Mod(mark[1]-m*mark[2],n)));
    my(points=vector(#support,j,marks[support[j]][1..2]));
    my(roots=matrix(2,2,j,i,monic_square_root(n,m,orders[i],(2*j-3)*products[i])));
    tested++;
    if(!#witness, witness=[points,vector(2,i,nfeltnorm(orders[i],products[i])),matrix(2,2,j,i,roots[j,i][1])]);
    for(j=1,2,
      if(roots[j,1][1]!=2 || roots[j,2][1]!=2, next);
      my(left=roots[j,1][2], right=roots[j,2][2], sign=2*j-3);
      if(Mod(left,n)^2!=sign*common || Mod(right,n)^2!=sign*common,error("bad modular square"));
      my(divisor=gcd(left-right,n));
      if(divisor==1 || divisor==n, next);
      certificate=[divisor,left,right,sign,points];
      break(2);
    );
  );
  if(n==323 && (dim!=1 || tested!=1 || witness!=[[[-1,2]],[-1,9],[0,0;0,0]]),
    error("lost the mixed-sign cubic dependency at 323"));
  [n,#marks,dim,tested,witness,certificate];
}
