{
norm_markers(nf,Y,want) =
  my(k=poldegree(nf.pol), markers=List());
  forprime(ell=33,Y,
    my(primes=idealprimedec(nf,ell));
    if(#primes!=k,next);
    my(ideal=idealhnf(nf,primes[1]), coeffs=(ideal*qflll(ideal))[,1]);
    my(a=nfbasistoalg(nf,coeffs), na=abs(nfeltnorm(nf,a)));
    if(na%ell!=0,error("marker is not in the prime ideal"));
    if(na/ell>32,next);
    listput(markers,[ell,a,na/ell]);
    if(#markers==want,return(Vec(markers)))
  );
  error("not enough norm markers", [nf.pol,Y,want])
}
{
check_products(nf,markers) =
  my(products=List(), maxcoeff=0);
  for(i=1,#markers-2,for(j=i+1,#markers-1,for(l=j+1,#markers,
    my(a=markers[i][2]*markers[j][2]*markers[l][2]);
    my(na=abs(nfeltnorm(nf,a)), expected=prod(h=1,3,my(m=[i,j,l][h]);markers[m][1]*markers[m][3]));
    if(na!=expected,error("norm product", [nf.pol,a,expected,na]));
    maxcoeff=max(maxcoeff,vecmax(abs(nfalgtobasis(nf,a))));
    listput(products,a)
  )));
  if(#Set(Vec(products))!=binomial(#markers,3),error("product collision"));
  [#products,maxcoeff]
}
{
subgroup_index(bid,logs,exponent) =
  matdet(mathnf(concat(matdiagonal(bid.cyc),exponent*logs)))
}
{
check_smooth_fixture(f,wanted_types,wanted_nonprincipal) =
  my(nf=nfinit(f), markers=norm_markers(nf,2500,8), types=Map(), good=0, bad=0);
  my(products=check_products(nf,markers));
  if(wanted_nonprincipal && vecmax(vector(#markers,j,markers[j][3]))==1,
    error("fixture should include nonprincipal norms"));
  forprime(t=2510,2760,
    my(type=vecsort(apply(pr->pr.f,idealprimedec(nf,t))));
    my(bid=idealstar(nf,t,2), logs=matrix(#bid.cyc,#markers), old);
    for(j=1,#markers,
      if(gcd(markers[j][1]*markers[j][3],t)!=1,error("nonunit at t"));
      logs[,j]=ideallog(nf,markers[j][2],bid)
    );
    my(idx=subgroup_index(bid,logs,1), squares=subgroup_index(bid,logs,2));
    if(squares<=1,error("squares should generate a proper subgroup"));
    if(idx==1,
      good++;
      if(!mapisdefined(types,type),
        mapput(types,type,t);
        print("full unit group ", t, " type=", type, " invariants=", bid.cyc, " square index=", squares)
      ),
      bad++
    )
  );
  if(#types!=wanted_types,error("expected more successful splitting types", [f,types]));
  print("field=",f," markers=",apply(row->[row[1],row[3]],markers));
  print("products=",products[1]," max coefficient=",products[2]," generating primes=",good," other primes=",bad)
}
iferr({
  check_smooth_fixture(x^2+5,2,1);
  check_smooth_fixture(x^3-x-1,3,0);
  check_smooth_fixture(x^4-x-1,5,0);
},err,print(err);quit(1));
