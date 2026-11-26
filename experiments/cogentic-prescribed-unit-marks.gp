check_unit_field(n, e, s) = {
  my(m=2*n+3, word=(x-1)*(x+5), j=sum(i=0,(e-1)/2,x^(2*i+1)));
  my(value=lift(Mod(s-1,n)/Mod(16,n)));
  if(!value, value=n);
  if((value-subst(j,x,m))%2, value+=n);
  my(h=j+value-subst(j,x,m), root=1+word*h, field=root^2-word);
  my(degree=2*e+4);
  if(poldegree(field)!=degree || pollead(field)!=1 || polcoeff(field,0)%4!=2 ||
    sum(i=0,degree-1,polcoeff(field,i)%2), error("expected monic Eisenstein field"));
  if(subst(field,x,1)!=1 || subst(field,x,-5)!=1 ||
    (root^2-word)%field || subst(field,x,m)<=0 || subst(field,x,m)%n,
    error("invalid square or mark norm"));
  my(residue=subst(root,x,m)%n);
  if(residue!=s%n || residue^2%n!=16%n, error("unexpected modular root"));
  residue
}

iferr({
  foreach([3,9,35,221,2^127+1], n,
    if(check_unit_field(n,1,4)!=check_unit_field(n,3,4), error("default signs differ"));
  );
  my(r=check_unit_field(221,1,4), s=check_unit_field(221,3,30));
  if(gcd(r-s,221)!=13 || gcd(r+s,221)!=17, error("supplied sign did not split"));
  print("Verified five unit-mark pairs and one supplied CRT split");
}, err, print(err); quit(1));
