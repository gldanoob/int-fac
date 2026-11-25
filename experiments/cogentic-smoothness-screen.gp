\\ Load the existing integral Cantor group law and independently checked twist map.
read("experiments/genus-two-cantor.gp");

raw_split(n) = {
  my(s=1);
  forprime(l=3,13,s*=l^logint(16*n^2,l));
  for(trial=1,72,
    my(g2=x^2+random(n)*x+random(n),g3=x^3+random(n)*x^2+random(n)*x+random(n));
    my(F=g2*g3,a=random(n),e=subst(F,x,a),skip=0);
    for(k=1,2,
      my(h=gcd(n,if(k==1,e,poldisc(F))));
      if(h>1 && h<n,return([h,0]));
      if(h==n,skip=1);
    );
    if(!skip,
      my(h=composite_gcd(F,a,e,s,n));
      if(h>1 && h<n && n%h==0,return([h,1]));
    );
  );
  [0,0];
}

screen(n,bound) = {
  if(n==1,return([1,0]));
  if(isprime(n),return([n<=bound,0]));
  my(pp=0,k=ispower(n,,&pp));
  if(k,return(screen(pp,bound)));
  my(hit=if(n%2,raw_split(n),[2,0]));
  if(!hit[1],return([0,0]));
  my(u=screen(hit[1],bound),v=screen(n/hit[1],bound));
  [u[1] && v[1],hit[2]+u[2]+v[2]];
}

check_screen() = {
  my(yes=0,no=0,crt=0,base=[5,7,11,13,17,19,23,29,31,37,41,43]);
  setrand(11252026);
  for(i=1,#base,for(j=i,#base,
    for(k=1,2,
      my(n=base[i]^k*base[j],r=screen(n,31));
      if(r[1]!=(base[j]<=31),error("incorrect smoothness decision ",[n,r]));
      yes+=r[1];no+=!r[1];crt+=r[2];
    );
  ));
  print("screen accepts, rejects, Cantor splits = ",[yes,no,crt]);
}
iferr(check_screen(),e,print(e);quit(1));
quit;
