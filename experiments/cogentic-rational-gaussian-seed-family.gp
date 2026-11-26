\\ Check the rational Gaussian seed family and its four sign blocks.
D=(x^2-15)/5; S=(10*x^2-76*x+150)/5; T=(38*x^2-300*x+570)/5;
A=x^2-8*x+17; B=13*x^2-96*x+181;
C=(17*x^2-120*x+225)/25; E=(181*x^2-1440*x+2925)/25;
N=4*S^4+D^4;
a=D^2+30*S^2; b=2*T*D; c=D^2+2*S^2; e=2*S*D;
if([T^2-15*S^2+56*D^2, N-A*B*C*E, a-b-9*A*B, a+b-25*C*E, c-e-A*E, c+e-B*C] != [0,0,0,0,0,0], print("polynomial identities failed");quit(1));
check(k,l) = {
  my(u=k/l, n=l^8*subst(N,x,u), d=l^2*subst(D,x,u), s=l^2*subst(S,x,u), t=l^2*subst(T,x,u));
  if(gcd(2*d*s*t*(d^2-2*s^2),n)!=1,error("nonunit chart denominator"));
  my(r=Mod(2*s^2,n)/d^2, p=Mod(l^4*subst(a,x,u),n)/(l^4*subst(b,x,u)), q=Mod(l^4*subst(c,x,u),n)/(l^4*subst(e,x,u)));
  if(r^2!=-1 || p^2!=1 || q^2!=1,error("modular roots"));
  my(labels=[1-r,-30+194/(r-1),-2*r/(r-1)]);
  if(labels[1]*labels[2]!=Mod(2*t,n)^2/d^2 || labels[1]*labels[3]!=Mod(2*s,n)^2/d^2,error("unit labels"));
  my(parts=apply(f->l^2*subst(f,x,u),[A,B,E,C]), pair=[gcd(lift(p)-1,n),gcd(lift(q)-1,n)]);
  if(gcd(pair[1],pair[2])!=parts[1] || pair[1]!=parts[1]*parts[2] || pair[2]!=parts[1]*parts[3],error("sign blocks"));
  if(prod(i=1,#parts,parts[i])!=n || sum(i=1,4,sum(j=i+1,4,gcd(parts[i],parts[j])))!=6,error("block product or coprimality"));
  print([k,l,n,parts]);
};
iferr(check(11300,1);check(129950,1);check(1340874950,118651),err,print(err);quit(1));
