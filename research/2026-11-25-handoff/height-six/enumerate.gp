\\ Set H before reading this file to enumerate a different coefficient height.
if(type(H)!="t_INT", H=6);
{
  my(fields=List());
  forvec(v=vector(3,i,[-H,H]),
    my(f=x^3+Polrev(v));
    if(polisirreducible(f),listput(fields,polredabs(f)))
  );
  foreach(Set(Vec(fields)),f,print([nfdisc(f),vector(3,i,polcoef(f,i-1))]));
}
