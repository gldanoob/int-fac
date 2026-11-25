\\ Gcd-checked Cantor addition in a monic odd-degree genus-two model.

unit_or_factor(value,n) = {
  my(g = gcd(lift(value),n));
  if(g>1 && g<n, error("factor ",g));
  g==1;
}

check_degree(f,n) = {
  if(f != 0 && !unit_or_factor(pollead(f),n), error("invalid leading coefficient"));
  poldegree(f);
}

q_and_r(f,g,n) = {
  check_degree(g,n);
  my(number = divrem(f,g));
  check_degree(number[2],n);
  number;
}

unit_monic(f,n) = {
  check_degree(f,n);
  f / pollead(f);
}

exact_quo(f,g,n) = {
  my(qr = q_and_r(f,g,n));
  if(qr[2] != 0, error("inexact Cantor polynomial division"));
  qr[1];
}

poly_bezout(f,g,n) = {
  my(a=1,b=0,c=0,d=1,qr);
  while(g != 0,
    qr=q_and_r(f,g,n);
    [f,g]=[g,qr[2]];
    [a,c]=[c,a-qr[1]*c]; [b,d]=[d,b-qr[1]*d];
  );
  check_degree(f,n);
  my(lc=pollead(f));
  [f/lc,a/lc,b/lc];
}

cantor(left,right,f,n) = {
  my(u=left[1],v=left[2],w=right[1],t=right[2]);
  if(u==1, return(right));
  if(w==1, return(left));
  my(first=poly_bezout(u,w,n), second=poly_bezout(first[1],v+t,n), d=second[1]);
  my(newu=exact_quo(u*w,d^2,n));
  my(top=second[2]*(first[2]*u*t+first[3]*w*v)+second[3]*(v*t+f));
  my(newv=q_and_r(exact_quo(top,d,n),newu,n)[2]);
  while(check_degree(newu,n)>2,
    newu=unit_monic(exact_quo(f-newv^2,newu,n),n);
    newv=q_and_r(-newv,newu,n)[2];
  );
  [newu,newv];
}

multiply_divisor(point,m,f,n) = {
  my(r=[Mod(1,n),Mod(0,n)],bits=binary(m));
  for(i=1,#bits,r=cantor(r,r,f,n); if(bits[i],r=cantor(r,point,f,n)));
  r;
}

composite_gcd(F,a,d,s,n) = {
  my(one=Mod(1,n),a0=a*one,d0=d*one, mono=d0^5*subst(F,x,x/d0));
  my(hit=0);
  iferr(multiply_divisor([one*x-d0*a0,d0^3],s,mono,n),err,
    if(errname(err)!="e_USER",error(err));
    my(payload=component(err,1));
    if(#payload!=2 || payload[1]!="factor ",error(err));
    hit=payload[2];
  );
  hit;
}
