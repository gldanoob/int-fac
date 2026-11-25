\\ Run checkHiddenDivisorLattice() after reading this file.

hiddenDivisorBasis(f, M, t, m) = {
  my(d=poldegree(f), polys);
  if(d<1 || pollead(f)!=1 || denominator(f)!=1 || M<2 || t<0 || m<1,
    error("expected a monic integral polynomial and valid lattice parameters"));
  polys=vector(m,j,
    my(s=min(t,(j-1)\d));
    M^(t-s)*f^s*variable(f)^(j-1-d*s)
  );
  matrix(m,m,i,j,polcoef(polys[j],i-1))
};

\\ The dual of an intersection is the sum of the two dual lattices.
hiddenDivisorIntersection(A, B) = {
  my(U=mattranspose(A^-1), V=mattranspose(B^-1), d=lcm(denominator(U),denominator(V)));
  my(dual=mathnf(matconcat([d*U,d*V])));
  mathnf(d*mattranspose(dual^-1))
};

\\ Each row is [f, public modulus, multiplicity, lower bound on the hidden divisor].
hiddenDivisorShortPolynomial(rows, m, radius) = {
  if(radius<1 || !#rows,error("expected a positive radius and at least one constraint"));
  my(B=matid(m), S=matdiagonal(vector(m,j,radius^(j-1))));
  foreach(rows,row,
    B=hiddenDivisorIntersection(B,hiddenDivisorBasis(row[1],row[2],row[3],m))
  );
  \\ shortcut: only the first LLL vector is tried, scan more vectors if it misses.
  B=B*qflll(S*B,1);
  Polrev(Vec(B[,1]),variable(rows[1][1]))
};

hiddenDivisorRoots(P, rows, radius) = {
  if(poldegree(P)<1,return([]));
  my(roots=select(r->type(r)=="t_INT" && abs(r)<=radius,nfroots(,P)));
  foreach(rows,row,
    roots=select(r->gcd(subst(row[1],variable(row[1]),r),row[2])>=row[4],roots)
  );
  Vec(roots)
};

checkHiddenDivisorLattice() = {
  my(x='x, a=12012, b=12036, f=x+1001-3, g=x^2+1003-9);
  my(rows=[[f,a,1,1001],[g,b,1,1003]]);
  my(A=hiddenDivisorBasis(f,a,1,4), B=hiddenDivisorBasis(g,b,1,4));
  if(matdet(hiddenDivisorIntersection(A,B))!=matdet(A)*matdet(B)/2,
    error("unexpected index for overlapping moduli"));
  if(hiddenDivisorRoots(hiddenDivisorShortPolynomial(rows,4,25),rows,25)!=[3],
    error("overlap fixture missed its root"));

  \\ Only the fixture construction uses p and q. The radius allows 160,001 offsets.
  my(c=10^6, radius=80000, p=nextprime(c+4321), q=nextprime(3*c+54321));
  my(N=p*q, M=nextprime(c+33333)*(p^2+p+1));
  f=x+c;
  rows=[[f,N,2,c-radius],[f^2+f+1,M,2,(c-radius)^2+(c-radius)+1]];
  my(P=hiddenDivisorShortPolynomial(rows,9,radius));
  my(v=vector(9,j,polcoef(P,j-1)*radius^(j-1)));
  my(D=(rows[1][4]*rows[2][4])^2);
  if(gcd(N,M)!=1 || vecsum(abs(v))>=D,error("shortness certificate failed"));
  my(found=apply(r->c+r,hiddenDivisorRoots(P,rows,radius)));
  found=select(r->r>1 && r<N && N%r==0 && isprime(r),found);
  if(found!=[p],error("cyclotomic fixture missed ",p,", got ",found));
  foreach(rows,row,
    if(#hiddenDivisorRoots(hiddenDivisorShortPolynomial([row],9,radius),[row],radius),
      error("a local first vector unexpectedly sufficed"))
  );
  \\ Here 1031² lies just below the square root of a three-prime input.
  my(n=1031^2*659*1613, c2=1024, r2=64, l=x+c2);
  my(rows2=[[l^2,n,2,(c2-r2)^2],[l^2+l+1,sigma(n),2,(c2-r2)^2]]);
  my(short=hiddenDivisorShortPolynomial(rows2,9,r2));
  if(vecsum(abs(vector(9,i,polcoef(short,i-1)*r2^(i-1))))>=(c2-r2)^8 ||
     hiddenDivisorRoots(short,rows2,r2)!=[7],error("single divisor sum fixture"));
  \\ Four supplied values of the ordinary divisor sum on different powers.
  my(c3=1006,r3=8,N3=1013*nextprime(3017)*nextprime(2019));
  my(rs=[2,3,5,7],ts=[5,2,1,1],g3=x+c3);
  my(rows3=vector(4,i,my(d=rs[i]-1);
    [subst(polcyclo(rs[i]),x,g3),sigma(N3^d),ts[i],(c3-r3)^d]));
  my(poly3=hiddenDivisorShortPolynomial(rows3,16,r3));
  if(vecsum(abs(vector(16,j,polcoef(poly3,j-1)*r3^(j-1)))) >=prod(i=1,4,rows3[i][4]^ts[i]) || hiddenDivisorRoots(poly3,rows3,r3)!=[7],
    error("divisor sums on powers fixture"));
  found
};
