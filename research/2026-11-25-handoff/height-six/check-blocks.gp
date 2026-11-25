checkblocks()={
  my(a=x^3-2*x-2,b=x^3+6*x-5,c=x^3-x^2+5*x-6,ab=polcompositum(a,b)[1],ac=polcompositum(a,c)[1]);
  if(poldegree(ab)!=9||poldegree(ac)!=9||!nfisincl(x^3-12*x-22,ab)||!nfisincl(x^3-x^2-9*x-13,ac),error("-19 dependence"));
  print(["minus19",vector(3,i,nfdisc([a,b,c][i])),9,9]);
  a=x^3-x^2+x-3;b=x^3+3*x-8;ab=polcompositum(a,b)[1];
  if(poldegree(ab)!=9||!nfisincl(x^3-6*x-10,ab)||!nfisincl(x^3+6*x-6,ab),error("-51 dependence"));
  print(["minus51",nfdisc(a),nfdisc(b),9]);
  a=x^3-x^2+3*x+2;b=x^3-x^2+x-7;ab=polcompositum(a,b)[1];
  if(poldegree(ab)!=9||!nfisincl(x^3+4*x-6,ab),error("-307 dependence"));
  print(["minus307",nfdisc(a),nfdisc(b),9]);
  my(F=[x^3-12,x^3-x^2+6*x-12,x^3-7,x^3-6,x^3-5,x^3-x^2-3*x-3,x^3-3,x^3-2,x^3-x^2+5*x+1,x^3-x^2-7*x+13]);
  my(P=[2,3,5,7,11,17],V=[[1,2,0,0,0,0],[0,0,0,0,0,1],[0,0,0,1,0,0],[1,1,0,0,0,0],[0,0,1,0,0,0],[1,0,1,0,0,0],[0,1,0,0,0,0],[1,0,0,0,0,0],[1,0,0,2,0,0],[1,0,0,0,2,0]]);
  for(i=1,#F,if(polredabs(F[i])!=polredabs(x^3-prod(j=1,6,P[j]^V[i][j])),error("pure-cubic line",i)));
  print(["minus3",10,"certified pure-cubic lines on six prime radicands"]);
};
iferr(checkblocks(),E,print(E);quit(1));
