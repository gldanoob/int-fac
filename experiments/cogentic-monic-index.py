"""Replay the common-root repair, denominator clearing, and square extraction."""

import os
import runpy
import subprocess
from math import gcd
from pathlib import Path


def derivative_at(coefficients, argument):
    return sum(i * c * argument ** (i - 1) for i, c in enumerate(coefficients) if i)


def repair(n, m, f, g):
    derivatives = [derivative_at(p, m) for p in (f, g)]
    for t in range(3):
        gcds = tuple(gcd(d + 4 * t, n) for d in derivatives)
        for divisor in gcds:
            if 1 < divisor < n:
                return divisor
        if gcds == (1, 1):
            return t, tuple((p[0] - 4 * t * m, p[1] + 4 * t, *p[2:]) for p in (f, g))
    raise AssertionError((n, m, derivatives))


def run():
    constructor = runpy.run_path(str(Path(__file__).with_name("cogentic-monic-pair.py")))
    monic_pair, scheduled_degree = constructor["monic_pair"], constructor["scheduled_degree"]
    inputs = (*range(9, 8192, 2), (1 << 127) + 1, (1 << 255) - 19, (1 << 1023) + 1)
    outcomes = {}
    for n in inputs:
        m, f, g = monic_pair(n, scheduled_degree(n))
        result = outcomes[n] = repair(n, m, f, g)
        if isinstance(result, int):
            assert 1 < result < n and n % result == 0
            continue
        t, (left, right) = result
        assert 0 <= t <= 2 and right == left[:-1] + (1 - m, 1)
        for before, after in ((f, left), (g, right)):
            assert len(after) == len(before) and after[-1] == 1 and after[0] % 4 == 2
            assert all(c % 2 == 0 for c in after[:-1])
            assert max(map(abs, after)) <= 10 * m
            assert sum(c * m**i for i, c in enumerate(after)) == n
            assert gcd(derivative_at(after, m), n) == 1

    assert monic_pair(2385, scheduled_degree(2385))[:2] == (47, (82, 2, 1))
    assert gcd(9, 2385) == 9 and (47 + 1) % 9 != 0 and outcomes[2385] == 3
    assert outcomes[145][0] == 1
    assert monic_pair(895, scheduled_degree(895))[0::2] == (29, (54, 0, -28, 1))
    assert outcomes[895][0] == 0
    assert monic_pair(11, scheduled_degree(11))[0::2] == (3, (2, 0, -2, 1))
    assert outcomes[11][0] == 0

    script = """
check(ok) = if(!ok, error("common-root or square extraction replay failed"));
power_square_root(P,Q) = {
  if(Q==0, return([1,0]));
  my(e=poldegree(P), n=2*e, h=denominator(Q,1), H=h^2*Q);
  my(X=matrix(n,n), Y=matrix(n,n), one=vector(n,i,i==1)~, Z, powers);
  for(j=1,e,
    my(a=lift(Mod(x^j,P)), b=lift(Mod(x^(j-1)*H,P)));
    for(i=1,e,
      X[i,j]=X[e+i,e+j]=polcoef(a,i-1);
      Y[i,e+j]=polcoef(b,i-1);
    );
    Y[e+j,j]=1;
  );
  for(t=0,n*(n-1)/2,
    Z=Y+t*X;
    powers=matrix(n,n);
    my(v=one);
    for(k=1,n, powers[,k]=v; v=Z*v);
    if(matdet(powers)!=0,break);
  );
  check(matdet(powers)!=0);
  my(factors=factor(charpoly(Z,y)));
  if(matsize(factors)[1]==1, return([0]));
  check(matsize(factors)[1]==2 && factors[,2]==[1,1]~);
  my(f1=factors[1,1], f2=factors[2,1], bezout=gcdext(f1,f2));
  check(poldegree(f1)==e && poldegree(f2)==e && bezout[3]==1);
  my(g=2*bezout[1]*f1-1, yvector=Y*one, v=vector(n)~);
  forstep(k=poldegree(g),0,-1,v=Z*v+polcoef(g,k)*yvector);
  check(v[e+1..n]==vector(e)~);
  my(root=Polrev(Vec(v[1..e]),x)/h);
  check(Mod(root^2-Q,P)==0);
  [1,root];
};
replay() = {
  my(P=x^3-28*x^2+54, N=895, m=29, D=deriv(P), beta=Mod((x^2-x+3)/15,P));
  check(poldisc(P)==4662900 && poldisc(P)==15^2*nfdisc(P));
  check(gcd(15,N)==5 && subst(D,x,m)==899 && gcd(899,N)==1);
  check(charpoly(beta,y)==y^3-51*y^2+33*y-5);
  my(C=lift(D*beta));
  check(denominator(C,1)==1 && C==51*x^2-22*x-90);
  check(lift(Mod(subst(C,x,m),N)/subst(D,x,m))==472);
  my(root=power_square_root(P,8*x^2+2*x-12)[2], gamma=lift(beta)+x+1);
  check(root==gamma || root==-gamma);
  C=lift(Mod(D*root,P));
  check(denominator(C,1)==1);
  my(value=Mod(subst(C,x,m),N)/subst(D,x,m));
  check(value==502 || value==-502);
  check(value^2==509 && gcd(lift(value),N)==1);
  check(power_square_root(P,2)==[0] && power_square_root(P,0)==[1,0]);
  check(power_square_root(P,(x+1)^2/49)[1]==1);
  P=x^3-2*x^2+2;
  check(poldisc(P)==-44 && gcd(poldisc(P),11)==11 && gcd(subst(deriv(P),x,3),11)==1);
};
iferr(replay(), err, print(err); quit(1));
"""
    result = subprocess.run([os.environ.get("GP", "gp"), "-fq"], input=script,
                            text=True, capture_output=True, timeout=15, check=True)
    assert not result.stderr, result.stderr
    print(f"Verified common-root repair on {len(inputs)} inputs and exact square extraction fixtures")


if __name__ == "__main__":
    run()
