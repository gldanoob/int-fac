# How often two cyclotomic values can have nearly maximal gcd

Fix $k\ge3$, put $d=\varphi(k)$ and let $B\ge1$. For integers $X<p<q\le2X$, consider the promise
$$
     \gcd(\Phi_k(p),\Phi_k(q))\ \ge\ (pq)^{d/2}/B.
$$
The existing input-only algorithm factors $N=pq$ on this promise in $O_k(B^{1/d}\operatorname{poly}(\log N))$ bit operations when $p,q$ are primes. The following bounds count even the integer pairs. [Factoring algorithm](2026-11-25-handoff/cyclotomic-supply/audit.md)

* Each dyadic interval contains $O_k(B^2)$ pairs. Uniformly over all $3\le k\le K$ together, the number is $O(K^2 B^2\log(2B))$ with an absolute implied constant. In particular, for $K,B=X^{o(1)}$ there are at most $X^{o(1)}$ pairs among the $\asymp X^2/\log^2 X$ prime pairs.
* For a fixed $k$ with $d>2$ and fixed $B$, there are only finitely many integer pairs $2\le p<q\le2p$ over **all** sizes. This finiteness argument gives no cutoff on the last pair. For $k=4$ there is an infinite family of balanced integer pairs already at $B=2$. Primality of both coordinates is a further condition.

## A uniform count in one interval

Set $F=\Phi_k$, $c=\mu(k)/d$ and $h(t)=F(t)^{1/d}$ for $t>1$. The cyclotomic product identity gives, uniformly for $t\ge4$,
$$
 \log F(t)-d\log t
 =\sum_{m\mid k}\mu(k/m)\log(1-t^{-m})
 =-\mu(k)/t+E,\qquad |E|\le4/t^2.
$$
Indeed the quadratic and higher terms from $m=1$ contribute at most $1/t^2$. The entire sum for $m\ge2$ has absolute value bounded by $\sum_{m\ge2}t^{-m}/(1-t^{-2})\le 8/(3t^2)$. Exponentiating and using $|e^z-1-z|\le |z|^2e^{|z|}/2$ gives
$$
       |h(t)-(t-c)|\le 8/(dt).
$$

For a qualifying pair let $g=\gcd(F(p),F(q))$, $a=F(p)/g$, $b=F(q)/g$. Both are positive and coprime. The log estimate gives $ab\le4B^2$ for $X\ge4$, uniformly even when $d$ grows. For fixed $k$, balance gives the stronger individual bounds $a,b=O_k(B)$. Each factor $|t-\zeta|$ of $h(t)^d$, with $\zeta$ a primitive $k$-th root, increases with real $t>1$. Thus $r=b/a>1$.

Fix one ratio $r$ and put $\rho=r^{1/d}$. Since $t-1\le h(t)\le t+1$, we have $\rho\le(2X+1)/(X-1)\le3$. The equality $h(q)=\rho h(p)$ puts every pair for this ratio within vertical distance $32/(dX)\le16/X$ of the line $q-c=\rho(p-c)$. Divide the $p$ interval into 128 equal subintervals. For any three points in one subinterval, subtracting the slope of that line from the second coordinate leaves the triangle determinant unchanged. Its absolute value is at most $2(X/128)(32/X)<1$. This integer determinant vanishes, so the points in each subinterval are collinear. This is the elementary linear determinant argument from lattice-point counting. [Bombieri–Pila](https://people.maths.ox.ac.uk/pila/Ovals.pdf)

A line with two such points has positive slope because $F$ is increasing. A polynomial identity $F(uT+v)=rF(T)$ with $u>0$ would permute the finite complex root set by $z\mapsto uz+v$. Comparing its positive diameter forces $u=1$, contrary to $u^d=r>1$. A line therefore meets the ratio curve in at most $d$ points. Each ratio contributes at most $128d$. Counting reduced ratios by their individual bounds proves $O_k(B^2)$. Using $ab\le4B^2$ gives $O(B^2\log(2B))$ choices uniformly. Summing $d\le k$ over $k\le K$ proves the simultaneous bound. The bounded range $X<4$ can be absorbed in either estimate.

## Why bounded deficits terminate in degrees greater than two

Fix $k,B$. In a putative infinite balanced family only finitely many ratios occur, by $ab=O_k(B^2)$, which also follows directly from $p<q\le2p$. Take a fixed $r>1$ occurring infinitely often. In the plane curve $F(Y)-rF(X)=0$, some absolutely irreducible component defined over $\mathbb Q$ contains infinitely many of the points. Indeed a component distinct from a Galois conjugate has only finitely many rational points by intersection with that conjugate. The full highest homogeneous part $Y^d-rX^d$ has distinct linear factors over $\mathbb C$. Hence a component of degree $m$ has $m$ distinct points at infinity, giving at least $m$ places there on its normalization. Siegel's integral-point theorem forces $m\le2$. This uses the classical theorem for curves in separated variables. Bilu and Tichy give a general classification, and Bilu treats quadratic factors in this setting. [Bilu–Tichy, Theorem 10.1 and Proposition 10.2](https://matwbn.icm.edu.pl/ksiazki/aa/aa95/aa9534.pdf#page=24) · [Bilu, quadratic factors](https://pldml.icm.edu.pl/pldml/element/bwmeta1.element.bwnjournal-article-aav90i4p341bwm)

As $p\to\infty$ on the component, $q/p\to\rho=r^{1/d}$. Evaluating the highest homogeneous part of this rational component at $(1,\rho)$ shows $[\mathbb Q(\rho):\mathbb Q]\le2$. If $\rho$ is rational, then $q-c-\rho(p-c)$ has a fixed denominator and tends to zero. Eventually the family lies on a line, which the preceding argument excludes.

If $\rho$ is quadratic irrational, its conjugate is real and its $d$-th power also equals $r$. The only other real root is $-\rho$, so $s=\rho^2$ is rational. The root estimate gives
$$
 (q-c)^2-s(p-c)^2=O_{k,r}(1).
$$
The left side again has fixed denominator. An infinite subfamily therefore lies on a single conic $V^2-sU^2=t$, with $U=p-c,\ V=q-c$. When $t=0$ this is a union of lines and the positive branch has already been excluded by the line argument. When $t\ne0$ the conic is absolutely irreducible, so it divides $F(V+c)-rF(U+c)$ by Bézout. Reflection $V\mapsto -V$ preserves the conic. Taking the difference shows $F(V+c)=F(-V+c)$ identically since infinitely many $V$'s occur. Write $F(V+c)=P(V^2)$. On the conic this gives
$$
                P(sz+t)=rP(z)
$$
as a polynomial identity. The real dilation $z\mapsto sz+t$, with $s>1$, cannot permute a finite set of positive diameter. Yet $P$ has at least two distinct roots, since $F$ has $d>2$ distinct roots. This excludes the last case.

For $k=4$, start with $(p,q)=(2,3)$ and iterate $(p,q)\mapsto(3p+2q,4p+3q)$. These are positive increasing solutions of $q^2-2p^2=1$ and $p<q<2p$. Thus $\Phi_4(q)=2\Phi_4(p)$ and $\gcd(\Phi_4(p),\Phi_4(q))=p^2+1>pq/2$. This family establishes the degree distinction for integer pairs.

## Finite checks

The GP replay tests the root enclosure by raising rational endpoints to the exact integer power at 826 index/argument combinations. On all 32,640 pairs $256<p<q\le512$, the numbers passing at $B=256$ for $k=3,4,5,6,8,10,12$ are respectively $23,43,0,25,0,0,0$. Restricting to primes gives $2,2,0,1,0,0,0$. Two smaller cutoffs check the changing counts. In degree four, the prime pair $(283,389)$ at $k=10$ has gcd $37\,901$ and least integer deficit $319\,758$. The replay also verifies 32 consecutive terms of the quadratic Pell family. Finiteness over all sizes follows from the argument above. [Exact replay](../experiments/cyclotomic-overlap-count.gp)
