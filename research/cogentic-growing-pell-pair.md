# Growing-degree Pell field pairs with two fixed marks

An infinite family of odd composite inputs has a productive square relation in two distinct monic Eisenstein fields of growing degree. The relation uses two fixed primitive marks. The fields have the norm-size bound needed at one-third sieve heights. This is a separate polynomial design from the scheduled monic pair, and the family can also be recognized and split from its integer value in polynomial bit time. [Exact replay](../experiments/cogentic-growing-pell-pair.py)

## A Pell family with two nontrivial gcds

Take an odd integer $m\ge3$, set $Y=2m+1$ and $C=Y^2-4$, and put $z=(Y+\sqrt C)/2$. The integer $C$ is between $(Y-1)^2$ and $Y^2$, and $z$ has norm one. For $j\ge1$ with $j\equiv1\pmod 3$, define $V+U\sqrt C=(C+\sqrt C)z^j$. The initial values and the multiplier for three more steps are
\[
U_1=(C+Y)/2,\quad V_1=C(Y+1)/2,\qquad
z^3=a+b\sqrt C,\quad
a=(Y^3-3Y)/2,\quad b=(Y^2-1)/2.
\]
Since $Y\equiv3\pmod4$, the initial values are even integers. The multiplier also has integral coefficients, so the recurrence $(U,V)\mapsto(aU+bV,aV+bCU)$ preserves evenness. Taking norms gives
\[
V^2+C=C(U^2+C).
\]
Set $N=U^2+C$. The value $V$ is always divisible by $C$, and modulo $C$ the initial $U$ and the recurrence multiplier $a$ are both $Y/2$, which is a unit. Thus $\gcd(U,C)=1$, and $U,V$ are units modulo the odd $N$. They have congruent squares modulo $N$.

The gcds split $N$ for every allowed parameter. Indeed $U\ge(C+Y)/2>Y+1$ and
\[
1<V/U=\sqrt{C+C(C-1)/U^2}<\sqrt{C+4}=Y.
\]
It follows that $0<V-U<V+U<N$. The two factors $V-U,V+U$ have product $(C-1)N$, and no prime dividing $N$ can divide both because $2U$ is a unit modulo $N$. Every prime power of $N$ lies in exactly one gcd, and neither gcd can be all of $N$. Therefore the two gcds are proper and multiply to $N$.

## Two irreducible fields and one common word

For an even integer $E$ with $0<E<m^k$, start with the monic degree-$k$ lift $X^k$ minus the base-$m$ expansion of $m^k-E$. It evaluates to $E$ at $m$ and has lower coefficients in $[-m+1,0]$. The difference modulo two from $X^k+1$ has degree at most $k-1$ and vanishes at $1$, since $m$ is odd and $E$ is even. Write that difference modulo two as $(X-1)H$ and lift $H$ with coefficients in $\{0,1\}$. Adding $(X-m)H$ preserves evaluation and leading coefficient, gives the desired reduction, and leaves all coefficients bounded in magnitude by $2m$.

Use this lift to take monic $P,Q$ with $P(m)=U$, $Q(m)=V$ and different degrees $k,\ell$. Choose $k$ minimal with $m^k>U$, and $\ell$ minimal with both $\ell>k$ and $m^\ell>V$. Define
\[
S=(1-2X)(3+2X),\qquad F=P^2-S,\qquad G=Q^2-S.
\]
Modulo two $S=1$, so $F,G$ reduce to their leading monomials. Their constants are each an odd square minus three, which has valuation one at two. Thus both are monic Eisenstein polynomials, and their degrees $2k$ and $2\ell$ distinguish the fields. The common argument obeys
\[
F(m)=N,\qquad G(m)=CN,
\]
so evaluation at $m$ defines a residue map modulo $N$ on each power order. For their roots $\alpha,\beta$, the respective elements $P(\alpha),Q(\beta)$ square to the same ordinary mark word $S$. If marks have $b>0$ in $a-bX$, take $(1,2),(-3,2)$ with the shared sign $-1$. Each mark is a unit at the residue because the product is $-C$ and $\gcd(C,N)=1$. The roots already lie in the power orders, so the certificate needs no reduction of maximal-order elements.

At $m=3,j=1$, the two roots evaluate to $26,180$, and the two gcds split $N=721$ into $7$ and $103$. The lifted polynomials have degrees six and ten. The replay also checks three larger cases, including a 14,615-bit input.

## Degree, norm scale and recognition

Take $\log m\asymp j^2\log j$ as $j\to\infty$. The two conjugate expressions for $V\pm U\sqrt C$ give $\log U=(j+1)\log Y+O(1)$ and $\log V=(j+2)\log Y+O(1)$ on this schedule. In fact $z=Y(1+O(Y^{-2}))$, and the smaller conjugate term is negligible. It follows that $k,\ell\asymp j$ and $L=\log N\asymp j^3\log j$. In particular both field degrees are $\Theta((L/\log L)^{1/3})$.

The lift coefficients are bounded by $2m$, so a defining polynomial of degree $e\in\{2k,2\ell\}$ has coefficient height $O(em^2)$. Its homogeneous norms on $|a|,|b|\le A$ have absolute value $O(e^2m^2A^e)$. For $W=L^{1/3}(\log L)^{2/3}$ and $V_*=L^{2/3}(\log L)^{1/3}$, this is $\exp(O(V_*))$ whenever $A\le\exp(O(W))$. The productive relation itself has constant mark height three.

For a promised parameter pair, the recurrence, lift and certificate take polynomial bit time. The parameters can also be found from $N$ alone. Enumerate $j\equiv1\pmod3$ through the bit length of $N$, which suffices because the recurrence increases $U$ by at least a factor eight every three steps. For each $j$, the expression $U^2+C$ strictly increases with odd $m\ge3$, since the initial values and positive recurrence coefficients increase with $m$. Binary search through $m\le\lfloor\sqrt N\rfloor$ therefore finds a hit if one exists. Intermediate bit lengths are $O((\log N)^2)$ for these search limits. A hit gives the gcd certificate above.

One can avoid all primes through $j^2$ on an infinite subfamily. For each odd prime $p\le j^2$, impose $Y\equiv2\pmod p$. Then $C=V=0$ and $U=1$ in the residue recurrence, so $N\equiv1\pmod p$. The coprime congruences on $m$ and its odd parity have modulus of bit length $O(j^2\log j)$. Choosing the constant in $\log m\asymp j^2\log j$ large enough fits that modulus in the chosen size interval. This roughness estimate does not reach trial division through $\exp(cW)$ for any fixed $c>0$. The theorem gives productive examples at the growing degree and mark height, while uniform productivity and survival of that larger trial filter remain open.
