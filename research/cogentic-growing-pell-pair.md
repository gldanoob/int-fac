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

## Surviving the one-third trial-division bound

Fix an integer $\kappa\ge1$. For all sufficiently large $j\equiv1\pmod3$, there is an odd admissible $m$ in
\[
[M,2M],\qquad M=j^{\kappa j^2},
\]
such that $N$ has no prime factor through $Z=j^{\kappa j/8192}$. Here $L=(2\kappa+o(1))j^3\log j$, so $W=((18\kappa)^{1/3}+o(1))j\log j$. Thus $Z\ge\exp(\kappa^{2/3}W/32768)$ for all sufficiently large $j$. Taking $\kappa$ large enough gives an infinite subfamily that survives any **fixed** threshold $\exp(cW)$. The degree remains $\Theta((L/\log L)^{1/3})$ with a constant depending on $\kappa$.

For each odd prime $p\le j^2$, impose $Y\equiv2\pmod p$. Then $C=V=0$ and $U=1$ in the residue recurrence, so $N\equiv1\pmod p$. Also require $m$ odd. The resulting CRT class has modulus $D=\prod_{p\le j^2}p$ and meets $[M,2M]$ on a progression of $K\ge\exp((\kappa-o(1))j^2\log j)$ consecutive indices. To bound $D$, the primes between successive powers of two divide the corresponding central binomial coefficient. This gives $\sum_{p\le x}\log p\le4x\log 2<3x$ by summing dyadically up to the next power of two.

The recurrence makes $N$ a polynomial in $Y$ of degree $2(j+1)\le4j$ with coefficients in $\mathbb Z[1/2]$. It is nonzero modulo each odd prime because its value at $Y=2$ is one. Since $D$ is a unit at $p>j^2$, the progression index has at most $h_p\le4j$ forbidden residues modulo $p$. Put $e_p=h_p/p$, which is at most $1/2$ for large $j$.

Group the primes in $(j^2,Z]$ into bands $(\sqrt{x_i},x_i]$ with $x_i=Z^{2^{-i}}$, truncating the final band at $j^2$. The number $B$ of bands is $O(\log j)$ and $\sum_i\log x_i\le2\log Z$. The prime bound above gives $\pi(t)\le\sqrt t+6t/\log t\le7t/\log t$ for $t\ge2$. Partial summation consequently gives $\sum_{\sqrt{x_i}<p\le x_i}1/p\le11$ on these bands. Thus $\sum_{p\text{ in band }i}e_p\le44j$.

For a progression index let $I_i$ be the indicator of avoiding the forbidden residues in band $i$. Take the even Bonferroni truncation $U_i$ through order $J=1024j$ and the odd truncation $L_i$ through order $J-1$. Then $0\le I_i\le U_i$ and $L_i\le I_i$. Telescoping products gives the pointwise lower bound
\[
\prod_i I_i\ \ge\ \prod_i U_i-\sum_i(U_i-L_i)\prod_{k\ne i}U_k.
\]
First compute its density in the product law of independent uniform residues. For each band, $\mathbb E U_i\ge\prod_p(1-e_p)\ge\exp(-88j)$, while $\mathbb E(U_i-L_i)$ is the sum of the order-$J$ subset products of the $e_p$. This is at most $(44j)^J/J!\le8^{-J}$. The block gap divided by $\mathbb E U_i$ is exponentially small in $j$. The product-law lower bound is therefore at least $\tfrac12\prod_{j^2<p\le Z}(1-e_p)\ge\tfrac12\exp(-88jB)$ for large $j$.

For each subset term in this expansion, CRT gives its expected count in the actual interval of $K$ indices with error at most the product of the $h_p$ for the selected primes. Each block contributes at most $(J+1)(4j x_i)^J$ to the sum of absolute rounding errors, since at most $J$ primes occur there. Accounting for the $B+1$ products, the logarithm of the total error is at most
\[
2J\log Z+O(j\log^2 j)=(\kappa/4+o(1))j^2\log j.
\]
The main lower bound is $\tfrac12K\exp(-88jB)=\exp((\kappa-o(1))j^2\log j)$ and exceeds this error. Hence some progression index avoids every prime through $Z$. The proof of existence still uses a selected Pell family. It supplies no claim that general inputs or the earlier scheduled monic pair admit a productive square relation.

## A variant with both defining values equal to the input

Use odd $m\ge5$, $Y=m+1$, $y=Y/2$, $C(X)=(X+1)^2-4$, and $c=C(m)=4(y^2-1)$. Set
\[
V+U\sqrt c=(c+\sqrt c)(y+\tfrac12\sqrt c)^j
\]
for even $j\ge2$. The multiplier squared is $a+y\sqrt c$ with $a=2y^2-1$. Starting with $U=1$, $T=1$, where $T=V/c$, the $j/2$ steps are
\[
(U,T)\longmapsto(aU+ycT,aT+yU).
\]
In particular $V=cT$ and $U$ stays odd. The residue of $U$ modulo $c$ is a power of $a$, which is a unit because every odd prime dividing $c$ has $y^2\equiv1$, and $a$ is odd. The norm identity is again $V^2+c=c(U^2+c)$. We have $U\ge a+yc>c/2$ and $U>Y+1$ after the first step. Thus $1<V/U<Y$ and the same two proper gcds split $N=U^2+c$.

Construct a monic lift $P(m)=U$ of degree $k$ with $m^k>U$ and parity $P\equiv X^k+X+1\pmod2$. This parity has the correct value at $m$. Since $T=V/c<U$, lift $J(m)=T$ of degree $\ell\in\{k,k+1\}$ with $J\equiv1+X+\cdots+X^\ell\pmod2$. Choose $\ell$ so that $\ell+1\equiv T\pmod2$, which makes the target parity compatible at $m$. The base-$m$ and $(X-m)$ adjustment above apply to any prescribed monic parity polynomial with the same value at $m$ and still give coefficient height at most $2m$.

The defining polynomials are
\[
F=P^2+C,\qquad G=CJ^2+1.
\]
Modulo two $F=X^{2k}$ and $G=((X+1)J+1)^2=X^{2\ell+2}$. Their constants are respectively an odd square minus three and one minus three times an odd square, so both constants have valuation one at two. Both are monic Eisenstein, with distinct degrees $2k$ and $2\ell+2$. Now $F(m)=G(m)=N$ exactly, since $cT^2+1=(V^2+c)/c$. For roots $\alpha,\beta$ of $F,G$, the two square roots are $P(\alpha)$ and $C(\beta)J(\beta)$. The second identity is $(CJ)^2+C=CG$, which permits its defining polynomial to have the same exact value as the first. Both square roots represent the signed word $(1-X)(3+X)=-C(X)$ and reduce to $U,V$. In positive-$b$ orientation the marks are $(1,1),(-3,1)$ with shared sign $-1$. They are units since $\gcd(c,N)=1$.

With $m\in[j^{\kappa j^2},2j^{\kappa j^2}]$, the conjugate formula again gives $\log U=(j+1)\log Y+O(1)$. The degrees, coefficient heights and norm bounds have the same orders as before. The recurrence gives polynomials in $y$ of degrees $j+1$ for $U$ and $j$ for $T$ after the first step, and at $y=1$ it gives $U=T=1$, $c=0$. The polynomial $N$ therefore has degree $2(j+1)$ and value one at $y=1$ modulo every odd prime. Preassigning $m\equiv1$ at the small primes replaces $Y\equiv2$ in the sieve, and $y$ is an invertible affine function of the progression index at the remaining primes. The same counting proof gives infinitely many of these exact-value inputs with no prime factor through $\exp(\kappa^{2/3}W/32768)$. For input recognition, enumerate even $j$ through the bit length and binary search odd $m$ as before. Strict monotonicity follows from the positive recurrence, and $a\ge17$ bounds the number of steps for a hit.

The replay checks $m=5,j=2$ with $N=12801=17\cdot753$, degrees six and eight, and both exact evaluations. It also verifies three larger exact-value examples. These fields are selected for this family. No conclusion about the canonical monic pair or arbitrary inputs follows.

### Making both residue branches simple

For one integer $s$, replace $P$ and $J$ by $P+2s(X-m)$ and $J+2s(X-m)$. This preserves their values at $m$, their degrees and parity, and the Eisenstein conditions on $F$ and $G$. The two root values are still $U,V$, and the shifts in the defining derivatives at $m$ are respectively $4sU$ and $4sV$.

For each prime $p\mid N$, the two slopes are units modulo $p$, so at most two residue classes of $s$ make either derivative zero. Write $r$ for the number of distinct primes dividing $N$. If all are greater than $2r$, the interval $0\le s\le2r$ has distinct residues modulo each such prime, so at most $2r$ candidates are forbidden and at least one succeeds. On the rough subfamilies above, $r<\log N/\log Z=O(j^2)$ and every prime factor exceeds $2\operatorname{bitlength}(N)$ for sufficiently large $j$. It is enough to try $0\le s\le2\operatorname{bitlength}(N)$ using gcds with $N$, without knowing its factorization. The coefficient height grows by at most a factor $O(1+s)$ for the lifted roots, leaving the degree and logarithmic norm bounds unchanged.

Both repaired derivatives being units gives simple roots at every prime dividing $N$. For each prime power, Hensel lifting selects a root congruent to $m$ modulo that prime power. The induced map on algebraic integers lands in the corresponding $p$-adic integer ring, and reduction followed by CRT gives the required maximal-order residue map. The square certificate itself continues to use only the power orders.

At $m=9,j=2$, the original derivative gcds are $7$ and $1$ for $N=279937$, so the first already supplies a factor. The replay also repairs with $s=1$, checks both derivative gcds are one, verifies $F(m)=G(m)=N$, and recovers the unchanged square certificate with factors $49$ and $5713$.
