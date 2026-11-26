# Obstructions to transporting the Pell square certificate

The manual Pell family has explicit square roots in its quadratic and cubic power orders. Copying its signed product and roots into the automatic pair cannot give an exact equality with a common signed product of primitive marks once the automatic degree exceeds two. This obstruction allows separate substitutions in the two fields and puts no upper bound on mark height. The argument also gives degree bounds for a common rational substitution and excludes a polynomial composition on the cubic side. [Manual Pell certificate](cogentic-parametric-square-split.md)

## The valuations of the transported Pell product

Write $F_0=X^2+2c^2$ and $G_0=F_0+(X-M)X^2$ for the manual pair, where $M=1+c^2n^2$, $w^2=1+2n^2$, $n=2uv$ is even and $c$ is odd. Set

\[
L=2n^2(X+1-M)+1,\qquad
S=(X^2-4c^2n^2)L,\qquad
R_F=wX(1+n^2X),\qquad R_G=XL.
\]

The exact identities in the manual certificate are

\[
R_F^2-S=(w^2n^4X^2+2n^2L)F_0,\qquad
R_G^2-S=2n^2 L G_0.
\]

Let $\alpha,\beta$ be the generators of a canonical pair of degrees $d,d+1$ for the same input, with $d>2$. Both defining polynomials are Eisenstein at two. In each field normalize the valuation by $v_2(2)=1$, so $v_2(\alpha)=1/d$ and $v_2(\beta)=1/(d+1)$.

Consider any elements $y_F\in\mathbb Q(\alpha)$ and $y_G\in\mathbb Q(\beta)$ such that

\[
R_F(y_F)^2=S(y_F)\ne0,\qquad R_G(y_G)^2=S(y_G)\ne0.
\]

This includes separate rational substitutions. Since $L(y_G)\ne0$, the second polynomial identity forces $G_0(y_G)=0$ and hence $v_2(y_G)=1/3$. The first gives either $F_0(y_F)=0$ and $v_2(y_F)=1/2$, or $w^2n^4 y_F^2+2n^2 L(y_F)=0$. In the latter case $Y=ny_F$ satisfies

\[
w^2 Y^2+4nY+2-4c^2n^4=0.
\]

Dividing by the odd leading coefficient makes this a quadratic Eisenstein polynomial over $\mathbb Z_2$. Thus $v_2(y_F)=1/2-r$ in this branch, where $r=v_2(n)\ge1$. The fields have valuation groups $(1/d)\mathbb Z$ and $(1/(d+1))\mathbb Z$. Both branches therefore require $d$ even and $d+1$ divisible by three, hence $d\equiv2\bmod6$.

In each case $v_2(L(y))=0$ since its constant is odd and $v_2(2n^2 y)>0$. The valuation of $y^2$ is strictly less than $v_2(4c^2n^2)$. Consequently

\[
v_2(S(y_F))\in\{1,\,1-2r\},\qquad v_2(S(y_G))=2/3.
\]

For an ordinary primitive mark $(a,b)$, the two terms $a,b\alpha$ have different valuations, so $v_2(a-b\alpha)$ is $0$ for odd $a$ and $1/d$ for even $a$. The same rule in the second field gives $0$ or $1/(d+1)$. A signed product with arbitrary integer exponents has valuations $H/d$ and $H/(d+1)$, where $H$ is the sum of the exponents on even-$a$ marks. These cannot be the two displayed values for $d>2$. This rules out representing the exact transported values $S(y_F)$ and $S(y_G)$ by the same signed expression in primitive marks.

If a shared nonzero rational scalar is allowed, its valuation cancels in the difference. The representation then requires

\[
H=\frac{d(d+1)}3
\quad\text{or}\quad
H=(1/3-2r)d(d+1),
\]

respectively. Either case needs at least $d(d+1)/3$ even-$a$ mark occurrences counted with absolute multiplicities. In the first case the scalar must have valuation $(2-d)/3$. Allowing nonprimitive marks only adds a shared rational scalar after primitive normalization. The bound applies to exact transport. Multiplying by separate field squares can change the two prescribed valuations.

## Degree bounds for a common rational substitution

Suppose one wants $y_F=U(\alpha)$ and $y_G=U(\beta)$ for a common rational function $U=A/B$ over $\mathbb Q$. If $A,B\in\mathbb Z_2[X]$ and $B(0)$ is odd, then the denominator has valuation zero in both fields. The negative-valuation branch for $y_F$ disappears. Write $i$ for the first index of an odd coefficient of $A$. An evaluation with valuation below one has valuation $i/d$ in the first field and $i/(d+1)$ in the second field, since a unique least term has that valuation. The required values force $i=d/2=(d+1)/3$, possible only for $d=2$. Thus polynomial substitutions over $\mathbb Z_2$ and rational substitutions regular at zero modulo two fail independently of the mark restriction.

For arbitrary rational coefficients, a lowest-term estimate gives a degree obstruction. For a nonzero polynomial $P=\sum_j p_j X^j$ put

\[
\mu_e(P)=\min_{j:p_j\ne0}\bigl(v_2(p_j)+j/e\bigr).
\]

This is the actual evaluation valuation whenever the least terms do not cancel. Also

\[
0\le\mu_d(P)-\mu_{d+1}(P)\le \frac{\deg P}{d(d+1)}.
\]

If all four evaluations of $A,B$ at $\alpha,\beta$ attain their least-term bounds, the difference $v_2(y_F)-v_2(y_G)$ therefore lies in

\[
\left[-\frac{\deg B}{d(d+1)},\,\frac{\deg A}{d(d+1)}\right].
\]

The first branch requires $\deg A\ge d(d+1)/6$. The second requires $\deg B\ge(r-1/6)d(d+1)$. If both degrees are below $d$, there can be no equal lowest terms because two exponents differ by less than $d$ and the coefficient valuations are integers. Since admissible $d>2$ starts at eight, both degree requirements are then impossible. Any common rational substitution thus has maximum degree at least $d$, and those below the branch-specific quadratic thresholds must use cancellation at two.

In particular the monomial substitution $X\mapsto X^k$, $k>1$, is already excluded. For that substitution, matching the shared arguments as integers would also require $m^k=M=(cn)^2+1$, impossible by the elementary difference of squares when $k$ is even and by Lebesgue's theorem when $k$ is odd. [Lebesgue's original proof](https://www.numdam.org/item/NAM_1850_1_9__178_0/)

## The automatic polynomial resists cubic composition

Write the canonical polynomial of degree $d+1$ as

\[
G=X^d(X+1-m)+D(X),\qquad
D=\sum_{i<d} a_iX^i,\qquad |a_i|\le2m .
\]

On $|X|=4$, the main term has magnitude at least $4^d(m-5)$ and $|D|<(2/3)m4^d$. On $|X-(m-1)|=4$, the main term has magnitude $4|X|^d$ and $|D|<2m|X|^d/(m-6)$. For $m>15$, Rouché's theorem gives $d$ roots inside the first circle and one inside the second. That last root is real by conjugation and exceeds $m-5$.

Suppose $G=H(P)$ over $\mathbb C$ with $\deg H,\deg P\ge2$, and write $k=\deg P$. The $k$ roots of $P(X)=t$ have the same sum for every root $t$ of $H$, by the coefficient of $X^{k-1}$. The group containing the large real root has sum of absolute value greater than $m-5-4(k-1)$. Every other group has sum of absolute value less than $4k$. These bounds are disjoint for $m>4d+5$, since $2k\le d+1$. The scheduled $m$ satisfies this inequality for large $d$, so its canonical $G$ admits no such polynomial composition.

A candidate cubic-side substitution $y_G=P(\beta)$ therefore cannot have polynomial degree $k=(d+1)/3$ for growing $d$. The divisibility $G\mid G_0(P)$ would force equality up to a scalar at that degree, whereas smaller degrees cannot give divisibility at all. The same argument rules out $y_G=A(\beta)/B(\beta)$ with $\deg A=k$ and $\deg B\le k-2$. At that degree the three polynomials $A-tB$, for the three roots $t$ of $G_0$, would partition the roots of $G$ and have the same top two coefficients, giving the same contradiction.

The Pell parameters still recognize and factor this input family in polynomial bit complexity. The obstructions address transporting its square identities into the consecutive-degree pair. A newly designed square relation for the automatic pair, with ordinary marks in the one-third box and a productive modular split, remains open here.
