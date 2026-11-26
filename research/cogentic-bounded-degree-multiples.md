# Bounds for bounded-degree fields with freely chosen multiples

Allowing independent values $F(m)=kN$ and $G(m)=\ell N$ does not permit two bounded-degree, small-height fields at a common argument. A separate congruence rules out even one small mark norm on almost all inputs when the argument is centered at a square or cube root of an adaptively scaled input. The second bound allows arbitrary lower coefficients. [Variable-multiple lattice](cogentic-variable-multiple-lattice.md) · [Centered quadratic private norms](cogentic-centered-quadratic-density.md)

## Two low-height fields cannot share the argument

Let $F,G\in\mathbb Z[X]$ have degrees $d,e$ and be coprime over $\mathbb Q$. If both values at any integer $m$ are divisible by $N$, the integral resultant identity gives $N\mid\operatorname{Res}(F,G)$. The Sylvester determinant and Hadamard give

\[
N\le|\operatorname{Res}(F,G)|
\le \|F\|_2^e\|G\|_2^d
\le(\sqrt{d+1}\,H_F)^e(\sqrt{e+1}\,H_G)^d .
\]

This uses no bound on $m$, the two multipliers or their gcds with $N$. When $d,e$ are bounded and $H_F,H_G=\exp(o(\log N))$, the inequality fails for all sufficiently large $N$. If both height logarithms are $O(V)$ on the one-third scale, then $d+e=\Omega(\log N/V)$, provided the degrees are at most polynomial in $\log N$. Distinct irreducible fields meet the coprimality hypothesis.

The same restriction applies when small coefficients follow from the marked values. For degree $d$, suppose $d+1$ pairwise nonproportional primitive marks of height $A$ have homogeneous values of magnitude at most $T$. Their integral evaluation matrix is invertible by interpolation. Cramer's rule gives $H_F\le(d+1)!A^{d^2}T$, since each replaced-column determinant uses one entry bounded by $T$ and $d$ entries bounded by $A^d$. With only $d$ such marks, first interpolate a polynomial $F_0$ of degree at most $d-1$ using the degree-$d$ homogeneous values. Its coefficients are bounded by $d!A^{d(d-1)}T$. Then

\[
F=F_0+s\prod_{i=1}^d(b_iX-a_i).
\]

For $b_i>0$ and $|m|\ge2A$, an evaluated multiple $F(m)=kN$ bounds $|s|$ by $2^d(|k|N/|m|^d+dH_{F_0}/|m|)$. Thus $d$ marks already force small coefficients when $d$ is bounded, $A,T,|k|=N^{o(1)}$, and $|m|\ge N^{1/d-o(1)}$. Two quadratic fields at a square-root base, each with two such marked values, cannot escape the resultant by allowing large coefficients before interpolation.

Even one bounded-degree polynomial of height $X^{o(1)}$ can represent only $X^{(1+\kappa)/d+o(1)}$ distinct integers $N\in[X,2X)$ with a nonzero multiple $F(m)=kN$ and $|k|\le X^\kappa$ for fixed $\kappa\ge0$. The number of coefficient vectors is $X^{o(1)}$. Outside $|m|\le2dH_F$, the leading term gives $|F(m)|\ge|m|^d/2$, so there are at most $X^{(1+\kappa)/d+o(1)}$ possible arguments. Each evaluated nonzero integer has $X^{o(1)}$ divisors by the usual divisor bound. This count is sparse for $\kappa<d-1$ and does not require a centered argument.

## A small mark norm is rare at an adaptive center

Fix $d\ge2$, and let $N\in[X,2X)$. Allow the positive leading coefficient $q$, positive multiplier $k$, offset $j$, and mark coordinates $(a,b)$ to vary over uniform $X^{o(1)}$ bounds, with $b>0$ and $\gcd(a,b)=1$. Set

\[
M=\left\lfloor(kN/q)^{1/d}\right\rfloor,\qquad m=M+j.
\]

The other coefficients of a degree-$d$ polynomial $P$ are unrestricted, subject to $P(m)=kN$. If its homogeneous value at the mark is $r$, then

\[
r\equiv b^d kN\pmod{|bm-a|}.
\]

This is the homogeneous polynomial evaluated with $a\equiv bm$. For fixed $k,q,M,j,a,b$, the possible inputs lie in an interval of length $X^{1-1/d+o(1)}$, from $qM^d/k\le N<q(M+1)^d/k$. The modulus $\delta=|bm-a|$ is at least $X^{1/d-o(1)}$ and coprime to $b$. For each fixed $r$, the congruence puts $N$ in at most one progression modulo $\delta/\gcd(k,\delta)$, also at least $X^{1/d-o(1)}$. Hence one tuple and one value of $r$ cost at most $X^{1-2/d+o(1)}$ inputs.

There are $X^{1/d+o(1)}$ choices for $M$ and only $X^{o(1)}$ remaining parameter tuples. Allowing every integer $|r|\le X^\theta$ gives at most $X^{1-1/d+\theta+o(1)}$ inputs, for any fixed $0\le\theta<1/d$. This applies simultaneously to adaptive choices made after seeing $N$. For absolute norms of $a-b\alpha$, where $\alpha$ is a root of $P$, the homogeneous value is $q$ times the norm, so a subpower leading coefficient preserves the subpower conclusion. In particular a natural square or cube base with such offsets and multipliers has no mark of one-third absolute norm size on a density-one set. The bound says nothing about a large norm whose prime exponents happen to cancel in a relation.

The [exact sanity check](../experiments/cogentic-bounded-degree-multiples.gp) verifies the congruence and resultant inequality for several nonmonic pairs with different evaluated multiples.
