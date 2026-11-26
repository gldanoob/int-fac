# Counting rough balanced inputs in the elliptic four-mark family

For every fixed finite set of excluded primes and every fixed balance ratio greater than one, the rank-one elliptic family gives at least $c\sqrt{\log X}$ distinct balanced inputs $N\le X$ for all sufficiently large $X$. For every fixed $0<\varepsilon<2$, at least $(\log X)^{\varepsilon/4-o(1)}$ of the inputs up to $X$ can additionally be chosen with least prime factor greater than $(2-\varepsilon)\log\log X$. The constants and large-$X$ thresholds are effective. Both factors in the fixed four-mark split inherit the avoidance bound. [Elliptic family and its square comparison](cogentic-elliptic-mark-cycle.md)

## Real returns and distinct integers

Use the curve
\[
 E\colon Y^2=(X+204)(X+1496)(X+264),\qquad
 P=(8976,-942480)
\]
and the inverse chart $m=51-8976/X$, $y=-8976Y/X^2$. The seed is $m=50,y=105$. The point $P$ is nontorsion since its reduced orders are 10 and 16 at the good primes 13 and 23. Their 2-primary parts differ, while reduction is injective on prime-to-residue-characteristic torsion. The three rational roots supply all of $E[2]$. [Curve and normalization](cogentic-elliptic-mark-cycle.md#a-point-of-infinite-order)

Fix a balance ratio $C>1$ and choose a closed real neighborhood of the seed inside the branch $y>0$, with $F(m)>0$, for which the two normalized factors have ratio between $C^{-1}$ and $C$. The separate signs in the finite-adic normalization are fixed by taking $y$ close to $+105$ at the exceptional places. In the notation of the family, $A_h=5v^2$, $B_h=5z^2$ with $v,z>0$, and $D_+=-zS_h+vb^2$, $D_-=-zS_h-vb^2$. Then $D_+/626$ and $D_-/620$ are coprime positive integers with product $N=F_h/485150$, and each is asymptotic to $b^3$ near the seed. The fixed real neighborhood can be chosen by polynomial inequalities and the positive square roots of $A(m)/5$ and $B(m)/5$. [Factor signs and coprimality](cogentic-elliptic-mark-cycle.md#the-two-balanced-factors)

In the identity component $E(\mathbb R)^0\simeq\mathbb R/\mathbb Z$, choose a symmetric arc about zero whose translate by $P$ is contained in that real neighborhood. Divide the circle into $s$ equal half-open arcs short enough that the difference of two points in any one arc lies in the chosen symmetric arc. This $s$ depends only on the chosen real neighborhood. For every $Q\in E(\mathbb R)^0$ and every integer $J\ge1$, put $0,Q,\ldots,JQ$ into those $s$ bins. A largest bin has at least $(J+1)/s$ indices. Subtract its smallest index from the others to obtain at least $(J+1)/s-1$ distinct positive return indices $j\le J$. This lower bound is uniform in $Q$, including steps that vary with the finite prime cutoff. An effective choice of $s$ follows from the real elliptic integral on the fixed curve, or from integrating its invariant differential on a compact neighborhood of $P$ and comparing with its finite positive period.

Write $m(nP)=u/b$ in lowest terms with $b>0$. The coordinate height changes by $O(1)$ under the fixed Möbius map from $X$ to $m$. With the normalization $h(X(Q))=\widehat h_x(Q)+O_E(1)$, the canonical height satisfies $\widehat h_x(nP)=n^2\widehat h_x(P)$ and $\widehat h_x(P)>0$. On the closed neighborhood, $m$ stays bounded and $F(m)$ is bounded above and away from zero. Thus
\[
 \log N(n)=6n^2\widehat h_x(P)+O(1)
\]
with a uniform error over all accepted indices, independent of the prime cutoff. The values are strictly ordered by $n$ beyond a fixed index because the gaps between successive main terms eventually exceed twice the error. After removing finitely many indices, both factors exceed one. There is a computable $c_0>0$ for which every accepted index $n\le c_0\sqrt{\log X}$ gives $N(n)\le X$. For effectiveness one can use the explicit height-difference bound and bounded real values of $F(m)$. A strictly positive lower bound for $\widehat h_x(P)$ is obtained by applying the same height-difference estimate to successive doublings and dividing by the square of their multipliers. [Canonical heights](https://www.math.brown.edu/johsilve/Wyoming/WyomingEllipticCurveJune7.pdf#page=80) · [Explicit height-difference bounds](https://doi.org/10.1090/S0025-5718-1990-1035944-5)

## Prime avoidance and the size of the common step

Fix once and for all the exceptional primes. Include the specified exclusions, the primes of bad reduction of the displayed model, the primes dividing $8976\cdot F(50)$, and the primes dividing the cross-resultant of $A,B$. This set is finite and independent of the growing cutoff. At each such $p$, choose an open subgroup $U_p\subset E(\mathbb Q_p)$ around zero so that $P+U_p$ lies in the local seed neighborhood for the factor normalization. At a sufficiently deep level the local formal group provides such a subgroup, including at bad reduction. It has finite index by compactness. Therefore there is a fixed even integer $M_0$ with $M_0P\in U_p$ for every exceptional $p$. It can be found by testing multiples for membership in the finitely many chosen formal subgroups. The local relative signs are those used in the family proof, so every $n\equiv1\bmod M_0$ has the separate seed valuations of $D_+,D_-$ there. [Local normalization](cogentic-elliptic-mark-cycle.md#recurrence-at-finitely-many-places)

At any other prime $p$ the integral curve has good reduction, $X(P)$ is a unit, and $F(50)=485150$ is a unit. If $nP\equiv P\bmod p$, the chart gives $m(nP)\equiv50\bmod p$ with $b\in\mathbb Z_p^\times$. Then $F_h=b^6F(m)$ and $N$ are units at $p$. Only this first-order reduction condition is needed at the growing set of primes.

For every odd good $p$, write $\#E(\mathbb F_p)=4k_p$. The full 2-torsion forces the order of every element to divide $2k_p$. Indeed a cyclic subgroup contains at most two of the four 2-torsion elements, so its quotient in the abelian group has an element of order two and has even size. By Hasse, $k_p\le(\sqrt p+1)^2/4$. For a cutoff $Y$, put
\[
 L_Y=\left\lfloor\frac{(\sqrt Y+1)^2}{4}\right\rfloor,
 \qquad
 M_Y=2M_0\operatorname{lcm}(1,\ldots,L_Y).
\]
Then $n=1+jM_Y$ preserves the fixed exceptional neighborhoods and returns to $P$ modulo every remaining prime $p\le Y$. The factor $2$ also keeps $M_YP$ in the real identity component. The ordinary prime number theorem gives
\[
 \log M_Y=\psi(L_Y)+O(1)=(1/4+o(1))Y.
\]

## The counts

For a fixed finite exclusion list take a fixed step $M_0$ and apply the real return bound to $Q=M_0P$ and $J=\lfloor(c_0\sqrt{\log X}-1)/M_0\rfloor$. After omitting the finitely many small indices, there are at least $c\sqrt{\log X}$ distinct $N\le X$ in the chosen balance window. There are also at most $O(\sqrt{\log X})$ accepted indices from this rank-one branch, by the same height formula.

For $0<\varepsilon<2$, take $Y=\lfloor(2-\varepsilon)\log\log X\rfloor$. Then
\[
 M_Y=(\log X)^{1/2-\varepsilon/4+o(1)},\qquad
 J=\left\lfloor\frac{c_0\sqrt{\log X}-1}{M_Y}\right\rfloor
   =(\log X)^{\varepsilon/4+o(1)}.
\]
The uniform real return count gives the asserted number of distinct moduli with no prime divisor at most $Y$. Since the least prime is an integer, it exceeds $(2-\varepsilon)\log\log X$ and therefore exceeds $(2-\varepsilon)\log\log N$ as well. All constants in the real count are independent of $Y$. Effective estimates for $\psi$, height and the fixed neighborhoods supply an effective threshold, for instance for the weaker lower count $c_\varepsilon(\log X)^{\varepsilon/8}$. The argument gives rough composite inputs in the stated range. It makes no primality claim for either factor.
