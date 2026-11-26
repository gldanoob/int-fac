# Counting distinct split inputs from independent elliptic points

For every fixed finite prime exclusion set and every fixed relative balance tolerance, the four-mark construction splits at least $c(\log X)^{2/3}$ distinct odd integers up to $X$ for all sufficiently large $X$. Each split has two coprime factors within the chosen ratio of one another. The input-only algorithm uses polynomial bit time on this family. The count is for integers after dividing out the entire seed contribution $485150$. The factors need not be prime. [Four-mark family and its exact split](cogentic-elliptic-mark-cycle.md)

## Independent directions

On $E:Y^2=(X+1496)(X+264)(X+204)$ use the seed $P=(8976,-942480)$ and the following rational points:
\[
 R_1=(-1344,13680),\quad R_2=(-544,9520),\quad R_3=(-280,1216).
\]
They generate a free group of rank three. To check this, take the usual rational two-descent homomorphism to $\mathbb Q^\times/\mathbb Q^{\times2}$ associated to the root $e=-1496$. Its value is $X-e$ away from $(e,0)$ and the identity. At $(e,0)$ use the product of the two differences from the other roots, and at the identity use $1$. For the chord-and-tangent proof, substituting a line into the cubic gives the product of its three root differences from $e$ as the square of the line's value at $e$. When the line goes through $(e,0)$, cancel the linear term $X-e$ before evaluating. The remaining product there is the derivative of the cubic at $e$. A vertical line pairs opposite points with the same class.

The first three points and the two torsion generators $T_1=(-1496,0)$, $T_2=(-264,0)$ give the following representatives.

| Point | Square class |
| --- | --- |
| $R_1$ | $2\cdot19$ |
| $R_2$ | $2\cdot7\cdot17$ |
| $R_3$ | $19$ |
| $T_1$ | $7\cdot11\cdot17\cdot19$ |
| $T_2$ | $7\cdot11$ |

The valuation parities at $2,7,11,17,19$ have binary rank five. Any integral relation among the $R_i$ up to rational two-torsion therefore has all coefficients even and its torsion term zero. Halving gives another relation up to two-torsion, since $T_1,T_2$ span $E[2](\mathbb Q)$. Iteration proves independence. No assertion of saturation is required.

## Many visits to the split neighborhood

Only $R_1,R_2$ are needed for the lower bound. Fix a sufficiently small real neighborhood of $P$ giving positive factors and the desired upper bound on their ratio. Also choose the finitely many local neighborhoods of $P$ needed for the seed valuations and the extra prime exclusions. There is a common integer $M\ge1$ so that $M R_1,M R_2$ belong to open subgroups whose translates by $P$ satisfy all the local conditions. At a finite place the formal group gives arbitrarily small open subgroups; their quotients in the compact elliptic group are finite.

For $0\le i,j\le T$, cover the real points $M(iR_1+jR_2)$ by finitely many fixed cells such that the difference of any two members of a cell is in the desired identity neighborhood. The largest cell contains $\gg T^2$ index pairs. Subtract the indices of any one member from each other member. Translating the resulting points by $P$ gives $\gg T^2$ distinct index pairs $(i,j)$ with $|i|,|j|\le T$, still satisfying every finite-place condition, and with $P+M(iR_1+jR_2)$ in the chosen real neighborhood. Their sextic numerators give positive integers $N=F_h/485150$ and coprime factors by the four-mark identities. Boundedly many pairs could give $N=1$, as also follows from the next estimate.

## Distinct integers in a height shell

Use the canonical height $\widehat h_x$ differing from logarithmic $X$-coordinate height by a bounded amount. The inverse chart to $m$ is a fixed invertible fractional-linear transformation. In the fixed real neighborhood, $m$ is bounded and the sextic value is bounded above and away from zero. The denominator $b$ of $m$ therefore satisfies
\[
 \log N=6\log b+O(1)=6\widehat h_x(P+M(iR_1+jR_2))+O(1).
\]
The constants are uniform on that neighborhood. On the subgroup spanned by the two independent directions the height form is positive definite. For fixed $N$, completing the square gives a translated positive definite binary quadratic form in $i,j$ restricted to an interval of width $O(M^{-2})$. The form itself is fixed. Its center is bounded uniformly for $M\ge1$, since the cross terms with $P$ shift it by $O(1/M)$. [Canonical height theorem](https://www.math.brown.edu/johsilve/Wyoming/WyomingEllipticCurveJune7.pdf#page=80)

Here is an elementary bound uniform in $N$ and $M$. A shell of bounded width in the squared radius, meeting the box $[-T,T]^2$, lies around an ellipse of radius $s=O(1+T)$ in the norm of the fixed form. Bounded radii give $O(1)$ points. For large $s$, divide the ellipse into $O(s^{2/3})$ arcs of length at most $\eta s^{1/3}$ for a fixed small $\eta>0$. Equivalently take angular sectors after a fixed linear change to circular coordinates. The shell in each sector fits in a tangent rectangle of length $O(\eta s^{1/3})$ and width $O(\eta^2 s^{-1/3}+s^{-1})$, by the cosine bound and the shell thickness. Choose $\eta$ so the area in the original integer plane is below $1/2$ for all large $s$. Three noncollinear lattice points span a triangle of area at least $1/2$, so all the points in a sector are collinear. On a unit-speed line the fixed squared norm is $a(t-t_0)^2+b_0$ with $a$ bounded below by the smallest eigenvalue. The preimage of an interval of bounded width has at most two components with uniformly bounded total length. Since lattice points on a line have spacing at least one, each sector contains $O(1)$ points. Thus any one $N$ occurs for at most $O((T+1)^{2/3})$ index pairs.

The visited box gives $\gg T^{4/3}$ distinct integers, and each has logarithm at most $C(1+M^2T^2)$. Take $T=\lfloor c_0\sqrt{\log X}/M\rfloor$ with $c_0$ sufficiently small. For fixed exclusions this proves the stated lower bound. Every input in the resulting family has an input-only certificate search: enumerate $P+iR_1+jR_2$ for signed indices bounded by the binary bit length of $N$ and check the normalized sextic value and the modular gcds. Positive definiteness and the height comparison put the required two unscaled indices within $O(1+\sqrt{\log N})$, so this covers all sufficiently large family members. All point coordinates have polynomial bit length throughout. The algorithm requires neither the generating indices nor the excluded primes with the input. Producing plentiful certificates on a fixed elliptic family leaves their existence for arbitrary inputs open.

## How many inputs can this fixed curve cover?

The growing prime-avoidance step works in both independent directions. In the [rank-one count](cogentic-elliptic-cycle-count.md#prime-avoidance-and-the-size-of-the-common-step), choose the fixed exceptional multiplier to send both directions into all the prescribed open subgroups. For every other good prime up to $Y$, the multiplier kills the entire reduced group. This gives $\log M=(1/4+o(1))Y$ and the same uniform real-cell and shell bounds. Taking $Y=(2-\varepsilon)\log\log X$, for fixed $0<\varepsilon<2$, now gives at least $(\log X)^{\varepsilon/3-o(1)}$ distinct eligible inputs up to $X$ with smallest prime factor exceeding $Y$.

There is also an upper bound even if every rational point of the quartic is available and no real neighborhood is imposed. The exact Sage computation `EllipticCurve([0,1964,0,753984,80568576]).rank(proof=True)` returns 3; PARI independently gives the rank interval $[3,3]$ with `ellrank`. For the fixed irreducible sextic $F$, every primitive pair $(u,b)$ with $b>0$ satisfies $|b^6F(u/b)|\gg_\eta\max(|u|,b)^{4-\eta}$ for each fixed $0<\eta<1$. For $|u/b|$ sufficiently large this follows from monicity. In a bounded interval away from the real roots use a positive lower bound for $|F|$. Near each real root $\alpha$, the other simple-root distances stay bounded below, and Roth's theorem gives $|u/b-\alpha|\gg_\eta b^{-2-\eta}$. The constant in this upper-count argument may be ineffective. [Roth, *Rational approximations to algebraic numbers*](https://doi.org/10.1112/S0025579300000644)

Consequently $N=|F_h|/485150\le X$ implies coordinate height $h(m)=O(1+\log X)$. In the rank-three Mordell–Weil lattice there are $O((1+\log X)^{3/2})$ points in this canonical-height range, by positive definiteness and the bounded height difference. This bounds the number of distinct fixed-cofactor inputs from the entire chart, including parameters outside the seed arc.

More generally, for a fixed signed mark word the rational-square condition, after clearing square factors and denominators, is $y^2=d\prod_{j=1}^k(m-a_j)$ for a fixed nonzero rational $d$ and distinct marks of odd multiplicity. When $k\ge5$, its smooth projective model has genus $\lfloor(k-1)/2\rfloor\ge2$. Faltings's theorem then leaves only finitely many rational parameters for that particular word and twist. Changing the marks, permitting a variable twist, or requiring a square only modulo $N$ gives different conditions. [Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*](https://doi.org/10.1007/BF01388432)
