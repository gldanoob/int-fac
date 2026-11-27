# Higher-degree terminal marks in the charged KeyBreak model

Under the standard rectangular smoothness ledger with the existing private field, primitive terminal marks of any fixed degree \(k\ge2\) rule out \(C\le2.177\). This grants optimistic proposal supply and free polynomial-time access to the necessary ideal labels, while charging all terminal requests to one input. The linear limit is \(C_*\approx2.1546302153\). [Linear limit and private constraints](keybreak-sparse-dependency.md#exact-limiting-coefficient) · [Asymmetric linear ledger](keybreak-asymmetric-terminal-budget.md)

## Norm and proposal scales

Put \(D=(\log N/\log\log N)^{1/3}\) and \(H=D\log\log N\). Use a field polynomial \(F\) of degree \(d\sim\delta D\) with coefficient height \(\exp((A+o(1))DH)\). The private construction charges \(A\ge1/\delta+3u^2/4\) and a work coefficient of at least \(b+p(u)\), where \(p(u)=4/(9u^2)+2u/3\) and \(b\) is the larger terminal factor-base exponent in \(H\) units.

Write the radix as \(m=r_0/Q\), with \(r_0,Q\asymp M\), \(\log M\sim DH/\delta\), and \(m\) bounded. Let \(P(X)=\sum_{i=0}^k c_iX^i\) be primitive of exact degree \(k\), with \(|c_i|\le W=\exp((v+o(1))H)\). The integral rational value is \(G_k(P)=Q^kP(r_0/Q)\). At a degree-one label \((q,s_0)\) the algebraic condition is \(P(s_0)=0\bmod q\). For a rational incoming prime \(q\nmid Q\), use \(P(r_0/Q)=0\bmod q\). The ordinary identity is \(1=(Q^k/G_k(P))\psi(P(\theta))\bmod N\), subject to the unit checks for evaluation.

The rational height is at most \((k/\delta+o(1))DH\). The source sampling of \(r_0\) gives the matching leading height with high probability, simultaneously on the full mark box. [Uniform height estimate](keybreak-higher-degree-terminal-height.md) The Mahler measures, bounded by the Euclidean coefficient norms, give
\[
|\operatorname{Res}(F,P)|\le M(F)^k M(P)^d
 \le \exp((kA+\delta v+o(1))DH).
\]
The resultant inequality is an upper bound. Using its exponent to price smoothness is an assumption of the box ledger. Smaller-resultant families or better conditional smoothness need a separate analysis. Removing one prescribed prime of logarithm \(O(H)\) changes neither leading coefficient.

The coefficient box has at most \((2W+1)^{k+1}\) marks. The volume exponent \((k+1)v\) is attainable before the root condition even with primitive coefficients, by choosing \(c_0,c_1\in[1,W]\) coprime and the rest independently with \(c_k\ne0\). Averaged over residues \(s_0\bmod q\), the number of primitive proposals is at most \(k(2W+1)^{k+1}/q\), because a primitive \(P\) has nonzero reduction with at most \(k\) roots. The average gives neither a pointwise bound nor a lower supply at field roots. For example \(s_0=0\) can give a larger slice when \(q>2W\). We grant the standard index-\(q\) volume, efficient proposal generation, and the ordinary Dickman charges. Unequal widths decrease the volume at a fixed maximum width under these charges.

## Elimination including asymmetric cutoffs

Let \(a,r>0\) be the algebraic and rational cutoff exponents, \(b=\max(a,r)\), \(y\) the incoming prime exponent, and \(s\) the reciprocal smoothness exponent. The relaxed constraints are
\[
s\ge\frac{k}{3\delta r}+\frac{kA+\delta v}{3a},\qquad
(k+1)v\ge y+s,\qquad C\ge b+s,\qquad C\ge b+p(u).
\]
Putting \(\lambda=\delta/(k+1)\) gives \(s\ge[kA+ka/(\delta r)+\lambda y]/(3a-\lambda)\), where feasibility requires a positive denominator. If \(y\ge b\), enlarge both cutoffs to \(b\) and decrease \(y\) to \(b\). If the incoming label is algebraic and \(a<b=r\), put \(y=a\). The resulting bound \([kA+a(k/(\delta b)+\lambda)]/(3a-\lambda)\) decreases with \(a\), so setting \(a=b\) also weakens the bound. Both cases give
\[
6b(C-b)\ge\frac{3k}{2}u^2+\frac{2(k+1)}{\delta}+
       \frac{2\delta C}{k+1}\ge\frac{3k}{2}u^2+4\sqrt C. \tag{1}
\]
For a rational incoming label with \(r=tb<b=a\), put \(y=r\). The two degree-dependent terms involving \(\delta\) instead become \(2(1+k/t)/\delta+2\delta(C-b+bt)/(k+1)\). For \(C\le2.177\) the private constraint gives \(C>2b\) since \(p(u)\ge(4/3)^{1/3}>1.1\). The identity
\[
(1+k/t)(C-b+bt)-(k+1)C=(1-t)\bigl[k(C-b)/t-b\bigr]\ge0
\]
gives the same last bound of (1) by AM–GM.

The symmetric right side before AM–GM is \(3u^2/2+4/\delta+\delta C\) at \(k=1\), \(3u^2+6/\delta+2\delta C/3\) at \(k=2\), and \(9u^2/2+8/\delta+\delta C/2\) at \(k=3\). Rescaling to \(\delta_{\rm eff}=2\delta/(k+1)\) absorbs the degree-dependent terms involving \(\delta\). The remaining surcharge over the linear constraint is \(3(k-1)u^2/2\).

## Uniform gap

The existing lower certificate excludes the linear constraints at \(C_0=2.154630\). If \(C\le C_0\), (1) gives the linear terminal constraint at \(C\) with degree parameter \(2/\sqrt C\). This same parameter works at \(C_0\), since \(6b(C-b)-(2/\sqrt C)C\), viewed as a function of the budget with parameter fixed, has positive slope by \(6b\ge4/\sqrt C\). The private bound also persists.

For \(C_0<C\le2.177\), put \(\Delta=C-C_0\) and \(b'=b-\Delta>0\), using \(b\ge2/(3\sqrt C)\). The private constraint persists at \((C_0,b')\). The terminal product falls by \(6\Delta(C-b)\le6\Delta C\), while \(4\sqrt C\) decreases. The degree surcharge for \(k\ge2\) is at least \(2/(3C)\), since \(4/(9u^2)\le C\). The exact rational check
\[
9(2.177-2.154630)(2.177)^2=0.95416910757<1
\]
shows that the surcharge exceeds \(6\Delta C\). The new point thus satisfies the forbidden linear constraints at \(C_0\). [Certified linear obstruction](../formal/cogentic/Cogentic/RandomizedScheduleFloor.lean)

The comparison leaves open proposal laws or smoothness estimates for selected small-resultant strata, changes to the private field height, and shared terminal work with a proved coverage and cost bound.
