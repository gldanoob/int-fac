# Terminal mark degree at the short-square width

The short-square schedule has limiting private width \(\theta_0=2/3\) and cost \(C_*=2.073778424966\ldots\). In the ordinary rectangular Dickman ledger with the same private field, no fixed terminal mark degree \(k\ge2\) improves this limit, even allowing unequal rational and algebraic cutoffs and either side as the incoming label. The obstruction does not rely on the old private inequality \(C>2b\), which need not hold across the short-width parameter region. [Short-square limit](keybreak-lattice-limit.md) · [Terminal mark heights](keybreak-higher-degree-terminal-height.md)

## Exact elimination in the ordinary ledger

Use private charge \(C\ge b+p_\theta(u)\), \(p_\theta(u)=4\theta/(9u^2)+2u/3\). The field height coefficient is at least \(A=1/\delta+3u^2/4\) on the \(DH\) scale. In a primitive degree-\(k\) coefficient box of side exponent \(v\), grant the usual index-\(q\) proposal exponent \((k+1)v-y\) at incoming prime exponent \(y\). Write \(a,r>0\) for the algebraic and rational cutoff exponents, \(b=\max(a,r)\), and \(s\) for the aggregate reciprocal-density exponent. The model constraints are
\[
s\ge\frac{k}{3\delta r}+\frac{kA+\delta v}{3a},\qquad
(k+1)v\ge y+s,\qquad C\ge b+s.
\]
These are assumptions of the charged box model. In particular, the height theorem supplies no smooth density or positive mean at a specified label.

For \(y\ge b\), increase both cutoffs to \(b\) and take \(y=b\). If the incoming label is algebraic and \(y\ge a<b=r\), first take \(y=a\). The bound for \(s\) after eliminating \(v\) is
\[
\frac{kA+a(k/(\delta b)+\delta/(k+1))}{3a-\delta/(k+1)},
\]
decreasing in \(a\) wherever the denominator is positive. Setting \(a=b\) thus also weakens this case to equal cutoffs. The terminal inequality at equal cutoffs is
\[
6b(C-b)\ge \frac{3k}{2}u^2+\frac{4k}{\delta}
                     +\frac{2\delta C}{k+1}
 \ \ge\ \frac{3k}{2}u^2+4\sqrt{\frac{2kC}{k+1}}. \tag{1}
\]
The two radix contributions are both \(k/\delta\) before the factor of two. The earlier [higher-degree comparison](keybreak-higher-degree-terminal-budget.md) uses the weaker \(2(k+1)/\delta\) term, which suffices for its obstruction but is not the exact symmetric elimination for \(k>1\).

For a rational incoming label take \(y=r=tb<b=a\), \(0<t\le1\), and write \(P=b(C-b)\). The two \(\delta\)-terms become \(2k(1+1/t)/\delta+2\delta(C-b+bt)/(k+1)\). Their infimum over \(\delta,t\) is \(4\sqrt{2kC/(k+1)}\) if \(b\le C/2\), and \(4\sqrt{k(C+2\sqrt P)/(k+1)}\) if \(b>C/2\). Indeed the product apart from \(k/(k+1)\) is \(C+bt+(C-b)/t\), minimized at \(t=\min(1,\sqrt{(C-b)/b})\).

The case \(b>C/2\) can be reduced to equal cutoffs as well, by replacing \(b\) with \(C/2\). The function \(6P-4\sqrt{k(C+2\sqrt P)/(k+1)}\) is convex on \([0,C^2/4]\) and negative at zero. If it is at least the strictly positive \(3ku^2/2\) at some \(P\), the convex endpoint bound forces that inequality at \(C^2/4\). The replacement also relaxes the private charge. Thus the sharp feasibility test of this relaxed model is to take \(b=\min(C/2,C-p_\theta(u))>0\) for some \(u>0\) and impose (1) after minimizing over \(\delta\). Conversely, when this test holds, equal cutoffs, \(v=C/(k+1)\) and \(\delta=\sqrt{2k(k+1)/C}\) realize the relaxed constraints. They need not satisfy the other constraints of a full schedule.

Already omitting the positive private-height term in (1) gives the lower bound \(C^3\ge128k/[9(k+1)]\), or \(C\ge2.11653\ldots\) for \(k=2\) and \(C\ge2.20128\ldots\) for \(k\ge3\). These exclude improvement at the short-square limit without numerical stationarity or any other work cost. Increasing \(\theta\) only tightens the charge. Including the private height and optimizing at \(\theta_0\) gives the following numerical values for the exact relaxed test.

| \(k\) | Approximate least feasible \(C\) |
|---:|---:|
| 1 | 2.0737784 |
| 2 | 2.3263467 |
| 3 | 2.4668713 |
| 4 | 2.5663665 |
| 5 | 2.6452528 |

For this table, at fixed \(C\) maximize \(6b(C-b)-3ku^2/2\) in \(u\), then solve for equality in (1). This is a one-dimensional strictly concave maximization on \(p_{\theta_0}(u)<C\): the term \(6b(C-b)\) is a concave nonincreasing function of \(p_{\theta_0}(u)\), and \(p_{\theta_0}\) is convex.

## What a structural discount would need to change

For comparison only, replace the usual rational height \(k/\delta\) by \(R/\delta\), the algebraic height by \(K/\delta+3J u^2/4+\delta v\), and the box dimension \(k+1\) by \(\nu>0\). These symbols specify a conditional model; they do not supply an arithmetic mechanism for changing any of these charges. At equal cutoffs the test is
\[
6b(C-b)-3J u^2/2\ \ge\ 4\sqrt{(K+R)C/\nu}.
\]
At \(C=C_*,\theta=\theta_0\), keeping \(J=k,\nu=k+1\), the maximum permissible combined radix charge \(K+R\) for this symmetric test is approximately \(2.57978,2.55060,2.37735\) for degrees \(3,4,5\), respectively. The ordinary charges are \(6,8,10\).

If only the rational height can change, allowing a rational incoming label at a smaller cutoff helps more. At fixed \(u,b\) put \(s=C-b\), \(W=6bs-3J u^2/2\), and \(L=\nu W^2/16\), taking only \(W>0\). The relaxed feasibility condition for a rational incoming cutoff \(tb\) is exactly
\[
R\ \le\ t\bigl(L/(s+bt)-K\bigr),\qquad 0<t\le1.
\]
The right side is concave in \(t\), with maximum on \([0,1]\) at \(\max(0,\min(1,(\sqrt{Ls/K}-s)/b))\) for \(K>0\). The zero endpoint describes a limit and is not a positive cutoff. Numerical maximization over the remaining private region gives a maximum \(R\) near \(0.18986\) for degree three and \(0.00603\) for degree four with \(K=J=k,\nu=k+1\) at \(C_*\). These are numerical model triggers, not certified supply thresholds.

An exact conditional cubic example below \(C_*\) uses \(C=2.06\), \(R=.1\), \(K=J=3\), \(\nu=4\), \(u=.615\), \(b=.86\), \(t=.22\), \(\delta=3.15\), \(v=.346\), and \(s=1.19\). The private charge is below \(2.054\), the aggregate smoothness model loss below \(1.179\), the volume \(4v=1.384\) exceeds \(tb+s=1.3792\), and \(b+s=2.05\). Thus even the favorable cubic calculation requires a radical change from its ordinary rational height \(3/\delta\), while preserving the full four-coordinate proposal exponent at the small rational cutoff. The [uniform rational height proof](keybreak-higher-degree-terminal-height.md) excludes that height discount for ordinary marks, even when a mark is selected from the full fixed-height box after seeing the field. A different input or mark construction, or a density advantage beyond its Dickman height charge, would be needed.
