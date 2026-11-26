# Asymmetric terminal cutoffs in the charged KeyBreak lattice model

Allow different algebraic and rational smoothness cutoffs and allow the last incoming label to be on either side. With the existing private field height, rectangular proposal law and full per-request terminal charge, neither change lowers the exact limiting coefficient \(C_*\) of the sparse schedule. A full prebuilt triangular reconciliation of the larger coordinates also meets the same obstruction. [Private and terminal cost floor](keybreak-sparse-dependency.md#exact-limiting-coefficient) · [Public identity rows](keybreak-public-pivot-budget.md)

## The charged terminal box

Write \(H=(\log N)^{1/3}(\log\log N)^{2/3}\) and \(D=(\log N/\log\log N)^{1/3}\). All work coefficients are in \(H\) units. Let \(a,r>0\) be the algebraic and rational cutoff coefficients, and set \(b=\max(a,r)\), the exponent of the materialized factor-base size. Use degree \(d\sim\delta D\), coordinate size \(\exp((v+o(1))H)\), incoming prime scale \(\exp((y+o(1))H)\), and aggregate inverse-density coefficient \(s\). The existing separate norm heights and the positive-mean ledger give the relaxed constraints
\[
s\ge \frac{1}{3\delta r}+\frac{A+\delta v}{3a},\qquad
2v\ge y+s,\qquad C\ge b+s.
\]
The first inequality uses the rational height coefficient \(1/\delta\) and algebraic coefficient \(A+\delta v\) on the \(DH\) scale. Dividing out one specified incoming prime changes only the lower-order term on that scale, whichever side contains the prime. The second inequality counts the proposal lattice of index \(\exp((y+o(1))H)\). The third charges a capped uniform search for each of \(\exp((b+o(1))H)\) requests. For a rational incoming prime these equations specify the putative counterpart of the source's algebraic proposal law. Establishing the rational conditional supply is unnecessary for this relaxation. [Existing proposal budget](keybreak-public-pivot-budget.md#work-under-the-same-triangular-proposal-law)

The private ledger uses \(u^2=2/(3\kappa\delta)\), \(v_0=\alpha/(2\kappa)\) and \(\alpha\ge1/2\). Consequently
\[
A=\frac{1+2v_0}{\delta}\ge\frac1\delta+\frac{3u^2}{4},
\qquad C\ge b+p(u),\qquad p(u)=\frac{4}{9u^2}+\frac{2u}{3}.
\]
For any candidate \(C\le C_*<2.155\) the private charge alone gives \(C>2b\). Indeed, AM–GM gives \(p(u)\ge(4/3)^{1/3}>1.10>C/2\).

Eliminate \(v\) to obtain
\[
s\ge \frac{A+\delta y/2+a/(\delta r)}{3a-\delta/2}.
\]
The denominator must be positive for a feasible box. When \(y\ge b\), increasing both cutoffs to \(b\) only decreases the two losses in the original inequality. Substitution gives the original terminal constraint
\[
6b(C-b)\ge\frac{3u^2}{2}+\frac4\delta+\delta C
\ge\frac{3u^2}{2}+4\sqrt C.
\]

## An incoming label below the larger cutoff

For an algebraic incoming label the minimal legal scale is \(y\ge a\). The only case left is \(a<b=r\). Replacing \(y\) by \(a\) relaxes the bound for \(s\). The resulting function
\[
s\ge \frac{A+a(\delta/2+1/(\delta b))}{3a-\delta/2}
\]
is strictly decreasing in \(a\) over the feasible interval, since the numerator of its derivative is \(-3A-(\delta/2)(\delta/2+1/(\delta b))\). Its value at \(a=b\) is the same symmetric bound.

For a rational incoming label the remaining case is \(r<b=a\) with \(y\ge r\). Substitute \(y=r\) and \(s\le C-b\) to get
\[
6b(C-b)\ge\frac{3u^2}{2}+\frac{2(1+b/r)}{\delta}+\delta(C-b+r).
\]
The last two terms are at least \(2\sqrt{2(1+b/r)(C-b+r)}\). With \(t=r/b\le1\),
\[
(1+1/t)(C-b+bt)-2C=(1-t)\bigl((C-b)/t-b\bigr)\ge0
\]
by \(C>2b\). The original terminal constraint follows again, now with strict loss in this comparison if \(r<b\). Its stationary lower certificate with the private constraint excludes \(C<C_*\). Symmetric limiting schedules approach \(C_*\), so the obstruction is sharp in this relaxation. [Exact stationary certificate](../formal/cogentic/Cogentic/RandomizedStationaryFloor.lean)

## Full prebuilds and selective reconciliation

For a full triangular prebuild, consider monotone successive cutoff pairs that retain all rows in the two prefixes at each step. If an original cutoff exceeds the final \(b\), the last stage that makes both cutoffs at most \(b\) eliminates an incoming prefix band above \(b\). When that band supplies \(\exp((y+o(1))H)\) pivot labels at scale \(y\ge b\), its independent uniform searches cost \(y+s\ge b+s\). A complete scan of its rectangular box costs \(2v\ge y+s\) under the same mean guard. If the main terminal box already uses cutoffs at most \(b\), its own charged requests meet the preceding terminal obstruction. A prebuild restricted to incoming scales below \(b\) provides no relief from either charge.

A small fixed pool of selected rational primes also yields a marginal counting check. Let \(X=\exp((R+o(1))DH)\) and allow all primes through \(\exp((b+o(1))H)\) plus any set of at most \(\exp((b+o(1))H)\) additional primes. Uniformly in the set, at most \(X\exp((-R/(3b)+o(1))H)\) positive integers up to \(X\) are supported on the allowed primes. For fixed \(\varepsilon>0\), enlarge the ordinary base through \(\exp((b+\varepsilon)H)\) and apply Rankin with exponent \(1-(\log D-2\log\log D)/((b+\varepsilon)H)\). The added primes above this cutoff contribute at most \(\exp(({-\varepsilon}+o(1))H)\) to the log of the Euler product. The base contributes \(o(H)\) by the prime harmonic upper bound. Let \(\varepsilon\) tend to zero after the input limit. [Rankin estimate in the KeyBreak scales](keybreak-private-shape-work.md)

This last count concerns the entire interval. An adapted pool can be correlated with the particular sparse values \(Qa-rb'\) from the chosen field and lattice. The count alone gives no usable lower bound on the number of distinct delayed requests in that setting. A proposal law with cheaper bulk pivots, or a supply theorem showing that a small adapted set of pivots supports the retained private rows, changes the charged constraints.
