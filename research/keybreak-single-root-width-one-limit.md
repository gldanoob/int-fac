# Scalar limit as the Gaussian width exponent approaches one

With the single-root and interior pair guards, take the top ratio \(\lambda_T=1.43\) and the high ratio \(\lambda_H=1.636\). The half-width scalar model has infimum \(1.9839824118071388229\ldots\) as \(\chi\downarrow1\). At \(\chi=1.01\), a rational 4096-stage witness has every charge below \(1.984578735\). The rate limit uses the balanced top predicates and multiplier-averaged estimates as its analytic premise. [Scalar formulas and grid](keybreak-single-root-subtwo-cost.md) · [Balanced top construction](keybreak-balanced-class-integration.md) · [Multiplier-averaged moment](keybreak-mixed-strip-moment.md)

## Which ratio constraints survive

The original three-root width guard \(\chi v_0>3y_1\) is \(\chi\lambda_T>3\), which gives \(\lambda_T>3/2\) at \(\chi=2\). The single-root guard gives \(\chi\lambda_T>1\), and the interior pair guard gives \(\chi\lambda_T>2\alpha\). At each fixed positive squared knot \(a\), the local ratio \(1+(\lambda_T-1)a>1\) separates the local child from the box. The parent exceeds the box because \(\alpha<1\), and \(2\alpha>1\) gives the area margin. The global child cutoff is attained at the last knot and dominates every other local child cutoff. These are the local replacements for the top inequalities of (H.2). Internally \(L>1\) gives the box separation from \(B\) and the clamped child, while \((\lambda_L-1)L\beta>A_+\) gives the unclamped low box-to-child gap. The high recurrence has asymptotic slope \(\alpha/\lambda_H<1\), and its high box-to-child gap follows from \(\lambda_H>1\). No further \(3/2\) ratio appears in these checks. [Tiered geometry and recurrence](keybreak-tiered-descent.md) · [Source (H.1)–(H.2)](https://crypto.sjtu.edu.cn/factoring.pdf#page=126)

The top parent-versus-child check uses the local child cutoff for that band. The shared internal cutoff can exceed a small top parent, and the internal pass-through rule handles children below its active band. The inequalities \(v_1<v_0<1/2\) and \(y_0<1\) supply the remaining upper box and parent margins of (H.2). The fixed positive knots and the strict logarithmic gaps absorb its constants \(2\), \(4\), and \(33\) at a sufficiently large input. [Local child cutoffs and shared internal recursion](keybreak-narrow-class-integration.md#integer-scales-and-cost)

The finite sampler must use the revised single-root check in place of the printed \(Y_1^3\) check. The one-mark comparison uses \(\chi>1\), with any fixed positive gap and polynomial padding. The balanced multiplier argument uses the same fixed positive gap and allows an angular cutoff exponent smaller than half that gap. The ordinary top proof has its separate width premise \(\chi>3/2\). [Root conditioning and padding](keybreak-root-congruence-scope.md) · [Ordinary top comparison](keybreak-narrow-class-integration.md#which-probability-estimates-change)

## Exact continuum endpoint

Use \(p(u)=2/(9u^2)+2u/3\) and \(U=3/4\) in the two-term envelope
\[
b+p(u)\le C,\qquad 6b(C-b)\ge Uu^2+4\sqrt C .
\]
With \(z=u^3\), \(P=2/9+2z/3\), \(D=2/3-4/(9z)\), and \(F=2P+Uz/(3D)\), the numerator of \((6P(F-P)-Uz^2)^2-16z^2F\) is proportional to
\[
\frac{1681}{144}z^6-\frac{41}{2}z^5+\frac{547}{27}z^4
-\frac{760}{243}z^3-\frac{224}{81}z^2+\frac{256}{729}z+\frac{256}{6561}.
\]
Exact algebraic-real isolation gives one root in \((.2003,.2004)\). Reconstruct \(C=F/u^2\), \(b=(F-P)/u^2\), \(\delta=2/\sqrt C\), and \(\kappa=2/(3u^2\delta)\). The unsquared terminal equality and \(6(C-2b)p'(u)=-2Uu\) hold, with \(0<2b<C\). In particular,
\[
1.9839824118071388228<C<1.9839824118071388230 .
\]
These comparisons give the supporting-tangent lower bound for every \(\chi\ge1\), since increasing \(\chi\) only increases the right side of the terminal inequality. At the reconstructed point the continuum private and low raw costs equal \(C\). With \(\alpha=1/2\), \(\eta=s=0\), all other charges and the nonactive geometry guards have strict room. The limiting weights have \(W/M<1.602\) and \(M>u/3\). Thus positive perturbations of \(\chi-1\), \(\alpha-1/2\), \(\eta\), and \(s\), together with a sufficiently fine fixed rational grid, approach \(C\). [Tangent lower bound](keybreak-narrow-cost-witness.md#exact-limiting-envelope) · [Finite grid convergence](keybreak-optimal-finite-knots.md)

The high raw charge explains the choice of \(1.636\). With \(Q=3\delta b\), the endpoint permits \(\lambda_H\) only up to \((3/\delta)(C-b-(1+v_1)/Q)\), which lies in \((1.6370,1.6371)\). Taking \(\lambda_H=1.64\) instead gives a high raw charge above \(1.9853684\) at \(\chi=1\), and above \(1.9852451\) for the rational \(\chi=1.01\) inputs below. At \(1.636\) the endpoint's high raw charge is below \(1.983475266\).

## Exact fixed grid at \(\chi=1.01\)

Use \((\delta,\kappa,\beta)=(1.4197202620,1.3732142239,.6654900015)\), \(\alpha=.50000001\), \(\eta=10^{-8}\), and \(s=10^{-7}\), all as exact rationals. The 4096-stage grid and rounding rule from the preceding certificates give \(h=.584768315988\). Only the scalar helpers from commit \(\texttt{a5160e2}\) are needed. The charges have these strict rational upper bounds.

| Charge | Upper bound |
|---|---:|
| Raw private slots | 1.981893042 |
| Staged screening | 1.984578735 |
| Top raw | 1.870046172 |
| High raw | 1.983352205 |
| Low raw | 1.984515433 |
| Top algebraic | 1.967323922 |
| High algebraic | 1.910189371 |
| Low algebraic | 1.736012425 |
| Characters | 1.891289814 |
| Sparse solve and extraction | 1.889619279 |

Exact rational checks give positive weights and \(W/M<1.596\), along with \(0<2v_0<1\), \(0<\chi v_0<1\), and \(0<y_2<v_1<y_1<v_0<y_0<1\). They give \(\lambda_L>1.67188>\lambda_H>\lambda_T>1\), \(L>1.05021\), and \((\lambda_L-1)L\beta-A_+>.05587\). The low cutoff and mean margins are exactly \(\eta\) and \(2\eta\). The single-root and interior pair margins both exceed \(.05656\). The bottom endpoint and progression margins exceed \(.19223\) and \(.16116\), respectively. At every top squared knot the parent, box and child are strictly ordered and \(2\tilde v>\tilde p\), and the top rational progression exponent is below \(-1/4\). The internal rational bound \(1.01y_1-.49<-1/4\) holds as well. The two algebraic square-root charges use positive rational residuals whose squares dominate the relevant squared terms.

The finite numbers are scalar bounds. The balanced construction uses its actual enlarged degree in the recurrence, and its fixed degree increment leaves these strict leading margins intact. No concrete rounded allocation or transition replay was used. [Adjusted degree and top predicate](keybreak-balanced-class-integration.md)
