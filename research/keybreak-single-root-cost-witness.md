# Half-width cost with a single-root congruence guard

Use the half-width abstract charges with coefficient-width multiplier \(\chi\), and impose \(\chi v_0>y_1\) and \(\chi v_0>2v_1\) for the single-root and interior pair guards. At \(\chi=151/100\) a rational 4096-interval grid has every charge below \(2.0100\). With \(\chi>3/2\) tending to \(3/2\), the abstract infimum tends to \(2.009433036410336\ldots\). These statements use the reduced guard list as a premise. [Definitions and full charge formulas](keybreak-narrow-cost-witness.md)

## Rational 4096-interval grid

Use exact decimals
\[
(\delta,\kappa,\beta,\alpha)=(1.4107162,1.4612196,.66889243,.50000001),
\qquad
(\lambda_T,\lambda_H,\eta,s)=(1.555,1.67,10^{-8},10^{-7}).
\]
The same rounded stationary knots and rational square-root upper bounds give \(h=.568691581329\). The following are strict rational upper bounds. The two algebraic square-root inequalities were checked by squaring their positive residuals.

| Charge | Upper bound |
|---|---:|
| Raw private slots | 2.007317094 |
| Staged screening | 2.009928951 |
| Top raw | 1.925243911 |
| High raw | 1.993096863 |
| Low raw | 2.009929108 |
| Top algebraic | 1.997314232 |
| High algebraic | 1.905366970 |
| Low algebraic | 1.759524015 |
| Characters | 1.884094854 |
| Sparse solve and extraction | 1.887234775 |

The weights are positive with \(W/M<1.549\). The low slope and ratios satisfy \(L>1\), \(\lambda_L>\lambda_H>\lambda_T>3/2\), and \((\lambda_L-1)L\beta>A_+\). The defining equations give \((\lambda_L-L)\beta-A_+=\eta\) and \((2L-1)\beta-\lambda_L/3-R/(3\beta)=2\eta\). At every squared knot the parent, box and child obey \(0<y_i<v_i<p_i<1\), \(2v_i>p_i\), \(y_i\le y_1\), and \(1.01y_i-.49(1+v_i-p_i)<-.1\). Also \(0<2v_0<1\), \(0<\chi v_0<1\), and the two margins \(\chi v_0-y_1\) and \(\chi v_0-2v_1\) both exceed \(.148\). The bottom endpoint margin \(.49(A_0+L\beta)-1.01R\) exceeds \(.20\). The progression margin \((15/32)(A_0+L\beta)-(33/32)R\) exceeds \(.176\). [Interior progression and pair estimates](keybreak-narrow-interior-guards.md)

## Continuum infimum and approach by fixed grids

Write \(p(u)=2/(9u^2)+2u/3\) and \(U=3\chi/4\). After optimizing the degree at \(\delta=2/\sqrt C\) the necessary inequalities are
\[
b+p(u)\le C,\qquad 6b(C-b)\ge Uu^2+4\sqrt C.
\]
The tangent proof for the wider model applies verbatim with this positive \(U\). To certify the stationary point, set \(z=u^3\), \(P=2/9+2z/3\), \(D=2/3-4/(9z)\), and \(F=2P+Uz/(3D)\). Isolate the zero of the numerator of \((6P(F-P)-Uz^2)^2-16z^2F\) in the interval below and recover \(C=F/u^2\), \(b=(F-P)/u^2\). Exact algebraic-real comparisons verify uniqueness in each interval, both unsquared equalities, and \(0<2b<C\).

| \(\chi\) | Isolating interval for \(z\) | Strict enclosure for \(C\) |
|---|---|---|
| \(151/100\) | \((.183,.185)\) | \((2.00991976864606,\ 2.00991976864608)\) |
| \(3/2\) | \((.184,.185)\) | \((2.00943303641033,\ 2.00943303641034)\) |

At both reconstructed points, fix \(\lambda_T=1.555\) and \(\lambda_H=1.67\), \(\alpha=1/2\), \(\eta=s=0\). The low raw and continuum staged charges equal \(C\). Exact comparisons give all other public and solve charges below \(2\), positive single-root and interior pair margins, strict low ratio ordering, \(L>1\), \((\lambda_L-1)L\beta>A_0\), both strict endpoint and progression bounds, and limiting \(W/M<2\). The worst top endpoint guard is at the last knot because the child and \(p_i-v_i\) increase with the squared knot.

For any prescribed excess over the stationary budget, take a sufficiently fine fixed grid approximating the continuum gate and total weight. Then take sufficiently small positive perturbations of \(\alpha-1/2,\eta,s\), and approximate the remaining coordinates by rationals. The formulas for \(\lambda_L,L\) produce the required strict low mean and cutoff identities. The grid's positive weight criterion holds because \(M=2/(9u^2)>u/3\) at both points. At \(\chi=3/2\), one may also move \(\chi\) to a fixed rational strictly above \(3/2\) by a sufficiently small amount, preserving the given budget. All these choices are fixed before taking the input limit. Conversely the inequalities for \(\chi>3/2\) imply those at \(\chi=3/2\), giving the same limiting lower bound. [Tangent proof](keybreak-narrow-cost-witness.md#exact-limiting-envelope) · [Finite-grid convergence](keybreak-optimal-finite-knots.md)

The certificate uses the existing abstract charges. Integer allocation and transition checks, and the analytic transfer at these coefficient widths under the reduced guard list, are outside its scope.
