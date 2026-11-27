# Scalar cost of quadratic marks at the top

Allow primitive quadratic marks only in the top search. Keep the half-width private curve, the field degree, and the linear interior and terminal searches. In this scalar model a genuinely three-dimensional top box gives a continuum budget \(2.001200809613760\ldots\) at field-width multiplier \(2\). At multiplier \(1\) the formal budget is \(1.965545284171044\ldots\). Both admit strict rational finite-grid perturbations from above. These are conditional cost comparisons whose input is the prescribed quadratic-top search and density ledger.

## Substitution in the top ledger

Write \(F\) for the degree-\(d\) field polynomial and \(H_F\) for its coefficient height. A primitive quadratic \(f(X,Y)=aX^2+bXY+cY^2\) of coefficient height \(V\) has rational value of size \(O(M^2V)\) at \((r,Q)\), and
\[
|\operatorname{Res}(F,f)|\le H_F^2 V^d e^{O(d+\log d)}.
\]
For example the resultant bound follows from the product of Euclidean row norms in the Sylvester determinant. These are upper bounds. In particular the exponent \(2\) on field height is present, but at fixed positive top knot the term \(d\log V\) is of order \(d^2t\), while \(\log H_F=O(dt)\). The factor \(H_F^2\) changes the top cutoff by only \(O(t)\); it does not double the interior field-height coefficient.

The prospective parent congruence is one scalar condition on three coefficients. Even for uniform rational root modulo \(p\), a primitive quadratic of height \(V<p\) hits at most two root values. The expected number of hits is \(O(V^3/p)\); thus a positive leading population needs \(V\ge p^{1/3-o(1)}\). Use a fixed positive padding by taking \(v_0=\alpha_T y_0\), \(\alpha_T>1/3\), and keep the independent linear interior \(\alpha>1/2\). Neither the volume comparison nor this mean count asserts concentration.

With \(a_i\) the squared knots, take the top parent and box sizes \(a_i y_0,a_i v_0\) in \(\log M\) units and define
\[
\lambda_T(a_i)=1+(\lambda_T-1)a_i,\quad
y_i=\frac{a_i v_0}{\lambda_T(a_i)},\quad
y_1=\frac{v_0}{\lambda_T},\quad v_1=\alpha y_1,\quad y_2=\frac{v_1}{\lambda_H}.
\]
Here \(y_1\) denotes the global first descendant cutoff; the local formula at the last knot attains it. With fixed \(\lambda_T>1\), every local child is strictly below its box and parent, and is above the terminal scale eventually. The raw search loss from the rational side is conservatively \(2/(3\delta b)\): the top cofactor after division by its parent has log size at most \((2+a_i(v_0-y_0)+o(1))\log M\). The top algebraic smoothness argument is at most \((\lambda_T+o(1))d\). Use the scalar costs
\[
\begin{array}{c|cc}
 &\text{raw} & \text{algebraic}\\ \hline
\text{top} & b+\delta\lambda_T/3+2/(3\delta b)
 & b+\delta\lambda_T/3+u\sqrt{y_1/y_0}\\
\text{high} & b+\delta\lambda_H/3+(1+v_1)/(3\delta b)
 & b+\delta\lambda_H/3+u\sqrt{y_2/y_0}\\
\text{low} & b+\delta\lambda_L/3+1/(3\delta b)
 & b+\delta\lambda_L/3 .
\end{array}
\]
The unchanged charges are the raw private slots, staged private screening, characters \(b+2\delta/3\), and sparse solve and extraction \(2b\). The high and low shape, positive mean, and endpoint constraints are the existing linear ones. For the retained linear one-root and interior pair comparisons use \(\chi v_0>y_1\) and \(\chi v_0>2v_1\). [Existing private and linear cost definitions](keybreak-single-root-cost-witness.md)

## Finite witnesses and limiting arithmetic

At the limiting \(\alpha_T=1/3\), \(\alpha=1/2\), the unchanged private curve uses \(\kappa=2/(3u^2\delta)\). The interior field-height term becomes \(A=\delta^{-1}+\chi u^2/4\) in the terminal norm units. Thus \(\delta=2/\sqrt C\) optimizes the terminal bound and the reduced envelope is
\[
 b+2/(9u^2)+2u/3\le C,\qquad
 6b(C-b)\ge(\chi/2)u^2+4\sqrt C .
\]
The stationary equations and convex tangent proof are the same as for the linear top with \(U=\chi/2\). The stationary polynomial in \(z=u^3\) has a unique root in \((.18,.19)\) at \(\chi=2\) and \((.21,.22)\) at \(\chi=1\). Exact algebraic-real checks of both unsquared equations and \(0<2b<C\) yield the coefficients above. At those roots top and high ratios \(1.10,1.55\) have strict room in the public costs other than the active low raw bound. The positive low allowances and a sufficiently fine fixed grid approach each endpoint. [Stationary equations and tangent argument](keybreak-narrow-cost-witness.md#exact-limiting-envelope)

For explicit finite examples use the 4096 rounded knots, \(\alpha_T=.33333334\), \(\alpha=.50000001\), \(\lambda_T=1.10\), \(\lambda_H=1.55\), \(\eta=10^{-8}\), and cost slack \(s=10^{-7}\) in the original grid and low-slope definitions. Exact rational calculations give the following upper bounds.

| Parameter or charge | Wider model | Narrower model |
|---|---:|---:|
| \(\chi\) | 2.00000001 | 1.00000001 |
| \(\delta\) | 1.4137892 | 1.42655483 |
| \(\kappa\) | 1.43186097 | 1.3017480 |
| \(\beta\) | .66759549 | .663904916 |
| Raw private slots | 1.998627527 | 1.962858564 |
| Staged private screening | 2.001263156 | 1.965610379 |
| Top raw | 1.961833006 | 1.963597488 |
| High raw | 1.937315963 | 1.945223541 |
| Low raw | 2.001201041 | 1.965545515 |
| Top algebraic | 1.778133 | 1.799997 |
| High algebraic | 1.853719 | 1.871481 |
| Low algebraic | 1.751399 | 1.718831 |
| Characters | 1.886366 | 1.898134 |
| Sparse solve and extraction | 1.887679 | 1.894194 |
| Strict ceiling | 2.0014 | 1.9657 |

The positive weight and factor cap checks give \(W/M_{\rm priv}<2\) in both columns. The low box slope, fixed-point and positive mean conditions hold with the inherited paddings. The endpoint progression margins at exponent \(1/32\) exceed \(.16\) and \(.14\) respectively, and both linear interior pair and single-root comparisons are strict. The top checks use \(3a_iv_0>a_i y_0\) for population volume and \(a_i y_0>a_i v_0>y_i>0\) for separation.

## Distribution and dimension limitations

The scalar model needs a quadratic analogue of the joint rational population estimates and of the one- and two-mark algebraic smoothness estimates, including incoming incidence and usable degree-one child output. Algebraic values are resultants, nonlinear in the remainder coefficients. For coprime primitive quadratic marks the full integral two-remainder kernel has generators given by monomial multiples of their product, with size \(O(V^2)\). A one-remainder kernel has generators of size \(O(V)\). These follow by rational polynomial divisibility and the primitive form of Gauss's lemma. They explain the reference widths \(V^{2+o(1)}\) and \(V^{1+o(1)}\) in the two columns. Kernel smoothing alone does not supply resultant smoothness, and the narrower column additionally needs an improvement on the pointwise two-remainder comparison. The ledger also assumes the corresponding search, row size, and exact extraction overheads fit the inherited charges.

Reducible quadratics have only \(V^{2+o(1)}\) possibilities at height \(V\). By Gauss's lemma they are products of primitive linear forms, and the product of their heights is \(O(V)\) by the degree-two Mahler measure bounds. Dyadically grouping the factor heights, each range contains \(O(V^2)\) pairs. They also represent products of two linear marks already. Quadratics with a fixed discriminant squareclass have only \(V^{2+o(1)}\) possibilities as well: write \(b^2-4ac=\Delta s^2\) with fixed squarefree \(\Delta\), count \(O(V^2)\) pairs \((b,s)\), then use the divisor bound on the nonzero integer \(ac\). If \(ac=0\), the form is reducible and its contribution is already covered. A fixed quadratic field therefore supplies no \(p^{1/3}\) volume gain from these marks. The gain in the displayed ledger depends on genuinely three-dimensional families and does not by itself establish a factoring bound.

For one uniform parent root, the raw primitive population in a smooth three-dimensional box is now proved when its side exceeds the cube-root threshold by a fixed power. The rational smoothness condition and the algebraic distribution are still needed. [Quadratic mark count and discriminant-family bound](keybreak-quadratic-mark-geometry.md)

When the accepted top resultants are squarefree, every good resultant prime gives a unique degree-one child. In a mixed row the leading-coefficient parity is weighted by the degree of each mark. [Local child and row identities](keybreak-squarefree-resultant-children.md)

An ordinary one-mark lower bound is now available under Dirichlet GRH for negative fundamental marks with split parity. It permits a bounded number of additional factors of size at most \(V\exp(O((\log\log V)^2))\). The strict cost table above uses a smaller pure-smoothness cutoff; the new one-mark conclusion cannot be substituted directly for that hypothesis. [Algebraic one-mark estimate and its remaining conditions](keybreak-quadratic-one-mark.md)
