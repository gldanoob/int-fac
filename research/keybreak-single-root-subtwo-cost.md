# Scalar cost below two with single-root guards

The half-width scalar model with a single-root congruence guard and the interior pair guard admits a fixed 4096-stage witness below \(2\) at coefficient-width multiplier \(\chi=13/10\). The largest charge is staged screening, with strict upper bound \(1.999588530\). At \(\chi=6/5\) the same grid construction gives \(1.994504559\). Both certificates assume the reduced guard list and the separately required analytic estimates. [Single-root cost model](keybreak-single-root-cost-witness.md)

## Rational inputs and grid

Each displayed decimal is exact. In both columns take \(\alpha=.50000001\), \(\lambda_T=1.51\), \(\lambda_H=1.64\), \(\eta=10^{-8}\), and \(s=10^{-7}\).

| Parameter | \(\chi=13/10\) | \(\chi=6/5\) |
|---|---:|---:|
| \(\delta\) | 1.4143811528 | 1.4161828070 |
| \(\kappa\) | 1.4261156028 | 1.4084922792 |
| \(\beta\) | .6673597811 | .6666757184 |
| Rational curve bound \(h\) | .574901940413 | .578119310889 |

Set \(b=\delta\beta\), \(R=\delta^{-3}\), \(y_0=1/(2\kappa)\), \(v_0=\alpha y_0\), \(y_1=v_0/\lambda_T\), \(v_1=\alpha y_1\), and \(y_2=v_1/\lambda_H\). The low parameters are determined by
\[
A_0=R(1+\chi v_0),\quad A_+=A_0+\eta,\quad
\lambda_L=\frac{\beta+2A_++R/(3\beta)+4\eta}{2\beta-1/3},
\qquad L=\lambda_L-\frac{A_++\eta}{\beta}.
\]
For \(U_{12}(x)=(\lfloor10^{12}\sqrt{x}\rfloor+1)/10^{12}\), use \(h=U_{12}(U_{12}(2)^2\,2y_0/(3\delta))\), as in the previous witness. Both strict square-root allowances were checked by squaring.

Write \(K=4096\) and start the integer recurrence at \(P_0=0\), \(P_1=10^{15}\). For \(1\le j<K\) use \(P_{j+1}=P_j+\lfloor(P_j^2-P_{j-1}^2)/(2P_j)\rfloor\). Put \(z_j=P_j/P_K\), \(a_j=z_j^2\) for \(1\le j\le K\), and set the moment \(M=\kappa\delta/3\). The first \(K-1\) weights are \(w_j=h(z_{j+1}-z_j)\); the last is \(w_K=M-\sum_{j<K}a_jw_j\). Write \(W=\sum_jw_j\) and \(G=hz_j+\sum_{i\ge j}w_i\), which is independent of \(j\). This is the exact recurrence and equalization from the named scalar helpers at commit \(\texttt{a5160e2}\). [Rounded knots and upper square root](../experiments/keybreak-quadratic-class-budget.py) · [Equalized grid](../experiments/keybreak-public-quadratic-budget.py)

## Charges and strict margins

Let \(Q=3\delta b\). The following are strict rational upper bounds. For each algebraic square-root term, subtract the rational part of its charge from the displayed bound and check that the remainder is positive and its square strictly exceeds \(h^2y_i/y_0\).

| Charge | Formula | \(\chi=13/10\) | \(\chi=6/5\) |
|---|---|---:|---:|
| Raw private slots | \(b+W+s\) | 1.996948150 | 1.991849403 |
| Staged screening | \(b+G+s\) | 1.999588530 | 1.994504559 |
| Top raw | \(b+\delta\lambda_T/3+1/Q+2s\) | 1.905487649 | 1.906248737 |
| High raw | \(b+\delta\lambda_H/3+(1+v_1)/Q+2s\) | 1.981270694 | 1.982268901 |
| Low raw | \(b+\delta\lambda_L/3+1/Q+2s\) | 1.999526297 | 1.994441978 |
| Top algebraic | \(b+\delta\lambda_T/3+h\sqrt{y_1/y_0}+2s\) | 1.986625373 | 1.989617188 |
| High algebraic | \(b+\delta\lambda_H/3+h\sqrt{y_2/y_0}+2s\) | 1.899760506 | 1.902001263 |
| Low algebraic | \(b+\delta\lambda_L/3+2s\) | 1.749845125 | 1.745140144 |
| Characters | \(b+2\delta/3\) | 1.886821866 | 1.888256562 |
| Sparse solve and extraction | \(2b\) | 1.887802194 | 1.888269381 |

All weights are positive, \(\sum_j a_jw_j/M=1\), and \(W/M<1.567\) and \(W/M<1.576\) in the respective columns. Both have \(0<y_0<1\), \(0<2v_0<1\), \(0<\chi v_0<1\), \(2\alpha>1\), \(2\beta>1/3\), \(L>1\), and \(\lambda_L>\lambda_H>\lambda_T>3/2\). The cutoff and mean margins are exactly \((\lambda_L-L)\beta-A_+=\eta\) and \((2L-1)\beta-\lambda_L/3-R/(3\beta)=2\eta\).

| Guard expression | Strict lower bound at \(\chi=13/10\) | Strict lower bound at \(\chi=6/5\) |
|---|---:|---:|
| \(\chi v_0-y_1\) | .11179 | .09544 |
| \(\chi v_0-2v_1\) | .11179 | .09544 |
| \((\lambda_L-1)L\beta-A_+\) | .06750 | .06360 |
| \(.49(A_0+L\beta)-1.01R\) | .20204 | .19870 |
| \((15/32)(A_0+L\beta)-(33/32)R\) | .17028 | .16718 |

For each of the 4096 squared knots in each column, use parent \(\tilde p_j=a_jy_0\), box \(\tilde v_j=a_jv_0\), and child \(\tilde y_j=\tilde v_j/[1+(\lambda_T-1)a_j]\) in the top guard. The checks give \(0<\tilde y_j<\tilde v_j<\tilde p_j<1\), \(2\tilde v_j>\tilde p_j\), \(\tilde y_j\le y_1\), and \(1.01\tilde y_j-.49(1+\tilde v_j-\tilde p_j)<-.1\). [Interior progression and pair guards](keybreak-narrow-interior-guards.md)

The finite witness comparisons use exact fractions. Only the scalar knot, weight, and square-root helpers were evaluated. Integer allocation, transitions, and any analytic transfer at the narrower widths require separate checks.
