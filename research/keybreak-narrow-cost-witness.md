# A half-width cost witness with field-height multiplier 37/20

Replace the coefficient-width multiplier $2$ in the abstract public field height by $\lambda=37/20$, keeping the other half-width formulas. The resulting two-variable envelope has infimum $2.0260264428373861865\ldots$. A 4096-stage rational grid gives a strict ceiling of $2.02610$ for the stated cost inequalities. This is a cost-model calculation. In particular, it does not show that a narrower coefficient law supplies the required relation or incidence estimates. [Half-width cost model](keybreak-quadratic-class-integration.md#cost-and-leading-limit) · [Finite knot calculations](keybreak-optimal-finite-knots.md)

## Exact limiting envelope

Write $u>0$ for the private curve coefficient, $b>0$ for the row exponent, and $p(u)=2/(9u^2)+2u/3$. At the limiting geometry, $\alpha=1/2$, $\kappa=2/(3u^2\delta)$ and the top box coefficient in the public normalized units is $v_0=1/(4\kappa)$. Thus the field height in the terminal norm units becomes
$$
A=\delta^2\bigl[\delta^{-3}(1+\lambda v_0)\bigr]
  =\frac1\delta+\frac{3\lambda}{8}u^2 .
$$
The unreduced terminal inequality becomes $6b(C-b)\ge 2A+2/\delta+C\delta$. Minimizing $4/\delta+C\delta$ over $\delta>0$ gives $4\sqrt C$ at $\delta=2/\sqrt C$. The abstract envelope is therefore
$$
b+p(u)\le C,\qquad 6b(C-b)\ge Uu^2+4\sqrt C,\qquad U=\frac{111}{80}.
$$

The stationary point satisfies $b_*=C_*-p(u_*)$ and
$$
6b_*(C_*-b_*)=Uu_*^2+4\sqrt{C_*},
\qquad 6(C_*-2b_*)p'(u_*)=-2Uu_*.
$$
To compute it, set $z=u^3$, $P=2/9+2z/3$, $P'_{\rm slope}=2/3-4/(9z)$, and $F=2P+Uz/(3P'_{\rm slope})$. Then $F=u^2C$ after using the stationary equation. Clearing denominators in
$$
(6P(F-P)-Uz^2)^2-16z^2F=0
$$
gives the polynomial
$$
690165441z^6-732015144z^5+1047594384z^4-205355520z^3
 -130222080z^2+14745600z+1638400.
$$
Exact Sage algebraic reals give a unique root in $(.1754,.1755)$. Reconstruction verifies both unsquared equalities, $0<2b_*<C_*$, and the exact enclosure
$$
2.02602644283738618<C_*<2.02602644283738619 .
$$

This point is a global envelope optimum. If a smaller $C$ were feasible, it could be raised to $C_*$ in the terminal inequality. Indeed its feasibility implies $6b>4/\sqrt C$, so $6bC-4\sqrt C$ increases on $[C,C_*]$. The private inequality at $C_*$ is then strict. By convexity of $p$,
$b-b_*<-p'(u_*)(u-u_*)$. Expand the terminal expression at the stationary point:
$$
\begin{aligned}
6b(C_*-b)-Uu^2-4\sqrt{C_*}
={}&6(C_*-2b_*)(b-b_*)-2Uu_*(u-u_*)\\
&-6(b-b_*)^2-U(u-u_*)^2 .
\end{aligned}
$$
The coefficient $6(C_*-2b_*)$ is positive, and the slope identity cancels the two linear terms after using the strict private inequality. The resulting strict negative value contradicts feasibility. The stationary point itself meets both envelope inequalities, so this proves the infimum for this envelope.

## A strict rational grid and the public inequalities

Use the following exact decimals as rationals.

| Parameter | Value |
|---|---:|
| $\delta$ | 1.40510067 |
| $\kappa$ | 1.51410840 |
| $\beta$ | .671608405 |
| $\alpha$ | .50000001 |
| Top ratio $\lambda_T$ | 1.64 |
| High ratio $\lambda_H$ | 1.72 |
| Perturbation $\eta$ | .00000001 |
| Cap slack $s$ | .0000001 |
| Ceiling $C$ | 2.02610 |

Set $b=\delta\beta$, $R=\delta^{-3}$, $y_0=1/(2\kappa)$, $v_0=\alpha y_0$, $y_1=v_0/\lambda_T$, $v_1=\alpha y_1$, and $y_2=v_1/\lambda_H$. In these normalized public units take
$$
A_0=R(1+\lambda v_0),\quad A_+=A_0+\eta,\quad
\lambda_L=\frac{\beta+2A_++R/(3\beta)+4\eta}{2\beta-1/3},
\quad L=\lambda_L-\frac{A_++\eta}{\beta}.
$$
Here $L$ is the low box slope and does not denote the input size. The private mesh uses moment $M=\kappa\delta/3$. To reproduce its rational curve coefficient $h$, let $U_{12}(x)=(\lfloor10^{12}\sqrt{x}\rfloor+1)/10^{12}$, put $a=U_{12}(2)$ and take $h=U_{12}(a^2 2y_0/(3\delta))$. This gives $h=.559786171254$. Use the clean forward rounded stationary knots with seed $10^{15}$ and 4096 intervals, then the equalized weights at moment $M$. In the repository these are the helpers at commit $a5160e2$. [Rounded knots](../experiments/keybreak-quadratic-class-budget.py) · [Equalized grid](../experiments/keybreak-public-quadratic-budget.py)

Exact rational arithmetic checks that all weights are positive and their sum divided by $M$ is below $1.523<2$. The top guard $3y_1<\lambda v_0$ has margin greater than $.00342$. Also $0<y_0<1$, $0<2v_0<1$, $2\alpha>1$, and $\lambda_L>\lambda_H>\lambda_T>3/2$. The low checks give $L>1$, $(\lambda_L-1)L\beta>A_+$, $(\lambda_L-L)\beta-A_+=\eta$, and $(2L-1)\beta-\lambda_L/3-R/(3\beta)=2\eta$. The normalized endpoint check $.49(A_0+L\beta)-1.01R>.04$ holds. At each squared knot $a_i$, the top parent, box and child are $p_i=a_i y_0$, $v_i=a_i v_0$ and $y_i=v_i/(1+(\lambda_T-1)a_i)$. Every stage satisfies $0<y_i<v_i<p_i<1$, $2v_i>p_i$, $y_i\le y_1$, $3y_i<\lambda v_0$, and $1.01y_i-.49(1+v_i-p_i)<-.1$.

The explicit charges are bounded above as follows. The square-root terms in the top and high algebraic costs were checked by squaring positive rational inequalities.

| Charge | Upper bound |
|---|---:|
| Raw private slots | 2.023516309 |
| Staged screening | 2.026087266 |
| Top raw | 1.963189171 |
| High raw | 2.013313371 |
| Low raw | 2.026026673 |
| Top algebraic | 2.02092 |
| High algebraic | 1.91594 |
| Low algebraic | 1.774636822 |
| Characters | 1.880411200 |
| Sparse solve and exact extraction | 1.887354840 |

The checks use only the existing abstract charges and the committed knot helpers. They do not replay rounded integer allocations or nonterminal transitions, and in particular do not verify the finite dyadic separation, absolute cutoff or occurrence guards on an integer fixture. The ratio below two is a leading factor-count margin. The coefficient-law one- and two-mark estimates, their incoming-root-conditioned variants, the internal good-state recurrence at the new width, and any changed character or extraction costs still need their own justification. [Top field-pool transfer and its required estimates](keybreak-polynomial-top-field-pool.md)

## A 4096-knot witness at width multiplier \(13/8\)

Use the same definitions, rounded knots, and equalized weights as above, now with the following exact rational parameters.

| Parameter | Value |
|---|---:|
| \(\lambda\) | 1.625 |
| \(\delta\) | 1.33144 |
| \(\kappa\) | 1.66533 |
| \(\beta\) | .686514 |
| \(\alpha\) | .50000001 |
| \(\lambda_T\) | 1.8462 |
| \(\lambda_H\) | 1.8465 |
| \(\eta\) | .00000001 |
| \(s\) | .0000001 |
| \(C\) | 2.0190 |

The rational curve coefficient is \(h=.548331780321\). Write \(P=3\delta b\), and denote the total grid weight and common staged gate by \(W\) and \(G\). The bounds in the table use exact rational comparisons, with the algebraic square-root terms checked by squaring the positive residual.

| Charge | Formula | Upper bound |
|---|---|---:|
| Raw private slots | \(b+W+s\) | 2.016243610 |
| Staged screening | \(b+G+s\) | 2.018761959 |
| Top raw | \(b+\delta\lambda_T/3+1/P+2s\) | 2.007316865 |
| High raw | \(b+\delta\lambda_H/3+(1+v_1)/P+2s\) | 2.018585699 |
| Low raw | \(b+\delta\lambda_L/3+1/P+2s\) | 2.018760014 |
| Top algebraic | \(b+\delta\lambda_T/3+h\sqrt{y_1/y_0}+2s\) | 2.018777919 |
| High algebraic | \(b+\delta\lambda_H/3+h\sqrt{y_2/y_0}+2s\) | 1.882044472 |
| Low algebraic | \(b+\delta\lambda_L/3+2s\) | 1.744863726 |
| Characters | \(b+2\delta/3\) | 1.801678867 |
| Sparse solve and exact extraction | \(2b\) | 1.828104401 |

All the abstract guard checks listed for the first grid hold with these parameters. In particular, every weight is positive and \(W/M<1.492\). The triple congruence margin \(\lambda v_0-3y_1\) exceeds \(0.00000609\), the high ratio exceeds the top ratio by \(0.0003\), and the interior two-mark kernel margin \(\lambda v_0-2v_1\) exceeds \(0.15\). At the bottom, \(0.49(A_0+L\beta)-1.01R>0.20\). The progression check at exponent \(1/32\) gives \((15/32)(A_0+L\beta)-(33/32)R>0.16\). [Interior moment guards](keybreak-narrow-interior-guards.md)

This certificate covers the real cost model and rational grid. Integer allocation and transition checks, as well as top coefficient-law estimates at width \(13/8\), remain open for this witness.
