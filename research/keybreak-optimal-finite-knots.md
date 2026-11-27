# Optimal finite private-screening knots

For $K\ge1$, take $0=x_0<x_1<\cdots<x_K=1$ and let
$$
S(x)=\sum_{i=0}^{K-1}x_i^2(x_{i+1}-x_i).
$$
In the equalized private-gate budget, the maximum gate is $m+h(1-S(x))$, so for $h>0$ one wants to maximize $S(x)$. The interval from zero to $x_1$ contributes zero. The sharp value is given by a scalar recurrence. Its excess gate cost relative to the continuum is $h(4/(9K)+o(1/K))$. [Uniform-grid comparison](../formal/cogentic/Cogentic/RandomizedPrivateGridUpper.lean)

## Exact recurrence and global optimum

Let $V_K$ be the maximum, initially permitting repeated knots. This is a compact simplex, and every such partition has $S(x)<1/3$ because the left-endpoint sum is strictly below the integral of $x^2$. In particular $V_K<1/3$. We have $V_1=0$. For $K\ge2$, write $t=x_{K-1}$. Rescaling the earlier knots from $[0,t]$ to $[0,1]$ divides their contribution by $t^3$. Hence
$$
V_K=\max_{0\le t\le1}\{t^3V_{K-1}+t^2(1-t)\}.
$$
The objective has derivative $t(2-3(1-V_{K-1})t)$ and a unique maximizing point in $(0,1)$,
$$
t_K=\frac{2}{3(1-V_{K-1})},\qquad
V_K=\frac{4}{27(1-V_{K-1})^2}.
$$
Since the final interval and the earlier optimizers are unique, induction gives a unique global partition. It has all inequalities strict. Its knots are
$$
x_i=\prod_{j=i+1}^K t_j\quad(1\le i\le K),\qquad x_0=0 .
$$

Equivalently this partition is determined by the interior recurrence
$$
x_{i+1}=\frac{3x_i^2-x_{i-1}^2}{2x_i},\qquad 1\le i<K.
$$
Indeed the derivative of $S$ with respect to $x_i$ is $x_{i-1}^2+2x_i x_{i+1}-3x_i^2$. Conversely, starting from $x_0=0$ and any $x_1>0$, the recurrence keeps increasing because $x_{i+1}-x_i=(x_i^2-x_{i-1}^2)/(2x_i)>0$. It is homogeneous of degree one, so requiring $x_K=1$ selects exactly one starting value. This is the optimizer already obtained by the scalar recurrence.

## Sharp error with finite bounds

Put $e_K=1/3-V_K$. The recurrence and its reciprocal form are
$$
e_K=\frac{e_{K-1}(1+3e_{K-1}/4)}{(1+3e_{K-1}/2)^2},\qquad
\frac1{e_K}-\frac1{e_{K-1}}
=\frac94+\frac{9e_{K-1}}{16(1+3e_{K-1}/4)}.
$$
With $e_1=1/3$, the first-order lower bound on each reciprocal increment gives $e_K\le4/(9K+3)$. Using this upper bound inside the positive correction gives the two-sided finite bound
$$
\frac{4}{9K+3+\mathcal H_{K-1}}\ \le\ e_K\ \le\ \frac{4}{9K+3},
\qquad \mathcal H_j=\sum_{i=1}^j\frac1i .
$$
In particular $e_K=4/(9K)+O(\log(2K)/K^2)$. Substituting this estimate once more in the reciprocal recurrence gives $\sum_{j<K}e_j=(4/9)\log K+O(1)$ and $\sum_j e_j^2<\infty$, so
$$
\frac1{e_K}=\frac94K+\frac14\log K+O(1),\qquad
e_K=\frac4{9K}-\frac{4\log K}{81K^2}+O(K^{-2}).
$$
The gate at the optimum is $m+2h/3+he_K$. Also $t_j=(1+3e_{j-1}/2)^{-1}$, so $\log t_j=-2/(3j)+O(\log j/j^2)$. The product formula gives $x_i\asymp(i/K)^{2/3}$ uniformly for $1\le i\le K$. The first knot is positive and of order $K^{-2/3}$, rather than $K^{-1}$ as in the uniform grid.

## Rational certificates without large exact optimizer denominators

The scalar recurrence is short, but its exact rational values still have rapidly growing denominators. If $V_j=p/q$ in lowest terms, then the unreduced next fraction is $4q^2/[27(q-p)^2]$. Starting at $0/1$, every reduced denominator is odd and every numerator is even. Since $(q,q-p)=1$, the cancellation is at most $27$. Hence the next denominator is at least $(q-p)^2>(2q/3)^2$ and at most $27q^2$. Starting at $V_2=4/27$, the bit lengths therefore grow on the scale $2^j$.

For practical certificates, round the scalar recurrence down to a $p_0$-bit dyadic grid at every step. The update $v\mapsto4/[27(1-v)^2]$ is increasing with derivative at most one on $[0,1/3]$, so $K$ updates cause absolute error at most $K2^{-p_0}$. Evaluate the ratios from these rounded values and round the ratios down as well. Their errors are $O(K2^{-p_0})$ since $v\mapsto2/[3(1-v)]$ has derivative at most $3/2$ on this interval. Each rounded ratio is strictly between zero and one for $p_0\ge2$. Forming their suffix products exactly gives strict dyadic knots with $O(Kp_0)$ bits each and maximum knot error $O(K^2 2^{-p_0})$.

The gate error from these perturbed knots does not gain another factor of $K$. If two strict partitions differ by at most $\Delta$ at every knot, comparing their summands while keeping one interval length fixed costs at most $2\Delta$ in total since the lengths sum to one. In the remaining length difference, summation by parts transfers the difference of adjacent knot errors to the monotone squared coefficients. The endpoint errors vanish and the squared coefficients have total variation at most one, so this part costs at most $\Delta$. The objective difference is thus at most $3\Delta$. This gives an exact certificate by simple dyadic arithmetic for a finite partition arbitrarily close to the sharp gate, without storing the exact rational optimizer.
