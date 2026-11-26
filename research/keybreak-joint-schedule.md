# A single-input GRH schedule with coefficient 2.430

For one integer $N$, the following changes to KeyBreak's multilevel descent give an expected bit-time upper bound $L_N[1/3,2.430]$ under Dirichlet GRH, assuming the correctness of the analytic propositions of the pinned preprint. The proof uses its public smoothness and good-parent arguments, the [staged private-coordinate construction](keybreak-private-band-stages.md), and the [first-split pass and exact extraction](keybreak-private-shape-work.md). All three are charged to every current input. This is an asymptotic manuscript result. [November 26 preprint, Appendices G and H](https://crypto.sjtu.edu.cn/factoring.pdf#page=105)

## Public integer parameters

Write $L=\log N$, $D=(L/\log L)^{1/3}$, $H=D\log L$, $n$ for the input bit length, and $m_b$ for its bit length. Choose the least odd $d\ge3$ with $125d^3m_b\ge64n$, so $d\sim\delta D$ with $\delta=4/5$. Keep the source's integer $M=\lfloor N^{1/d}\rfloor$ and set $t=dm_b$, $k_0=\lceil 7d/5\rceil$, $K=2k_0$. Use the same formula for $e_0$ with this $k_0$, namely $\lfloor(n-5)/(2k_0)\rfloor-1$. Define
$$
 \beta=1.03,\quad \alpha=.502,\quad \gamma=.98,\quad
 \lambda=4.08,\quad h_T=2.66,\quad
 e_B=\lceil\beta t\rceil,\quad T_H=\lfloor h_Tdt\rfloor .
$$
All terminating decimals denote exact rationals. Use $B=2^{e_B}$, $e_{\min}=\lceil .503e_0\rceil$, $v_i^{\rm bit}=\lceil\alpha e_i+\gamma e_B\rceil$, $V_i=2^{v_i^{\rm bit}}$ and
$$
 e_{i+1}=\max\{e_B,\lceil(\alpha e_i+\gamma e_B+T_H/d)/\lambda\rceil\}.
$$
The leading coefficients of $\log B/H$ and $\log_2 M/(dt)$ are $b=\delta\beta=.824$ and $A=\delta^{-3}=125/64$. Write $y_0=5/14$, $v_0=\alpha y_0$, $y_1=v_0/\lambda$, $v_1=\alpha y_1$. These are the limits of the logarithms of $Y_0,V_0,Y_1,V_1$ divided by $\log M$. Keep the Gaussian width $V_0^2 n^{10}$ and its original truncation. The [exact replay](../experiments/keybreak-public-private-schedule.py) verifies the strict endpoint, period, density and cost inequalities.

## Verification of the analytic hypotheses

The following estimates replace Proposition G.13's numerical substitutions. The progression errors may all use the fixed $\epsilon=1/100$. [Rational counts and Gaussian comparisons](https://crypto.sjtu.edu.cn/factoring.pdf#page=108) · [Verification in the original schedule](https://crypto.sjtu.edu.cn/factoring.pdf#page=123)

* **Heights and levels.** The true leading logarithm of $\sigma M$ in $dt$ units is $A(1+2v_0)=4755/1792$, strictly between $2.65$ and $2.66$. This absorbs the polynomial and $2^{O(d)}$ factors in the finite reference bound (G.57). The distance of the unclamped fixed point below $e_B$ is of order $t$ because $(\lambda-\alpha-\gamma)\beta-h_T=.01594>0$. The slope is $\alpha/\lambda<1$, giving $j=O(\log D)$ and eventual strict decrease. The exact cutoff inequality $\lambda d e_{i+1}\ge T_H+\alpha d e_i+\gamma d e_B$ gives (G.26) with upper argument $\lambda d$ using the conserved height padding. For the lower bound in (G.26), the underlying log heights have size comparable to $dt+d(\alpha e_i+\gamma e_B)$, even after divisions by a parent or child and the fixed truncations used in (G.25). The adjacent cutoffs have bounded log ratios. Thus the argument is between positive constant multiples of $d$ throughout. The startup guard $2(T_H+d v_0^{\rm bit})\le n-1$ is eventually true since $d v_0^{\rm bit}/n\to v_0=.1792857\ldots<1/2$. It bounds raw algebraic values by $\sqrt N$. All rational values remain smaller than $N$.
* **Boxes and rational parent weights.** Put $S=\alpha+\gamma=1.482$. For internal levels $\log_2(V_i/(2B))\ge (S-1)e_B-1$ and $\log_2(V_i^2/Y_i)\ge(2S-1)e_B$, since $2\alpha>1$. At an unclamped transition the margin for $\log_2(V_i/Y_{i+1})/t$ is at least $[(\lambda-1)S\beta-h_T]/\lambda+o(1)>0$, and the clamp uses $S>1$. The same comparisons apply to the top box where needed. The new parent floor exceeds both $V_0$ and $Y_1$ since $.503>\max(\alpha,\alpha/\lambda)$. The denominator prime and top parent remain distinguishable. The top cofactor $MV_0/p$ is below $M$, and the worst rational loss comes from $MV_1$. In the rational error terms (G.12) and (G.17), the respective coefficients of $\log M$ are $(1+\epsilon)y_1-(1/2-\epsilon)(1+v_1)$ and $(1+\epsilon)y_1-(1/2-\epsilon)(1+v_0-y_0)$. Both are below $-1/4$. In (G.18) and (G.53), $y_0-2v_0$, $y_1-2v_0$, and $y_1-1$ are strictly negative. The inverse rational densities cost $\exp(O(H))$, below every fixed positive power of $M$. These checks cover the wider top-band averages with the same field and child-good sets.
* **Gaussian and separate-period estimates.** We have $2v_0-3y_1>0$, so the Gaussian congruence comparison for the maximum product of three child primes and the finite scalar guards (H.1) hold with a fixed power margin. For (G.9), (G.23), (G.32), and (G.38) use $\log_2 X_*\ge 2.65dt+d(\alpha e_i+\gamma e_B)-O(e_i+e_B)$ and $\log_2 m_{\rm coord}\le1.96dt+3(\alpha e_i+\gamma e_B)+O(1)$. These follow from the same height and local period formulas because $A<1.96$ and $A(1+2v_0)>2.65$. The first relative error exponent is bounded at the bottom by
$$
 (1+\epsilon)1.96-(1/2-\epsilon)(2.65+S\beta)=-.0668654<-1/25 .
$$
The coefficient of $d(e_i-e_B)$ is strictly negative; a larger region improves the margin after the $O(e_i+e_B)$ padding. The additional endpoint factor $4k$ of (G.32) has logarithm $O(e_i+e_B)$, so both the separate-period estimate and the endpoint estimate absorb it. The angle, radius, mesh, inverse-density and finite-sampler factors are the same lower orders as in G.8–G.10. The fixed uniform constants there may depend on this schedule.
* **Local means and conditional tails.** The algebraic loss from Lemma G.6 and (G.25) is at most $(\lambda/3+o(1))(\log2)t$ and the global rational loss in $H$ units is at most $s_R+o(1)$, $s_R=(1+v_1)/(3\delta b)$. In a particular internal box the rational loss in $(\log2)t$ units is at most $[A+\alpha e_i/(dt)+\gamma\beta/d]/(3\beta)+o(1)$. Multiply the two local density estimates by the whole-box lower count, with geometric factor $V_i^2/Y_i$. The coefficient of $e_i/t$ in the resulting mean bound is $2\alpha-1-\alpha/(3\beta d)>0$ eventually. Its minimum occurs at the bottom, with margin
$$
 (2S-1)\beta-\lambda/3-A/(3\beta)=.0308407119\ldots>1/50 .
$$
Normalized complete semismooth bands lose only a logarithmic factor as in (G.13). For the internal root average (G.15), $Y_i/V_i^2$ times the inverse rational density decreases with $e_i/t$ and its exponent is strictly negative at the bottom, already by the stronger displayed mean inequality. The top ordinary and summed means have the extra positive $\log M$ margins $2v_0-y_0$ and $2v_0-y_1$. Thus the G.10 concentration threshold $\exp((\log2)t/50)$ holds, and G.11's weighted child recursion and G.12's good-parent union apply. This local check is needed because a uniform worst-stage density alone gives a weaker bottom mean.
* **Finite guards.** Apply the original comparisons on the actual integers for the coefficient sampler, root/denominator units, numerical size limits, record sizes and termination, substituting the displayed recurrence and bound on $T_H+d v_0^{\rm bit}$ for the old hard-coded ratios. Test the private grouped-band containment and count conditions from the staged proof. Reject the fast epoch if a needed comparison fails. The strict margins give eventual validity; monotonically advancing trial division between epochs covers the remaining finite sizes.

## Private coordinates, cost and extraction

The bit lengths in a private group still scale as $f_i L_x$ for a positive log-size fraction $f_i$. The inverse lower-density coefficient for a full unpartitioned squarefree band is now $W=2\kappa\delta/3$ with $\kappa=7/5$, since $k_0\sim\kappa\delta D$ and $\log k_0\sim(\log L)/3$. The Rankin upper loss for one coordinate of scale $X\asymp\sqrt N$ is $W/2$: $\log X/\log Y_0\sim\kappa\delta D$. Thus the lower good-shape construction and the upper prefix count change by exactly the same factor.

Use 128 fixed stages, $z_i=.71+.29i/127$, $a_i=z_i^2$. The first $a_i=.5041$ strictly exceeds the .503 floor. Set $h=21823/20000>(20001/10000)\sqrt{2y_0/(3\delta)}$, $w_i=h(z_{i+1}-z_i)$ for $i<127$, $w_{127}=W-\sum_{i<127}a_iw_i$, and $f_i=a_iw_i/W$. All weights are positive, $\sum f_i=1$, and $\sum f_i/a_i<2$. The explicit good product count, partial-factor recognizer, prefix gates on both coordinates and virtual-slot Markov caps follow from the staged proof. The $H$-coefficient caps use the conversion $H\sim(\log2)t/\delta$: implement a rational ceiling $q$ by $2^{\lceil qt/\delta\rceil}$. The raw-attempt allowance uses the new group counts; each launched shape has at most $2K$ top requests.

Take slack $s=.0001$ per cap and put $s_A=\delta\lambda/3$. Recompute (H.15) with inverse densities $s_A+s$ and $s_A+s_R+s$ in $H$ units. Retain the original character probes, the bounded algebraic testing exponent $2.0001$, and the fast extraction from the staged proof. The new $(2d)!$ in (H.22) has coefficient $2\delta/3$; the other factors in that expression have polynomial bit length. All lookup, confidence, recognizer-node and random-block caps in H.30–H.32 use the new counts. The maximum leading costs are as follows.

| Work | Coefficient |
| --- | ---: |
| Testing coordinate pairs, $b+\sum_{j\ge i}w_j+s+h z_i$ | $2.428995714\ldots$ |
| Raw descent trials and rational tests, $b+s_A+s_R+2s$ | $2.429017948\ldots$ |
| Algebraic tests, $b+s_A+2s+(20001/10000)\sqrt{2y_1/(3\delta)}$ | $2.294939996\ldots$ |
| Selection of original character probes, $8\delta/3$ | $2.133334$ (rounded up) |
| Characters on retained occurrences, $b+2\delta$ | $2.424$ |
| Rank-revealing binary elimination, at most $2.6b$ | $2.1424$ |
| Product expansion, exact integral field root and verification, at most $2b$ | $1.648$ |

The nonterminal epoch succeeds with probability bounded below, uniformly over previous failed epochs, by the same arguments as H.8 with the staged caps. Every returned divisor is verified unconditionally. The geometric epoch count, explicit trial-division fallback, and polynomial total split-tree nodes give the stated bound for every integer, including setup. The replay checks exact inequalities and the rounded schedule at a synthetic input bit length, including 1,325 public transitions and all 128 disjoint band allocations. The previous replay exercises finite prefix survivors. Neither runs an end-to-end implementation of the asymptotic schedule.
