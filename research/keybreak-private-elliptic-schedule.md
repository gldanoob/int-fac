# A 2.159 single-input randomized factoring schedule

For one integer from scratch, this schedule gives a manuscript-level expected bit-time bound $L_N[1/3,2.159]$ under Dirichlet GRH and the pinned KeyBreak analytic results. The [private elliptic recognition proof](keybreak-private-elliptic-recognition.md) derives its private prime supply from RH, then applies Lenstra and Pomerance’s elliptic-curve splitting theorem to the counted shapes. All public algebraic tests retain the genus-two guarantee used by the [tiered schedule](keybreak-tiered-descent.md). The [arithmetic replay](../experiments/keybreak-private-elliptic-schedule.py) checks the parameters and costs. Neither the analytic argument nor the complete factoring algorithm has been verified in Lean.

## Exact parameters

Use the integer parameters and the one-field law from the [tiered schedule](keybreak-tiered-descent.md#integer-schedule) with the following rational constants.

| $\delta$ | $\kappa$ | $\beta$ | $\alpha$ | $\gamma$ | $h_T$ | $\lambda_H$ | $\lambda_L$ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1.3032 | .8786 | .678 | .5001 | .7222 | .70904 | 2.15 | 2.2684 |

Use 128 groups, $z_j=.0662+.9338j/127$, $a_j=z_j^2$, and the first private floor $\lceil.0043 e_0\rceil$. For top class $j$ use $E_j=\lfloor a_j e_0\rfloor$ and $\lambda_T(a_j)=1+.5005a_j$. The global first internal cutoff uses $a=1$. The leading local child log ratio is $a_j v_0/\lambda_T(a_j)$ in $\log M$ units, which increases with $a_j$. Each top class uses its own box and local ratio, then hands its children to the same global internal chain. The finite guards compare the rounded child cutoff of each class to the rounded global cutoff. The high-to-low switch still uses $e_i^2>dt^2$ for the high tier. The private factor-count cap is $K=2k_0$ per coordinate.

Here $A=\delta^{-3}<.452$ and the limiting log height of the coefficient law in $dt$ units is $A(1+2v_0)=.7089985757\ldots$, between .7089 and $h_T$. The conditioning margin is positive since $\lambda_T(1)>3/2$. The top geometry has $2\alpha>1$, and the local child-to-box log ratio tends to $1/\lambda_T(a_j)<1$ for all 128 classes. The normalized progression error coefficients are at most $-.298432852\ldots$ for (G.12) and $-.159034377\ldots$ for (G.17). The low fixed-point margin is $.0002158$, and the bottom mean margin is $.001171057\ldots$ in $(\log 2)t$ units. For the G.10 diagonal term the normalized contribution is $O(1/\mu)$, so $\mu\ge \exp(.001(\log 2)t)$ gives the same negligible bound as the larger source constant. The conservative separate-period margin is $.2969135056\ldots$. The same local mean, rational count and polynomial comparison arguments therefore apply as in the tiered schedule. [KeyBreak Proposition G.10 and Appendix G.8](https://crypto.sjtu.edu.cn/factoring.pdf#page=116)

## Private search and work on one integer

Take $h_P=.7631>1.4143/\sqrt{3\kappa\delta}$ and $h_A=1.07918>2.0001/\sqrt{3\kappa\delta}$. The private recognition input must supply capped, verified prime-factor products with cost exponent $h_P z_j$ for a gate at $a_j$. The lower bound for a successful private shape needs these recognitions on a sufficiently dense subset of the counted shapes with publicly good parents. The upper bound for a prefix gate only uses the verified prime factors already found. Set $W=2\kappa\delta/3$, $w_j=h_P(z_{j+1}-z_j)$ for $j<127$, and $w_{127}=W-\sum_{j<127}a_jw_j$. Assign the log-size fractions $f_j=a_jw_j/W$. All the weights are positive, the fractions sum to one, and $\sum f_j/a_j=1.604035004\ldots<2$. Use the same staged count, lower shape density and launch cap argument with the new recognition cost. [Staged private-coordinate tests](keybreak-private-band-stages.md)

Write $b=\delta\beta$ and allocate cap slack $s=.0001$. For a request with local ratio $\lambda$, use algebraic loss $\delta\lambda/3$ and its own rational loss ceiling. The largest top log ratio of the rational cofactor is $1-(1-\alpha)a_0 y_0$ despite $\lambda_T$ varying, and bounding both top caps with $\lambda_T(1)$ is sufficient. The high-ratio rational cofactor is bounded by $1+v_1$ and the low one by $1+o(1)$ in log-radix units. Divide those ratios by $3\delta b$. The algebraic test at child log ratio $y$ costs at most $h_A\sqrt{y/y_0}$ above its invocation coefficient, and vanishes on the $H$ scale in the low tier. Every setup and all retained work is charged to the current integer. The character rows below allow the [cumulative polynomial-bit probe cost](keybreak-cumulative-character-probes.md).

| Work | Single-input coefficient, rounded up |
|---|---:|
| Private gates $b+\max_j(\sum_{i\ge j}w_i+h_Pz_j)+s$ | 2.158592 |
| Top raw trials and rational tests | 1.824712 |
| Top algebraic tests | 2.158611 |
| High raw trials and rational tests | 2.134675 |
| High algebraic tests | 2.118209 |
| Low raw trials and rational tests | 2.158649 |
| Low algebraic tests | 1.869163 |
| Character probe setup | .868800 |
| Retained character evaluations | 1.752370 |
| Exact binary elimination | 2.120568 |
| Exact product, root and verification | 1.767140 |

For elimination, take exact binary square multiplication with exponent strictly below 2.4. The exact all-fields multiplication theorem gives an exponent below 2.371055 over $\mathbb F_2$. At a fixed block side one can use an exact binary bilinear identity with rank below the side to a power strictly between that bound and 2.4. Recursive products and block linear combinations use sequential scans with quadratic per-node routing up to logarithms. CUP uses those products for a rank profile, and a triangular solve gives one nonzero dependency. The fixed identities have current-input-independent size. The bit bound for the $e^{(b+o(1))H}$-dimensional binary matrix is therefore $2.4b$ in $H$ units, including routing. [Exact multiplication over every fixed field, Theorem 1.1](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/build/sections/introduction.tex#L57) · [CUP](https://arxiv.org/abs/1112.5717) · [Tape routing](cogentic-fast-transposed-extraction.md#short-entry-modular-pivots-on-tape)

The [arithmetic replay](../experiments/keybreak-private-elliptic-schedule.py) checks these costs with rational comparisons, including the square-root inequalities. It exercises the finite high-to-low transition, all local top cutoffs and private allocations at two symbolic input sizes. The conditional epoch success, verified output, and backup splitting argument follow the tiered schedule with the separate private recognition input.

## Limits of retuning the preceding schedule

With the original genus-two private coefficient the 2.250 schedule is already close to the continuous limit of its private gate and terminal per-request cost model. Put $x=\kappa\delta$, replace the private coefficient by its limiting lower value $h=2/\sqrt{3x}$, and write $P$ for the private cost excluding $b$. If $\tau(z)$ is the total weight in stages whose cutoff coordinate is at least $z$, then $\tau(z)\le(P-hz)_+$ wherever it might be positive. Hence
$$
W=\sum_j z_j^2w_j=\int_0^1 2z\tau(z)\,dz
\le \begin{cases}
P-2h/3,&P\ge h,\\
P^3/(3h^2),&P<h.
\end{cases}
$$
These bounds are attained as limits of fine grids with saturated gate inequalities. With $W=2x/3$ they give $P\ge p(x)$, where $p(x)=2\cdot3^{-1/3}$ for $x\le 3^{-1/3}$ and $p(x)=2x/3+4/(3\sqrt{3x})$ above that point. For a fixed number $m$ of intervals in the regime $P\ge h$, the optimal lower sum at terminal coordinate one is $S_0=0$ and $S_{m+1}=4/[27(1-S_m)^2]$. Indeed the preceding endpoint $u$ contributes $u^2(1-u)$ while all earlier intervals scale their optimum by $u^3$, so maximize $u^2-(1-S_m)u^3$ over $[0,1]$.

This terminal obstruction applies to non-affine low boxes as well under the same mean and cap proof. In units $t$, let $v$ be the last active box exponent, $q\ge\beta$ its parent cutoff, and $\beta$ the terminal child cutoff. Algebraic smoothness requires $\lambda\beta\ge v+h_T$. The source mean comparison requires $2v-q\ge\lambda/3+A/(3\beta)+c$ for a positive mean exponent $c$. Eliminating $v$ and letting $q\downarrow\beta$ gives $(2\beta-1/3)\lambda\ge\beta+2h_T+A/(3\beta)+c$. With limiting top slope $1/2$ and minimal height $h_T=A(1+\delta/(2x))$, the resulting low raw coefficient is bounded below by
$$
R(\delta,b,x)=\frac{6b^2+1/x+4/\delta+c\delta^2}{6b-\delta}.
$$
Allowing $c\downarrow0$ and omitting fixed slack, a proposed ceiling $C$ requires $6b(C-b)\ge 1/x+4\sqrt C$ because $C\delta+4/\delta\ge4\sqrt C$. For $C$ near 2.25, $b\le C-p(x)<C/2$, so feasibility requires
$$
\max_{x>0}\left[6p(x)(C-p(x))-{1\over x}-4\sqrt C\right]\ge0.
$$
The bracket is increasing up to $3^{-1/3}$ and strictly concave above it, since there $p',p''\ge0$ and $C<2p$. Its scalar zero is approximately $2.248355$, at $x\simeq .989137$ and $\delta\simeq1.333821$. This is the limiting envelope of those two rows. The 2.159 schedule changes the private recognition cost entering that envelope.
