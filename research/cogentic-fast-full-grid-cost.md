# Faster algebra on the full projective grid

The existing full-grid trace conditions and a faster transposed extractor give a manuscript-level coefficient of

$$
2\left[\frac{\omega^2}{3(\omega-1)}\right]^{2/3}
=2.5663543681\ldots
\quad\text{for }\omega=\log_2 7.
$$

The analytic inputs remain primitive Dirichlet GRH and the local smoothness, Gaussian and extraction hypotheses of the full-grid trace. The exponent $\omega$ here is for a multiplication algorithm implemented with the tape accounting of the extractor. The displayed value uses Strassen arithmetic. [Full-grid trace proof](cogentic-averaged-projective-trace.md) · [Fast transposed extraction](cogentic-fast-transposed-extraction.md)

## Separate costs

Use the full prime-denominator grid. The parameters are $c>b>0$, $x>0$, $xc>1/x$, $S=xc+1/x$, and $\rho=2S/(3b)$. The trace requires the strict relation-count margin $2c-\rho>b$. Write $B=\exp((b+o(1))H)$ and $M$ for the realized number of smooth columns. The one-mark upper bound gives $\mathbf E M\le\exp((2c-\rho+o(1))H)$. The sieve costs $\exp((2c+o(1))H)$.

- The modular pivot proposal costs $B^{\omega+o(1)}+MB^{\omega-1+o(1)}$. Partition the columns into batches of $B\,\operatorname{poly}(\log N)$ and maintain a basis consisting of original modular columns. At each merge, the batch and retained basis form a matrix with both dimensions $O(B\,\operatorname{poly}(\log N))$. CUP returns rank-revealing rows and columns even when this block is singular. Save the indicated original columns and discard the rest. The span after a merge equals the span of every column seen, so a final rank profile of the retained basis supplies the required square pivot minor with original indices. The dense batches can be materialized by sequential sorting of the sparse entries with zero filling. At each recursive CUP invocation panel and permutation data can be routed by sorting indexed records, and triangular updates and Schur products reduce to matrix products. Strassen multiplication itself can process quadrant streams on a fixed number of tapes, with the splitting, permutation and recombination charged to the entries across its recursion tree. [Rank-profile revealing CUP algorithm](https://arxiv.org/abs/1112.5717)
- The exact pivot solves, including the transposed solve with dyadic log right-hand sides, cost $B^{\omega+o(1)}$. Fast lifting is important here because those right-hand sides can have $B\,\operatorname{poly}(\log N)$ bits per entry. For example, Theorem 17 of Birmpilis–Labahn–Storjohann explicitly handles a product of right-hand-side count and lift digit count bounded by the system dimension. Pad with identity rows and columns to dimension $B\,\operatorname{poly}(\log N)$ to meet that hypothesis, without altering the desired block of solutions. Each reconstructed solution has numerators and denominators of $B\,\operatorname{poly}(\log N)$ bits by the existing Cramer bounds, so fast rational reconstruction across the required coordinates takes $B^{2+o(1)}$ bit operations. [Prime-power high-order lifting](https://cs.uwaterloo.ca/~glabahn/Papers/SmithMultipliers.pdf) · [Pivot and projection precision](cogentic-transposed-log-precision.md)
- Forming and testing the projected real columns after the transpose solves can cost $MB^{1+o(1)}+B^{2+o(1)}$ with quasi-linear high-precision arithmetic. For the sparse dot products, sort references to pivot-row coordinates, merge with the saved rounded transpose solutions, and sort the returned terms by column. This reads each required coordinate with the multiplicity of the sparse references. Each mark uses real logarithms of positive absolute values with the separation and precision of the existing proof. Fast real logarithms give quasi-linear bit cost at that precision. Root bisection still costs $B^{2+o(1)}$ in total because there are only polynomially many roots. The final real solve and sparse verification of the selected directions also fit $B^{2+o(1)}$. [Brent’s multiple-precision logarithm](https://doi.org/10.1145/321941.321944) · [Fast transposed extraction](cogentic-fast-transposed-extraction.md)

Thus the expected bit-time coefficient is

$$
\max\{2c,\ \omega b,\ 2c-\rho+(\omega-1)b\}. \tag{1}
$$

The third term is the modular batch scan, not a charge for each arithmetic operation on a high-precision free column. The expected work bound uses linear dependence on $M$. For a capped trial replace $2c-\rho$ in that term by $2c-\rho+\epsilon$, for any fixed $\epsilon>0$, and use the one-mark expectation and Markov to bound the rejected fraction by $\exp(-(\epsilon+o(1))H)$.

## Exact infimum and a strict rational schedule

Write $u=b/c\in(0,1)$. The sample margin and $S\ge2\sqrt c$ give

$$
c^{3/2}>\frac{4}{3u(2-u)}.
$$

For any $\omega\in(2,3]$ the lower envelope of $\max(2,\omega u)c$ under this constraint decreases up to $u=2/\omega$ and increases thereafter. On the first part $u(2-u)$ is strictly increasing. On the second part the cube of the lower envelope is proportional to $u/(2-u)^2$, which is strictly increasing. Put

$$
u_*=\frac2\omega,\qquad
c_*=\left[\frac{\omega^2}{3(\omega-1)}\right]^{2/3},\qquad b_*=u_*c_*,
\qquad x_*=\frac1{\sqrt{c_*}}.
$$

At these limiting values, $\rho_*=2c_*-b_*$, so the third term of (1) is exactly $\omega b_*=2c_*$. Hold $b_*$ and $x_*$ fixed and increase $c$ slightly. Then $xc>1/x$, and the derivative of $2c-\rho-b$ with respect to $c$ is $2-2x_*/(3b_*)>0$, since $2x_*/(3b_*)=(2-u_*)/2$ at the limit. Approximate the resulting strict parameters by rationals. Thus the lower envelope is the actual infimum of (1) with these analytic constraints.

A concrete strict witness is $c=1283/1000$, $b=183/200$, $x=883/1000$. Here $x^2c>1$, $2c-\rho-b>0.00044$, and all three terms of (1) are below $2.570$. These inequalities follow by rational arithmetic using the strict upper bound $\omega<351/125=2.808$, certified by $7^{125}<2^{351}$. A trial cap with $\epsilon=1/20000$ still keeps all three terms below $2.570$. The fixed even moment order must be chosen with the actual strict relation margin. The existing interleaving argument applies to rational schedules approaching the infimum.
