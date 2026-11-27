# One-coordinate public quadratic rows and a conditional 2.034 budget

A public row with a witnessed modular square root needs only one large smooth coordinate. If a short quadratic-sieve window supplies enough such rows and their completed descents leave residual dimension at exponent at most .20, the single-input KeyBreak ledger gives \(L_N[1/3,2.034]\). All public searches, screenings and descents are charged to that input. The exact infimum of the corresponding relaxed cost model is \(2.03288100822533195\ldots\), strictly above the ordinary GNFS coefficient \((64/9)^{1/3}=1.922999427\ldots\). The supply and rank assumptions are additional hypotheses. [Public span and tagged extraction](keybreak-public-span-schedule.md) · [Existing charged limit](keybreak-sparse-dependency.md) · [Exact replay](../experiments/keybreak-public-quadratic-budget.py)

## Public root window and hypotheses

Write \(H=(\log N)^{1/3}(\log\log N)^{2/3}\) and \(D=(\log N/\log\log N)^{1/3}\). Take integers \(x\) with \(x-\lfloor\sqrt N\rfloor\) between half of \(\exp(tH)\) and \(\exp(tH)\), inclusive after rounding. Then \(U=x^2-N>0\) has size \(\sqrt N\exp((t+o(1))H)\) and \(x^2\equiv U\pmod N\). The raw pair is \((U,1)\). Keep the verified prime list for \(U\), its descent into the same field and base as the private rows, and the public comparison root \(x\). Unit checks give a direct factor when a proper gcd occurs. Otherwise these are zero-tag rows in the usual signed square certificate. The additive \(O(H)\) change in coordinate bit length does not change the leading band losses or factor counts. The design needs no shorter representative for this public pair.

The following two hypotheses specify the missing arithmetic input. They concern the same environment and field as the existing good-field event, with joint probability bounded below.

1. For the specified public band grid, the deterministic window has sufficiently many fully valid one-coordinate shapes with elliptic-eligible primes and good top-prime requests to collect the prescribed \(\exp((b+o(1))H)\) public rows using the existing bounded recognition and descent. At each earlier gate its population of certified prefix shapes is at most \(\exp((t-\sum_{i<j}w_i+o(1))H)\), where \(w_i\) is the one-coordinate loss for stage \(i\). These are rate hypotheses inside the **short quadratic window**, including the stage caps. The ordinary interval count of smooth integers does not supply them. Fixed positive slack above \(t=b+\sum_i w_i\) and in the caps accommodates subleading factors.
2. The completed public rows of this charged list leave at most \(\exp((.20+o(1))H)\) constraints in the quotient for the private rows. It suffices to certify a containing subspace for the offered rows with this residual dimension. The public list is ready independently of the unrevealed private roots. The tagged sparse solve then finds a dependency involving fresh private rows, and the original exact lifting and hidden-sign argument give a proper gcd with probability bounded below.

A witnessed modular root supplies the public tag. It gives no guarantee that the associated descent vectors cover the private law. In particular, conditioning on good field labels does not imply the quadratic-window population hypothesis.

Each permitted prime \(p>\exp(tH)\) coprime to \(N\) occurs in at most two distinct values in the window. The roots of \(x^2\equiv N\pmod p\) occupy two classes, and the window has length less than \(p\). Thus repetition among the top-prime requests gives at most constant reuse. The ledger charges each descent separately.

## Exact gate minimax and positive last bands

Let \(u=\sqrt{2/(3\kappa\delta)}\) be the limiting elliptic coefficient for a cutoff whose logarithm is the endpoint-one scale, with \(d\sim\delta D\). Write \(W=4/(9u^2)=2\kappa\delta/3\) for the two-coordinate moment. The public moment is \(m=W/2\). A band at log cutoff fraction \(z_i^2\) with weight \(w_i\) contributes \(z_i^2w_i\) to the moment. The gate contribution above the required row exponent is
\[
G=\max_j\left(uz_j+\sum_{i\ge j}w_i\right).
\]
Let \(T(z)\) denote the tail of the band measure. The moment is \(\int_0^1 2zT(z)\,dz\) and the gate imposes \(T(z)\le G-uz\). If the endpoint is one, then \(G\ge u\). Consequently \(G\ge m+2u/3\). With no factor-count cap the exact limiting infimum is \(\max(u,m+2u/3)\).

For \(m>u/3\), use uniform density \(u\) below one and an atom \(m-u/3\) at one. For \(0<m\le u/3\), take a small positive atom \(\tau<m\) at one and density \(u\) on \([a,1)\), where \(a^3=1-3(m-\tau)/u\). The gate is \(u+\tau\), so a negative endpoint weight is never required. If the factor-count cap \(\sum w_i\le2m\) is imposed, the exact limiting moment capacity at gate \(G\ge u\) instead is
\[
\int_0^1 2z\min(2m,G-uz)\,dz .
\]
The bound follows from both upper envelopes for \(T\). The envelope itself is a tail, and scaling it down realizes any smaller moment. Strict slack admits a finite positive grid and a positive endpoint atom. For the simple full-interval grid at the optimum below, both public and private moments exceed \(2u/3\), so the single atom is positive and the limiting count ratio \((m+2u/3)/m\) is strictly below two. The localized construction is available for other parameters, with the same separate count-cap check.

## The exact relaxed joint constant

Public screening imposes \(C\ge b+p(u)\), where \(p(u)=2/(9u^2)+2u/3\). Fully charging \(\exp((b+o(1))H)\) public descents at the physical field height gives the original terminal constraint
\[
6b(C-b)\ge \tfrac32u^2+4/\delta+C\delta.
\]
This reduction uses the same bottom mean and raw-search constraints as the sparse schedule. In particular any feasible terminal has \(6b>\delta\). Allowing a constant private row count in the relaxed minimization only eases the constraints. [Terminal elimination](keybreak-sparse-dependency.md#how-close-the-schedule-is-to-its-cost-floor)

At the stationary point write \(b=C-p(u)\) and choose \(\delta=2/\sqrt C\). The two active equations and their stationary slope relation are
\[
6b(C-b)=\tfrac32u^2+4\sqrt C,\qquad 6(C-2b)p'(u)=-3u.
\]
Set \(z=u^3\). Their solution has \(z\in(.172,.173)\) and satisfies
\[
455625z^6-437400z^5+680400z^4-136512z^3-82944z^2+9216z+1024=0,\quad
C=\frac{225u^6-48u^3-32}{36u^2(3u^3-2)}.
\]
Exact real-algebraic arithmetic isolates the root and verifies the equations before squaring, \(C>2b>0\), and \(p_{\rm private}(u)+.20<C\), where \(p_{\rm private}(u)=4/(9u^2)+2u/3\).

The stationary point gives a global lower bound for this relaxation. Hold its value \(C_0\) fixed. The tangent to the convex \(p\) bounds any feasible \(b-b_0\) above by \(-p'(u_0)(u-u_0)\). The tangent to the concave \(6b(C_0-b)\), with positive slope at \(b_0\), then bounds that quantity by its stationary value plus \(3u_0(u-u_0)\). The tangent to \(3u^2/2\) has the same slope and is a lower bound. If a smaller budget had been feasible, increasing it to \(C_0\) would give strict slack in the terminal inequality because \(6b>\delta\). This contradicts the tangent inequalities and \(4/\delta+C_0\delta\ge4\sqrt{C_0}\). The optimum also equals the infimum with the gate count cap and residual exponent .20, since both have strict slack. The terminal floor with the excess height discarded is already \((64/9)^{1/3}\); supplying one-coordinate public rows keeps the full terminal population in this model.

Allowing the public grid to end below one gives the same joint infimum while retaining the physical field height. Indeed the terminal inequality implies \(u^2\le C^2-(8/3)\sqrt C\). Since \((64/9)^{1/3}\le C\le2.034\) for any competing budget, its right-hand side is increasing and gives \(u<.6\). Then \(m>u/3\). A gate \(G<u\) could carry moment at most \(G^3/(3u^2)<u/3\), by integrating the tail envelope only through \(G/u\). Thus \(G\ge u\), and the same gate lower bound applies even when the public endpoint is flexible.

## A finite strict ledger

Use \((\delta,\kappa,\beta,\alpha,\gamma)=(1.40273,1.536,.67286,.50001,.576970)\), public top ratio \(1+.63a\) at squared cutoff \(a\), high and low ratios \(1.72,1.790783\), and height allowance \(.480269\). The curve allowance is \(.55626\). The public grid has 1024 evenly spaced knots from .021 to one, the private grid 512 from .026 to one, and each has its own exact moment and positive final weight. Use \(t=2.021469891890\ldots\), the raw public window exponent \(b+\sum_iw_i\) plus fixed slack. The source's rounding guards from the fixed grids remain valid for the public coordinate length after the additive \(O(H)\) change, since the band gaps are fixed positive fractions of their \(DH\) endpoint scale. The replay checks both grids at the ordinary coordinate length and the exact leading costs of the enlarged window.

| Work charged to this input | Coefficient rounded up |
|---|---:|
| Public screening, including the whole window | 2.033152 |
| Private screening at residual exponent .20 | 2.007774 |
| Public top and high raw descent | 1.957772 and 2.012425 |
| Public low raw descent | 2.032951 |
| Public top and high elliptic tests | 2.014088 and 1.914194 |
| Setup and character checks | 1.878995 |
| Tagged sparse solve and exact extraction | 1.887682 |

Private descent charges are smaller than their public counterparts because they use the same per-row caps with .20 in place of \(b\). The existing first-split prepass costs \(\exp(o(H))\), since its small-factor cutoff uses the same degree scale. Under hypotheses uniform on eligible inputs, independent retries and exact divisor checks give the stated expected bit-time ceiling, including recursive splits. The relaxed stationary value can be approached using the same strict-rational perturbations and finer fixed grids as the original schedule, with the top and high ratios here and the low ratio set by the terminal mean. This requires public supply and span for the resulting grids as well as for the finite witness above. [First-split prepass](keybreak-private-shape-work.md#ensuring-the-count-suffices-on-every-input)
