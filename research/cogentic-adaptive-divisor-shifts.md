# Adaptive divisor-forcing shifts for prescribed Cogentic marks

For one prescribed mark, an adaptive CRT shift forces an explicit squarefree band divisor almost as large as the coefficient interval. It also gives a short list guaranteed to contain shifts free of a prescribed sparse shell of forbidden primes. An exact two-coordinate chart handles two prescribed marks at once while preserving a prescribed modular coefficient class. The construction tests only polynomially many indices for each mark or pair. In the conservative schedule, the remaining cofactor still has logarithm of order $V$. [Coefficients and marks](cogentic-universal-score-sampler.md) · [Replay](../experiments/cogentic-adaptive-divisor-shifts.py)

## Choosing the shift from the actual residue

Consider values $n(j)=c+qj$ for $0\le j<T$ in a unit class with $q\ne0$. Suppose the progression has fixed nonzero sign and $l\le|n(j)|\le h$. Let $J$ be the eligible band and let $F$ be a specified set of disjoint forbidden primes. Fix an integer $M\ge1$. Run through distinct eligible primes in $(B/2,B]$ coprime to $q$, multiplying them into an anchor $S$ until the next multiplication would exceed $T/M$. If enough primes are available to reach that stopping condition, then
\[
                          T/(BM)< S\le T/M.
\]
For each selected prime $p\mid S$, impose $j\equiv-cq^{-1}\pmod p$. Incremental CRT finds the least index $j_0\bmod S$. Each of the $M$ indices $j=j_0+Sk$ for $0\le k<M$ is in the original interval. Their cofactors satisfy the exact affine identity
\[
                    n(j_0+Sk)/S=(c+qj_0)/S+qk .
\]
For every selected anchor prime, at most $M/p+1$ of these cofactors repeat that prime. For a forbidden prime not dividing $q$, at most $M/p+1$ cofactors contain it. Forbidden primes dividing $q$ divide none, by the unit assumption. Assuming
\[
       \sum_{p\mid S}\frac1p+\sum_{p\in F}\frac1p+
                        \frac{\omega(S)+|F|}{M}\le\frac12,               \tag{1}
\]
at least half the tested indices have squarefree anchor divisor $S$ with no repeated anchor prime and no forbidden prime. One gcd per candidate against $S\prod_{p\in F}p$ checks precisely these conditions. Every remaining cofactor has absolute value between $lM/T$ and $hBM/T$. Applying bounded division to it determines whether the full norm is a squarefree band product.

In the fixed schedule one can include the *whole* forbidden shell $(V^2,2V^2]$ used in the affine-line obstruction. The prime number theorem gives reciprocal sum $O(1/\log V)$ on that shell. The anchor uses $O(V/\log B)$ primes in $(B/2,B]$ and adds negligible reciprocal weight. Its prime supply is sufficient after excluding the polynomially many primes dividing the step or the cofactor multipliers. Taking $M$ a sufficiently large polynomial in $L=\log N$ enforces (1). The support depends on the actual $c,q$ through the CRT index. A passing cofactor can still contain a larger forbidden prime. [Affine-line obstruction and its witness shell](cogentic-intercept-sampling.md#realizing-the-obstruction-in-dyadic-subboxes-of-a-fixed-cogentic-score)

The construction gives a witness to at least $\omega(S)$ distinct eligible prime divisors. Equivalently its factorial divisor moment $\binom{\omega_J(n)}{\omega(S)}$ is positive, with the known anchor supplying a summand. Building the anchor by CRT takes polynomial work in the explicit prime cutoff and input bit lengths. It avoids enumerating all products of $\omega(S)$ band primes or all $T$ shifts.

## Two marks and a modular root class

Let the two coefficient coordinates be $(u,v)$ with centered widths $4UA,4U$, and take $0\le a<b\le A$. Fix any compatible coefficient residue pair modulo $Q=B^{O(1)}$, for example from specified affine root or derivative congruences at boundedly many primes. Choose $(u_0,v_0)$ in its residue class within $Q$ of the original center. For integers $z,w$ of magnitude at most $U/(4Q)$, set
\[
 (u,v)=(u_0,v_0)+Q(bz-aw,w-z).
\]
These coefficients lie in the original box and preserve all prescribed congruences. The two mark coordinates are independently shifted by $Q(b-a)z$ at $a$ and by $Q(b-a)w$ at $b$. Thus each has a scalar progression of length $\Theta(U/Q)$. Apply the adaptive shift construction to each progression, after the standard gcd reduction when the common divisor is eligible and squarefree. An ineligible common divisor makes that chart unusable for smoothness. Any pair of passing independent indices gives one simultaneous perturbation in the original coordinates. The same construction applies in the other field. [Affine lattice congruence routine](cogentic-coefficient-selection.md) · [Unit-class reduction](cogentic-scalar-divisor-count.md#a-sharp-count-for-long-progressions-at-arbitrary-moduli)

For each prescribed pair and each prescribed CRT class in each field, at most $M^4$ coefficient tuples need be produced across the two fields. Individual exact smoothness checks can be done before taking the Cartesian product. There are at most $A^2$ mark pairs and at most $B^{O(1)}$ bounded prescriptions for roots and residues. Even enumerating every such choice costs $\exp(O(H))$ on the fixed schedule, with $H=L^{1/3}(\log L)^{2/3}$. The guarantees are per prescribed pair. Different pairs may require different coefficients, so their smoothness witnesses do not pool into a rank certificate for one field pair.

In that schedule $\log T=(100000+o(1))V$ for the full-width chart and $\log l,\log h=(100001+o(1))V$ for the actual marks. Here $V=L^{2/3}(\log L)^{1/3}$. The anchor bounds imply that the residual log size is $(1+o(1))V$. In an intermediate box with $\log T=(\tau+o(1))V$, it grows to $(100001-\tau+o(1))V$. The method spends almost all available intercept freedom on known prime divisors, but a generic passing residual is still too large for a size certificate of smoothness. [Fixed schedule](cogentic-deterministic-two-thirds.md#fixed-parameters) · [Intermediate window geometry](cogentic-intermediate-score-budget.md#dyadic-subboxes-and-the-linear-mass-term)

## Exact finite comparison

Run `python3 -B experiments/cogentic-adaptive-divisor-shifts.py`. With $m=\lfloor\sqrt N\rfloor$ and $r=N-m^2$, the base polynomials are $X^2+r$ and $X^2-X+r+m$. Both take the value $N$ at $m$. The affine perturbation $N(X-m)(u+vX)$ preserves this value exactly. The ordinary one-mark trial holds $v=0$ and uses a length-$2^{40}$ intercept interval starting at $2^{40}$. All trials take the band $(\sqrt{1009},1009]$, the primes between 11 and $\sqrt{1009}$ as the forbidden set, and the eligible unit marks among $m+1,\ldots,m+16$. Each method has a budget of 192 indices per scalar call. The controls are the first 192 indices and the first index of each of 192 equal-width strata. The controls use the direct band test, so they need not pass the additional forbidden-prime screen separately.

| Input | Unit marks | Both fields smooth by adaptive shifts | Fixed prefix | Fixed strata | Adjacent unit pairs | Both marks smooth in both fields via two-coordinate chart |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 77 | 9 | 9 | 0 | 0 | 6 | 6 |
| 143 | 10 | 10 | 0 | 0 | 7 | 4 |
| 221 | 11 | 9 | 0 | 0 | 8 | 1 |
| 187 | 12 | 11 | 0 | 0 | 9 | 5 |
| 299 | 12 | 12 | 0 | 0 | 9 | 0 |
| 437 | 14 | 14 | 0 | 0 | 12 | 1 |
| **Total** | **68** | **65** | **0** | **0** | **51** | **17** |

The pair comparison uses adjacent marks for the exact chart with $Q=1$, a wider coefficient rectangle holding the computed shifts, and independent coefficient choices between fields. The replay tests $2\cdot192\cdot68=26{,}112$ adaptive indices for the one-mark cases and $4\cdot192\cdot51=39{,}168$ for the paired cases. It checks the lattice formula separately at $Q=35$. It verifies each successful norm by dividing the original integer directly and checks both marked values after reconstructing the common perturbation in a field. The measurements concern local smoothness of affine marked values on a finite geometry. The positive Gram score and factoring performance remain unmeasured.
