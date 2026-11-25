# Factoring from several partial cyclotomic divisibilities

Let $N$ be a product of a fixed number $t\ge2$ of distinct primes in $(X,2X]$ and write $H=N^{1/t}$. Fix finitely many distinct prime indices $r$ with $d_r=r-1$. For each index fix a finite list of nonconstant integer polynomials. Choose one entry $P_r$ of degree $e_r$ per index, with $P_r(N)\ne0$. For a prime factor $p$ put
$$
 g_r=\gcd(\Phi_r(p),|P_r(N)|),\qquad
 u_r=\frac{\log g_r}{d_r\log H},\qquad
 S=\sum_r\frac{d_r}{e_r}u_r^2.
$$
The factor, the gcds and the selections are hidden. Given $N$ and the fixed lists, a deterministic search finds a proper factor in
$$
 \operatorname{poly}(\log N)\, H^{\max(0,(t-1-S)/t)}
$$
bit operations whenever such a selection and factor exist. In particular, a deficit $t-1-S=O(\log\log N/\log N)$ suffices for polynomial time. Every factor meeting the polynomial-time criterion can be recovered within a polynomial cutoff with the corresponding constant. The number of distinct inputs having even one qualifying factor at that cutoff is at most $X^{1+o(1)}$. The [full-divisibility construction](polynomial-order-supply.md) attains this population exponent in the larger model.

## Radius and number of candidates

Take the monic row $T$ at modulus $N$ and $\Phi_r(T)$ at each modulus $M_r=|P_r(N)|\ge2$. Modulus-one rows can be omitted. Try dyadic lower bounds $A_r\le g_r<2A_r$ and lower bound $\lfloor H/2\rfloor$ for $p$. There are polynomially many tuples of bounds since the lists and indices are fixed. The hidden divisors are pairwise coprime as in the full-order argument. Since $\log M_r=e_r\log N+O(1)$, rounding the lower bounds to powers of two decreases the radius logarithm by at most $O(1)$ in total. At the correct tuple the guaranteed radius thus has logarithm at least
$$
 \frac{(\log H)^2}{\log N}+\sum_r\frac{(\log g_r)^2}{d_r\log M_r}-O(1)
 = \frac{\log H}{t}(1+S)-O(1).
$$
Use a public budget starting at one and doubling. At each budget try only tuples whose guaranteed radius covers $[H/2,2H]$ in that many windows up to a fixed constant factor. Round radii down with a bounded additive error in their logarithms. At every correct tuple test the returned candidates by division and primality. By the displayed radius the stated budget suffices. The fixed polynomial cutoff uses all qualifying tuples if all their factors are wanted. [Simultaneous univariate lattice theorem](hidden-divisor-lattices.md#a-lattice-for-overlapping-public-moduli)

For the population bound, fix $p$. Each $g_r$ can be chosen from the $X^{o(1)}$ divisors of $\Phi_r(p)$. On a fixed choice apply the squarefree-part argument for each $P_r$ to $g_r$ in place of the full order. It yields a divisor $h_r\mid g_r$ with $h_r\gg g_r^{1/e_r}$ and $X^{o(1)}$ possible classes for $N/p\bmod h_r$. The product of the pairwise coprime $h_r$ therefore has logarithm at least
$$
 (\log H)\sum_r (d_r/e_r)u_r-O(1)\ \ge\ (\log H)S-O(1).
$$
The last inequality uses $0\le u_r\le1+O(1/\log H)$ on balanced inputs. CRT leaves at most $X^{o(1)}(1+X^{t-1}/H^S)$ possible cofactors for that choice. At a polynomial cutoff this is $X^{o(1)}$ per $p$, proving the bound. More generally, for any fixed $s\ge0$, at most $X^{1+\max(0,t-1-s)+o(1)}$ inputs have $S\ge s$. [Squarefree parts, contents and root counts](polynomial-order-supply.md#upper-bound-for-every-fixed-list)

## Common divisors of the orders at two primes

For $t=2$ take any fixed set of distinct indices $k\ge3$, including composite indices. Now use $u_k=\log\gcd(\Phi_k(p),\Phi_k(q))/(\varphi(k)\log H)$. The same window budget works with $S=\sum_k u_k^2$. At each index use the relative cyclotomic rows from the single-index algorithm. Remove primes dividing $k$ from its own overlap as in that proof, at loss $O_k(1)$ in the logarithm. Every remaining prime $\ell$ gives $p\bmod\ell$ exact order $k$, so rows from different indices have coprime hidden divisors. Sum their radius contributions while counting the row $T$ at $N$ just once. The single-index Cauchy–Schwarz estimate gives each contribution at least $(\log H)u_k^2/2-O_k(1)$. This proves the claim. The available positive supply theorem for moderate common divisors reaches a smaller threshold. An infinite family crossing the combined polynomial-time threshold with genuinely partial overlaps at every selected index is open here. [Relative rows](2026-11-25-handoff/cyclotomic-supply/audit.md) · [Moderate-overlap population](moderate-cyclotomic-overlap.md)

## Exact checks

At $N=17\,767$, the entries $N-2,N-4$ at indices $2,5$ give gcds $55,5\,921$ at the factor $109$. Integer power comparisons certify $u_2\ge4/5$, $u_5\ge2/5$, hence $S\ge32/25$. Neither individual contribution reaches one. One translated lattice of radius 32 recovered $109$ from the two public lower bounds and $N$. For $12\,613\cdot16\,421$ the entries $N-1,N-4,N+2$ at indices $2,3,7$ give proper gcds $238,66\,877,281$. The exact comparisons certify $S\ge20\,129/20\,000$ and $u_r\le3/5$ throughout. The replay also checks separation of the two relative classes at indices $3,4,6$ on 568 balanced prime pairs, including 43 pairs with nontrivial unramified overlap at multiple indices. [Exact replay](../experiments/partial-order-supply.gp)
