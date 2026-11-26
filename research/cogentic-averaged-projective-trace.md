# Averaged row residues lower the projective trace threshold

Use the full interval of prime denominators and keep all the original numerator windows. Under the local Gaussian and clean-moment estimates of the variable-multiple construction, the centered trace and rank proof needs $c>b$ and $2c>b+\rho$, where $\log A\sim cH$, $\log B\sim bH$, $S=xc+1/x$ and $\rho=2S/(3b)$. The two-prime hit estimate is averaged over row residues inside the trace. Primitive slope spacing supplies the rough pointwise estimates. The proof below covers the narrow numerator width $Aw$ with $\log(1/w)\sim D\sqrt z$, where $D=(\log N/\log\log N)^{1/3}$ and $z=\log\log N$. It uses all denominator primes. [Complementary prime-denominator character estimate](cogentic-prime-denominator-residues.md) · [Fixed thin-menu trace transfer](cogentic-thin-denominator-moments.md)

## Primitive classes and a weighted second moment

Let $W_\beta\asymp A e^{-30z^2}$ be the denominator interval length and $K\asymp W_\beta/\log A$ its number of primes, using the RH prime-counting error. In each root or baseline interval the slope has width $\asymp w$. The numerator interval at a denominator $\beta$ has integer length $\asymp J$ for $J=Aw$. The normalized grid measure $\pi_0$ gives all $2d+1$ intervals equal mass and is uniform inside each interval. Each mark is reduced since $0<a<\beta$ and $\beta$ is prime. A proper gcd of $a-m\beta$ with $N$ ends the search. On runs reaching the field draws, every original numerator remains available. The variable-multiple family has no field-dependent cofactor sieve. [Variable-multiple field and grid](cogentic-variable-multiple-lattice.md#the-two-polynomial-fields)

For a modulus $m_0$ supported on primes at most $B$, two distinct marks of the same projective residue modulo $m_0$ have $|\Delta|\ge m_0$, where $\Delta=a\beta'-a'\beta$. Their rational slopes are therefore at distance at least $m_0/A^2$. There are $O(1+A^2w/m_0)$ such marks in each interval. Consequently for every residue $\sigma$ and every such modulus, including moduli larger than $A^2$, put $d_0=1/(A^2w)$ and obtain
\[
 \pi_0(\operatorname{slope}\equiv \sigma\bmod m_0)
 \ll e^{O(z^2)}(m_0^{-1}+d_0).                                      \tag{1}
\]
In particular $B^2d_0$ is exponentially small in $H$ when $c>b$. Keeping the interval width in the spacing count puts the factor $w^{-1}$ only in the additive term.

For a distinct pair of main-band primes $Q=pp'$, fix $t\le T=\exp(Cz^2)$ supported on the small-prime band and put $m_0=tQ$. Let $F(v)$ be bounded by $M$ and have total variation at most $M$ in each numerator interval, for every fixed denominator. Define
\[
 D_\sigma(F)=m_0\sum_{v:\operatorname{slope}(v)\equiv\sigma(m_0)}
                   \pi_0(v)F(v)-\sum_v\pi_0(v)F(v).
\]
No regularity as the denominator varies is needed. Expanding the square and averaging over all $\sigma\bmod m_0$ gives
\[
 \mathbb E_\sigma |D_\sigma(F)|^2
 =\sum_{v,v'}\pi_0(v)\pi_0(v')F(v)\overline{F(v')}
                      \bigl(m_0\,1_{m_0\mid\Delta}-1\bigr).            \tag{2}
\]
It suffices by the triangle inequality in the root-mean-square norm to prove the bound in one grid interval at a time.

For a denominator pair, the congruence on the two numerators is a lattice of determinant $m_0$. Write $\lambda$ for its shortest nonzero vector length. Every subrectangle of the two numerator intervals has count equal to its area divided by $m_0$, with error $O(J/\lambda+1)$. Represent integer intervals by half-integer endpoints so that the area is the product of the integer lengths. To see the error bound, extend a shortest vector to a lattice basis and count on lines parallel to that vector. Their spacing $m_0/\lambda$ is at least $\sqrt 3\,\lambda/2$ by reducing the other basis vector along the shortest one. Each line has error at most one. The slice lengths are unimodal with total variation $O(J)$, so their sum gives the area term with error $O(J/\lambda)$. Two-dimensional partial summation now gives an absolute bound $O(M^2 m_0(J/\lambda+1))$ on the weighted numerator sum in (2) at that denominator pair.

Here is an elementary bound for the mean of $\lambda^{-1}$ over distinct denominator pairs in the full prime interval. If a nonzero vector of maximum norm at most $U\le\sqrt{m_0}$ lies in the numerator lattice, write it as $g(s_1,s_2)$ with $\gcd(s_1,s_2)=1$. Put $h=\gcd(g,m_0)$. The primitive direction has size at most $U/h$ and satisfies $s_1\beta'-s_2\beta\equiv0\bmod(m_0/h)$. In a dyadic block of primitive directions of size $\asymp Z$, the possible exact multiples of $m_0/h$ for one direction number $O(1+ZW_\beta/(m_0/h))$. For each multiple there are $O(1+W_\beta/Z)$ integer denominator pairs, since solutions advance by the primitive direction. As $W_\beta\gg\sqrt{m_0}$, the product is $O(W_\beta/Z+W_\beta^2/(m_0/h))$. Summing the $O(Z^2)$ directions dyadically to $U/h$, and then summing over $h\mid m_0$, bounds the proportion of pairs by
\[
 L^{O(1)}\left(\frac U{W_\beta}+\frac{U^2}{m_0}\right).
\]
This uses $\sum_{h\mid m_0}1/h\le1+\log m_0$. Since the number of prime pairs is $\asymp K^2$, the passage from integer pairs costs only the squared prime-density factor. Dyadic summation with weights $1/U$ gives $\mathbb E\lambda^{-1}\ll L^{O(1)}/\sqrt{m_0}$ for distinct denominators. The identical denominator pairs use $\lambda\ge1$ and number only $K$. Dividing the bound for (2) by the squared mark count $\asymp(KJ)^2$ gives
\[
 (\mathbb E_\sigma |D_\sigma(F)|^2)^{1/2}
 \ll M L^{O(1)}
 \left(\frac{m_0}{KJ}+\frac{\sqrt{m_0}}J+\frac{m_0}{J^2}\right)^{1/2}
 =M e^{-\Omega(H)}.                                                  \tag{3}
\]
All three ratios tend to zero exponentially for $c>b$, since $K,J=Ae^{-o(H)}$ and $m_0\le B^2e^{O(z^2)}$. This treats all projective residues, including nonunit residues at either row prime.

## One averaged edge in each distinct-position term

Use the local assumptions in the thin-menu trace proof. In particular, the compatible prescribed-row probabilities, the rough distinct-mark bound and the clean formula (1) of the full-grid trace are uniform in the original mark tuples. For any chosen fixed trace order $k$, take the degree slack and Gaussian width for $k$ marks and at least $2k+2$ row prescriptions as in the finite-order lemma. The changed residue argument does not alter the Gaussian conditional moduli or the saddle analysis. [Local assumptions](cogentic-thin-denominator-moments.md#schedule-and-inputs) · [Full-grid clean formula](cogentic-projective-trace.md#joint-smoothness-at-distinct-marks)

The physical primes of distinct row labels are initially taken distinct. At edge $j$ of a cyclic row tuple, write $Q_j=p_jp_{j+1}$ and $M_j=(p_jp_{j+1})^{-\alpha_s/2}$. The source's pointwise incidence identity, after suppressing unnecessary root hits, is $f_j\Pi_j^\circ=Q_j1_{\rm hit}\overline U_j(v)$. The function $\overline U_j$ depends on the endpoint primes and fields and the mark center. It is independent of the row residues. Its supremum and numerator variation are $L^{O_k(1)}M_j$. In the variable-multiple chart no exclusion depending on a random cofactor occurs. The factors from the actual nominal windows and the coprime projective denominator belong to the one-point reference densities. Those densities cancel against their reciprocal weights in the clean formula. The remaining $\Phi_i$ are the prescribed-hit factors of the source identity. [Source Lemma 9.2(2), p. 45](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=45) · [Variable-multiple conditional moduli](cogentic-variable-multiple-lattice.md#the-two-polynomial-fields)

Fix a small-prime slope class $s\bmod t$. Formula (3), applied with $m_0=tQ_j$, bounds the root-mean-square over the two endpoint residues of
\[
 Q_j\sum_{v:\,\operatorname{slope}(v)\equiv s(t),\ \mathrm{hit}}
                      \pi_0(v)\overline U_j(v)
       -t^{-1}\sum_v\pi_0(v)\overline U_j(v)
\]
by $M_j e^{-\Omega(H)}$. Indeed this expression is $D_\sigma(\overline U_j)/t$, and fixing one class modulo $t$ can raise the mean square of $D_\sigma$ by at most a factor $t$. The ordinary $t$-class mass follows from a numerator count at fixed denominator. The modifications in $\Pi_j^\circ$ are supported on the prescribed slopes, and their total local gains are polynomial in $L$ for fixed $k$. For an additional prime $p$ outside $Q_j$, (1) applied at $tQ_jp$ bounds the weighted added-hit mass by $e^{O(z^2)}(1/(tp)+Q_jd_0)$. Unneeded target hits are bounded in the same way with $p=\ell$, whose logarithm is $\asymp z^3$. An extra condition at an endpoint label already agrees with the retained endpoint or has no hit on its full support. On the mean part a single ordinary prescribed slope has the simpler bound from (1). Thus the absolute centered sum at this edge is $M_j e^{-C' z^2}$ on average over its two endpoint residues, for any fixed $C'$ and sufficiently large $N$. Every edge, at every residue, also has the rough upper bound $M_j e^{O_k(z^2)}$ from (1) and $Q_jd_0=o(1)$. [Full-grid identity and suppression](cogentic-projective-trace.md#expansion-of-the-centered-trace)

Expand the small-prime partition factors as in the original trace. For a term with product $t\le T$, split the independent marked sums by their slope classes modulo $t$. For each class vector, bound all but one centered edge by the rough upper bound and average the absolute error on the remaining edge. This average is valid in the row-label sum itself. Distinct labels at distinct primes carry independent residue choices when summing, weighted by their uniform prescribed-root probabilities $\prod_p p^{-1}(1+O(e^{-L^3}))$. The chosen edge has two distinct endpoints. A repeated label in a nonadjacent edge simply reuses its residue, and its other edge factors have already been bounded uniformly. Summing the prime choices with the same $M_j$ as in the original proof costs only $L^{O_k(1)}$. The number of class vectors is at most $T^k$, which is absorbed by the chosen $C'$. If distinct labels share a physical prime, its saved prime choice gives $B^{-1+o(1)}$. Preserve the rough upper bounds on every edge for that exception and use the uniform root-event formula for distinct residues or fields at the same prime. There is no appeal to typicality of actual roots.

For a tail term whose prime product exceeds $T$, retain one required pair equality at each prime. Expose the marks in order. The imposed moduli $t_j$ of the later marks have product exceeding $T$, so one exceeds $T^{1/k}$. The weighted conditional mass of its class is $O(e^{O(z^2)}(1/t_j+Q_jd_0))$ by (1) at $t_jQ_j$. The other steps can be bounded by their unconditional hit brackets. This gives $e^{O_k(z^2)}(T^{-1/k}+B^2d_0)$ before multiplying by the total partition coefficient mass $L^{O_k(1)}$. The estimate works for arbitrary tail moduli because (1) holds even above $A^2$. Choose fixed $C$ large enough. The $p^2\mid\Delta$ exception intersected with an edge hit has weighted mass $O(e^{O(z^2)}(1/p+Q_jd_0))$ by (1) at $\operatorname{lcm}(Q_j,p^2)$. At fixed first mark, true coincidence costs at most $O(B^2\|\pi_0\|_\infty)=\exp((2b-2c+o(1))H)$ when restoring the factored main sum. None of these errors spends a fixed-denominator discrepancy factor $B^2/(Aw)$. [Singular-series partition expansion and rough moments](cogentic-projective-trace.md#expansion-of-the-centered-trace)

## Repetitions, diagonal and the cost implication

Put $n=\exp((2c-\rho)H)$ and $\eta=2c-\rho-b>0$. A genuine repeated position costs $n^{-1}\exp(o(H))$ after merging its smooth indicators. Apply the same bipartite closed-walk count as in (3) of the full-grid trace proof. A tree congruence uses (1) at one main-band prime. A two-prime cycle closure, including a four-cycle, uses (1) at their product. Their masses are $B^{-1+o(1)}$ and $B^{-2+o(1)}$, respectively, since $c>b$. For repeated physical primes the saved prime choice is unchanged. The bridge-only tree exception still has $2h\le k$ for $h$ distinct marks. The resulting sum is bounded by
\[
 B^{o(1)}\sum_{h<k}(B/n)^{k-h}
   +B^{1+o(1)}\sum_{h\le k/2}(B/n)^{k-h}.
\]
It decays exponentially for fixed even $k>2b/\eta$ with positive slack. The distinct-position estimates and this bound give the off-diagonal operator-norm estimate by the even trace moment. [Repeated-position graph count](cogentic-projective-trace.md#repeated-marked-positions)

The target and diagonal have support modulus at most $BE^2=B^{1+o(1)}$ with $\log E\sim z^3$. Thus even the old fixed-denominator numerator estimate is sufficient there, including its small auxiliary modulus. The squared hit bracket averages $O(Q+Q^2/(Aw))=O(Q)$ at those support moduli $Q$. A true duplicate costs $B^{1+o(1)}/n$, up to polynomial factors, after using the single-mark smoothness bound. Distinct terms use the two-point cancellation with their smaller support and the same rough tail bounds. The total mass and the root cleanliness and normalizer estimates remain as in the original proof. The interval spectral lower bound and norm-direction elimination use equal mass of intervals and the uniform pointwise logarithm bounds. The selected denominator range remains the original one. These are the stochastic and spectral inputs to the existing peeling and rank conclusion. [Target and diagonal](cogentic-projective-trace.md#the-target-and-the-diagonal) · [Cogentic Proposition 10.1, pp. 52–55](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=52)

With the separately proved transposed extraction cost, the full-grid sieve costs $\exp((2c+o(1))H)$ and the exact lift costs at most $B^{3+o(1)}+MB^{2+o(1)}$ for $M$ smooth columns. The one-mark bound gives the expected ledger
\[
 \max\{2c,\,3b,\,2c+2b-\rho\}.
\]
For a lower bound on this ledger, write $u=b/c\in(0,1)$. The inequality $S\ge2\sqrt c$ gives $c^{3/2}>4/[3u(2-u)]$, and the cost is at least $c\max(2,3u)$. The cube of the resulting lower bound decreases up to $u=2/3$ since $u(2-u)$ increases, and increases thereafter since it is $48u/(2-u)^2$. The new constraints admit the limiting choice $c=3b/2$, $x=1/\sqrt c$, $b^3=2/3$, at which all three entries approach $3(2/3)^{1/3}=2.6207413942\ldots$. For instance hold this $b$ fixed and increase $c$ slightly with $x=1/\sqrt c$ to make $2c>b+\rho$ strict, then approximate the positive parameters by rationals. This is a manuscript-level bound using the imported local Gaussian, smoothness and extraction hypotheses above. It uses the full prime-denominator interval and does not give averaged two-prime control for an arbitrary sparse fixed menu. [Transposed extraction](cogentic-transposed-log-precision.md) · [Randomized retry and verification](cogentic-randomized-relation-time.md)
