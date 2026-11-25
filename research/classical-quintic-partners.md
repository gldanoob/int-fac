# A classical uniform prime-factor bound on long partner intervals

Let $p$ be any prime, $L=\log(2p)$, $b=\lceil\log_2(2pZ+1)\rceil$. For a sufficiently large absolute $C$, the following deterministic mean bounds hold.

* On the integers $N=pq$ with prime $Z<q\le2Z$, a single algorithm completely factors $N$ in mean time $b^{O(1)}\exp(O(L^{2/3}(\log(2L))^{4/3}))$ whenever $\log Z\ge C L^2\log(2L)$.
* On the integers $N=pm$ with integer $Z<m\le2Z$, the same bound gives one proper split of $N$ or the factor of a prime-power input whenever $\log Z\ge C L^3$. It also holds on restricting to the partners for which $p$ is the least prime factor.
* On ordinary RH, replace $L^{2/3}(\log(2L))^{4/3}$ by $\sqrt{L\log(2L)}$ in both statements.

There are no exceptional $p$ and the classical versions use neither an ordinary RH assumption nor a fixed Hecke zero-free strip. The price for constructing the fields from a public parameter is the lower bound on $Z$. The [pointwise field construction](quintic-field-genus-two.md) reaches $Z\ge p^4$ with the additional fixed-strip input. Both methods use the uniform genus-two order mass of Lenstra–Pila–Pomerance and Younis's smooth-number asymptotics. [Lenstra–Pila–Pomerance II, Theorem 1.1](https://people.maths.ox.ac.uk/pila/HyperII.pdf#page=3) · [Younis, Theorems 1.1 and 1.3](https://arxiv.org/pdf/2409.05761)

## A family of independent cyclic fields

Use Lehmer's quintic
$$F_T(X)=X^5+T^2X^4-(2T^3+6T^2+10T+10)X^3+(T^4+5T^3+11T^2+15T+5)X^2+(T^3+4T^2+10T+10)X+1.$$
This is a regular cyclic degree-five cover of the parameter line. Its smooth projective source has genus four. Its four tame branch points are the zeros of $D(T)=T^4+5T^3+15T^2+25T+25$. A generator of its Galois group sends a root $u$ to $((T+2)+Tu-u^2)/(1+(T+2)u)$. Away from finitely many primes the cover retains its geometric group. Over each such $\mathbb F_p$, an unramified fiber either splits with five rational points or has no rational point and is irreducible of degree five. The Weil bound on the genus-four source, after omitting the bounded branch and bad model fibers, proves that $4p/5+O(\sqrt p)$ of the $p$ parameter values are irreducible. [Darmon, *Note on a polynomial of Emma Lehmer*](https://www.math.mcgill.ca/darmon/pub/Articles/Research/03.Lehmer/lehmer.pdf) · [Cho and Kim, §3, polynomial and automorphism](https://jtnb.centre-mersenne.org/article/JTNB_2012__24_3_583_0.pdf)

Fix a small-prime dyad $P<p\le2P$ with $P$ a power of two. Put $2^k=2P$ and $w=\lceil 200\log(2P)\rceil$. Grow a list of $w$ distinct odd primes $r_i$ where $D$ has a simple root and $w$ further distinct odd primes $h_j$ where $F_0$ splits with different roots. Omit the fixed bad primes for $F_0,D$, the primes below 11 and the finite exclusions below. The ordinary prime ideal theorem for these fixed fields, or classical Chebotarev, gives sufficient choices below $O(w\log(2w))$. Brute testing all residues at these small primes has polynomial cost. For large $p$ they are all smaller than $p$.

The following polynomial identities are exact:
$$
\operatorname{disc}_X F_T=(T^3+5T^2+10T+7)^2D(T)^4,\qquad
F_T(X)\equiv (X+T^2/5)^5\pmod {D(T)},
$$
$$
3125 F_T(-T^2/5)=D(T)(4T^6+30T^5+65T^4-200T^2-125T+125).
$$
The last factor is coprime to $D$ in $\mathbb Q[T]$. At $r_i$ choose a lift $b_i$ of the simple root with $r_i\parallel D(b_i)$ and avoid the fixed resultant. Put $A=\prod_i r_i^2\prod_j h_j^2$. Choose $0\le a_i<A$ congruent to $b_i$ modulo $r_i^2$ and zero modulo all other listed prime squares. For a public integer $0\le t<2^k$ take
$$T_i=A t+a_i,\qquad K_i=\mathbb Q[u_i]/(F_{T_i}(u_i)).$$
After translating the root by a lift of $-T_i^2/5$ at $r_i$, the displayed identities make $F_{T_i}$ Eisenstein at $r_i$. Thus $K_i$ is cyclic quintic, totally ramified at $r_i$, and unramified at every other $r_{i'}$. Each $h_j$ splits into five distinct primes of residue degree one. For any fixed $t$ the fields $K_i$ are linearly disjoint. In fact the compositum of any previous fields is unramified at the new designated prime, whereas a cyclic quintic field has no intermediate field. Uniformly in $i,t$,
$$\log(2+|T_i|)+\log |\operatorname{disc} K_i|=O(L\log(2L)).$$

Each $t\mapsto T_i$ permutes $\mathbb F_p$. Therefore the mean over $t\bmod p$ of the number of inert $K_i$ is $w(4/5+O(1/\sqrt p))$. A positive proportion have at least $w/2$ inert fields. The integers $0\le t<2^k$ include every such residue, so the same positive-proportion lower bound, up to an absolute constant, holds for the bit words. Write $I_p(t)$ for the set of inert indices and call a word admissible if $|I_p(t)|\ge w/2$. This set is used only for counting.

## Independent quadratic marks for each field

For each $h_j$ lift the five distinct roots of $F_0$ modulo $h_j^2$. Construct an integral polynomial $B_j(X)$ of degree at most four whose evaluations at these lifts are $h_j,1,1,1,1$ in an arbitrary fixed order. At every other $h_{j'}^2$ require the entire polynomial to be 1. Lagrange interpolation and coefficientwise CRT give such a polynomial with coefficients bounded by $\prod_j h_j^2$. Divide out its ordinary integer content. This rational scaling does not change the ratio $\sigma(B_j(u))/B_j(u)$, and the content is a unit at each designated $h_{j'}$.

For $K=K_i$, $u=u_i$, let $z_j=B_j(u)$ and $c_j=\sigma(z_j)/z_j$. Since $F_{T_i}\equiv F_0$ modulo every $h_j^2$, $z_j$ has valuation one at one prime over $h_j$ and zero at the other four. Each $z_{j'}$ with $j'\ne j$ is a unit at all primes over $h_j$. Consequently the squareclasses of the $c_j$ are independent. All $c_j$ have norm one. At an inert $p$, each $z_j$ is a unit: a primitive polynomial of degree less than five has a nonzero reduction evaluated at the degree-five root. Each $\log(2+|\operatorname{Norm}z_j|)$ is $O(L\log(2L))$ by the elementary bounds on the coefficients and roots of $F_{T_i}$.

Let $E_i$ be the compositum over $K_i$ of the quadratic extensions for all conjugates of the $c_j$. This is Galois over $\mathbb Q$, abelian over the degree-five $K_i$, with $[E_i:K_i]\ge2^w$. Every individual quadratic character over $K_i$ in this compositum has finite conductor norm at most $\exp(O(w L\log(2L)))$. In fact each conjugate of $c_j$ is represented modulo squares by a conjugate of the algebraic integer $\sigma(z_j)z_j$. A product of at most $5w$ such elements has norm with logarithm $O(wL\log(2L))$. The relative quadratic discriminant divides the principal ideal generated by four times this product. All ramified rational primes divide the field discriminants, 2 or some $\operatorname{Norm}z_j$ and thus are smaller than the long partner interval.

## Counting the unusable partners for all parameter words at once

Fix an admissible $t$. The combined field of the $K_i$ for $i\in I_p(t)$ is abelian over $\mathbb Q$ of degree $5^{|I_p(t)|}$. Each associated Dirichlet character has conductor dividing the product of the individual conductors, with logarithm $O(wL\log(2L))$ by the conductor–discriminant formula. In reduced residue classes modulo that product, the fraction of Frobenius vectors with no zero coordinate is $(4/5)^{|I_p(t)|}$. Brun–Titchmarsh on the rational primes gives
$$\#\{Z<q\le2Z:\ q\text{ splits in none of the inert } K_i\}\ll (4/5)^{w/2} Z/\log Z$$
provided $\log Z\ge C wL\log(2L)$ with sufficiently large absolute $C$. [Montgomery–Vaughan](https://doi.org/10.1112/S0025579300004708)

When $q$ splits in $K_i$, failure of all $w$ marks means that every conjugate of every $c_j$ is a quadratic residue at every prime over $q$. This is exactly complete splitting in $E_i$. The unconditional Chebotarev Brun–Titchmarsh theorem of Thorner–Zaman, Theorem 1.1, bounds this count by $O(2^{-w}Z/\log Z)$ in the same partner range, after choosing the constant in that range sufficiently large. Their abelian subgroup is $\operatorname{Gal}(E_i/K_i)$, the Frobenius class is the identity and the base degree is five. Their sufficient height is
$$Z\gg D_{K_i}^{246}\mathcal Q^{185}+D_{K_i}^{82}\mathcal Q^{130}5^{1230},$$
where $\mathcal Q$ is the maximum individual relative conductor norm just bounded. This dependence on $K_i$ and the maximum conductor permits $w$ proportional to $\log p$. [Thorner–Zaman, Theorem 1.1](https://arxiv.org/pdf/1606.09238#page=3)

There are fewer than $2p$ possible $t$ and $w$ fields per parameter. The union bound therefore shows that, except for $O(Zp^{-6}/\log Z)$ prime partners, **every** admissible word $t$ has an index $i$ inert at $p$ and split at $q$ with a mark $c_j$ nonsquare at some prime above $q$. The constants $200$ and 6 have slack. This uniformity in $t$ controls the dependence of the field and mark on the partner selected by the input.

## Public bit words and the full mean cost

Use the [norm quintics and marked divisor classes](quintic-field-genus-two.md#a-quintic-norm-with-a-prescribed-point) at all $w^2$ field/mark pairs. In each pair inert at $p$, at least one of the five projective charts on $\beta$ has a target of density
$$\gamma\ge\exp(-C_0 L\log(2L)/\log Y)$$
in the cube of four $k$-bit coefficients. This is the uniform vertical odd-order estimate proved from Lenstra–Pila–Pomerance there. The smooth cutoff is $Y=\exp(C L^{2/3}(\log(2L))^{4/3})$ classically, or $Y=\exp(C\sqrt{L\log(2L)})$ on ordinary RH.

For each pair $(t,\beta_0)$, apply the binary XOR construction to the four $k$-bit coefficients of $\beta_0$, trying $4^a$ shifts with $4^a\ge C_1 k^2 w^2/\gamma$ and taking the next power of four. The machine may use the stated explicit exponential majorant for $1/\gamma$. For fixed admissible $t$ a uniform $\beta_0$ has miss probability at most $(4k)^2/(4^a\gamma)$ for the selected chart of each inert field/mark pair. By the union bound at least half the $\beta_0$ hit **every** such pair under these inner shifts. The set of $(t,\beta_0)$ satisfying this condition with an admissible $t$ therefore has positive density in the $5k$-bit cube. The set depends only on $p$ and the dyadic data. For every partner outside the previous exceptional set, a hit gives a proper factor from the odd scalar and the genus-two divisor. Each candidate $(t,\beta_0)$ costs $Y^{O(1)}b^{O(1)}$. This includes the $w^2$ field/mark pairs, the inner shifts, the CRT and field arithmetic on $O(L\log(2L))$-bit data, and the gcd-checked Cantor multiplications. [Binary shift bias and exhaustive coverage](mean-time-elliptic-factoring.md#a-deterministic-search-with-a-summable-cost-per-stage)

The starting $5k$-bit word uses the low bits of $\lfloor N/2^j\rfloor$, trying every $j\le b$. Choosing $j=\lfloor\log_2p\rfloor$ in the proof makes this the low bits of $\lfloor vq\rfloor$ with $1\le v<2$. Since $Z\gg p^5$, each starting word occurs $O(Z/p^5)$ times before restriction to primes. Run an outer sequence of $4^a$ XOR shifts for $a=1,2,\ldots,5k$. The positive density target bounds the number of integer partner starts missing stage $a$ by $O(Z k^2/4^a)$. Multiply this tail by the next stage's cost $4^{a+1}Y^{O(1)}b^{O(1)}$ and sum over stages. Dividing by the number $\asymp Z/\log Z$ of prime partners preserves the claimed mean. The exceptional $O(Zp^{-6}/\log Z)$ prime partners are charged at most $\sqrt p\, b^{O(1)}$ each to an interleaved deterministic factorial-block search. Run all possible $P$ instances by round robin using only $N$. This establishes the prime-partner result.

For integer partners start with exact perfect-power and primality tests, and interleave the same factorial-block fallback. Let $U_0=\exp(C_2 L^2\log(2L))$ with $C_2$ large enough for the prime estimates on dyads down to $U_0/2$. An integer partner divisible by a prime $q\ge U_0$ that is usable for all admissible $t$ obeys the same two-reduction argument; extra prime divisors and multiplicities do not change it. The seed now uses the whole $m$ in $\lfloor vm\rfloor$, so every starting-word count remains valid. The count of partners divisible by any of the exceptional primes $q\ge U_0$ is bounded by
$$2Z\sum_{\substack{U_0\le q\le2Z\\q\ \rm exceptional}}1/q\ll Zp^{-6}(1+\log\log(2Z)),$$
summing the uniform prime bounds on dyads. If all prime divisors of $m$ are below $U_0$, the number of such partners is at most $\Psi(2Z,U_0)$. For $\log Z\ge C_3L^3$, the smoothness parameter $u=\log(2Z)/\log U_0$ satisfies $u\log u\ge 10L$ on increasing $C_3$. The classical Canfield–Erdős–Pomerance estimate gives $\Psi(2Z,U_0)/(2Z)\le p^{-3}$. Its range $U_0\ge(\log(2Z))^2$ covers all cases where $p> b^2$. If $p\le b^2$, trial division finds a factor in polynomial time. Charging these exceptional partners to the same fallback proves the asserted mean. Conditioning on $p$ being the least prime factor still leaves $\gg Z/\log Z$ eligible partners, which is sufficient for normalization. [Canfield–Erdős–Pomerance estimate, also recalled in Younis (1.7)](https://arxiv.org/pdf/2409.05761#page=5)

The finite construction used three exclusive ramification primes $11,31,41$ and three split mark primes $43,101,107$. It checked 18 quintic specializations and 162 designated local valuation patterns. Of 20,771 parameter words over the tested primes, 18,579 gave at least two inert fields. In 771 of 772 split field/partner pairs, a tested mark had unequal nonzero quadratic signs. The remaining triple was word 1, field 1 and prime 919. The asymptotic argument allows exceptional partners. Run `gp -q experiments/classical-quintic-partners.gp`. [Exact family replay](../experiments/classical-quintic-partners.gp)
