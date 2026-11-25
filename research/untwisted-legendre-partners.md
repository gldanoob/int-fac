# A single rational conic and deterministic time moments at each prime

Let $p$ be any prime, $Z\ge p$, $r\ge1$ a fixed integer and $b=\lceil\log_2(2pZ+1)\rceil$. On input $N=pq$ alone, with prime $Z<q\le2Z$ distinct from $p$, a deterministic algorithm has the following bound on the $r$-th root of its mean $r$-th power of the bit cost:
$$
  \left(\mathbb E_q T(pq)^r\right)^{1/r}
    \ \le\ b^{O_r(1)}\min\left\{\sqrt p,\ (1+p^r/Z)^{1/r}W_p\right\}.
$$
For every fixed $\theta>1/(4\sqrt e)$ one may take $W_p=p^\theta$ **for every prime**, using classical theorems. For example, $r=1$, $\theta=31/200$ gives $p^{0.155}\mathrm{poly}(b)$ in mean for every partner dyad, including balanced pairs. The known unrestricted algorithm can be interleaved where its input-length bound is stronger. On the primes with the subexponential central-order supply in the [zero-density theorem](zero-density-hasse-intervals.md), $W_p$ improves to $\exp(O((\log p)^{2/3}(\log\log p)^{4/3}))$ classically and to $\exp(O(\sqrt{\log p\log\log p}))$ using proved ordinary RH. When $Z\ge p^r$ even the length factor is bounded. The same bound gives a proper split for whole integer partners, also after conditioning on $p$ being the least factor. A single algorithm may be chosen for each fixed $r,\theta$.

The public list of auxiliary rationals has polynomial size in $b$. One conic suffices for a successful pair. The exceptional-partner bound holds for **every fixed $p$**.

## Exact untwisted Legendre mass

For nonzero ordinary trace $t$ with $p+1-t=4m$, $m$ odd, and $D=t^2-4p$, the number of $\lambda\ne0,1$ for which the *untwisted* Legendre curve has trace $t$ is exactly
$$
                2\big(H(D)-H(D/4)\big)\ \ge\ H(D).
$$
Here $H$ uses the automorphism weight $h(\mathcal O)/|\mathcal O^\times|$. Katz's universal elliptic family with a marked point of order four maps by a rational two-isogeny to the Legendre family with parameter $\lambda=1-4u$. The parameter correspondence is a bijection. Among curves of order $4m$, a cyclic Sylow two-subgroup gives exactly two points of order four, and a noncyclic Sylow two-subgroup gives none. The latter is precisely the full rational two-torsion condition of mass $H(D/4)$. Counting the marked curves gives the displayed equality since a point of order four has trivial stabilizer in the automorphism group for these odd characteristics. The bounded characteristics may also be handled by trial division. [Katz, §2, pp. 4–5](https://web.math.princeton.edu/~nmk/newratio33.pdf#page=4) · [Lenstra, ordinary curve masses](https://pages.cs.wisc.edu/~cs812-1/Lenstra1987.pdf#page=4) · [Auer–Top on existence in a prescribed isogeny class](https://arxiv.org/abs/math/0106273)

Gao's Corollary 4.5 already derives the trace law of the untwisted Legendre family by marking rational points of order four. At curve order $4\bmod8$, equation (6) in its proof specializes to twice the indicator that full rational two-torsion is absent. Thus the equality above follows directly from that formula and the ordinary class masses. Corollary S1.3 gives the same marking identity over finite extensions. [Gao, proof of Corollary 4.5, equation (6), and Corollary S1.3](https://hexagonmath.org/pdf/2611.00852v1#page=11)

For the inequality, let $2^a f$ be the conductor of $\mathbb Z[\pi]$ with $f$ odd and $a\ge1$. At an odd divisor of $f$ let $w_i$ be the weighted class numbers at its $2^i$ multiples. Then $w_i/w_0=(2-\chi_{D_K}(2))2^{i-1}$ for $i\ge1$ by the order class number formula. Thus $w_a-\sum_{i=0}^{a-1}w_i=(1-\chi_{D_K}(2))w_0\ge0$. Summing at all odd divisors gives $H(D)\ge2H(D/4)$. This lower bound in the untwisted family keeps a parameter set of size $\gg (|S|-2)\sqrt p/\log p$ for any eligible set of central orders $S$, by Lenstra's Proposition 1.9(b). [Exact trace replay by primitive positive definite quadratic forms](../experiments/untwisted-legendre-traces.py)

## A polynomial list for every fixed prime

For a positive integer $f>1$ put
$$
       c=\left(\frac{f+1}{f-1}\right)^2,\qquad
       c-1=f\left(\frac{2}{f-1}\right)^2 .
$$
When $f$ is a square modulo $p$ and a nonsquare modulo $q$, both $c,c-1$ are squares at $p$ and their product is a nonsquare at $q$, provided the displayed factors are units. Use the same marks $a=cu^2$, $a-1=(c-1)v^2$ and points as in the [moving-curve construction](legendre-average-factoring.md#marking-the-point-and-keeping-its-order-even-at-the-other-prime). For $\chi_p(a-\lambda)=+1$ the twist is the good untwisted class at $p$, the marked point has odd smooth order at $p$, and it has even order or gives a bad-reduction gcd at $q$. At most $O(p/H)$ parameters miss all $H$ distinct marks. For $|S|\gg\sqrt p$ take $H=\lceil(\log(2p))^3\rceil$. For $|S|\ge\sqrt P/V$ use the larger prefix in the [mean-time construction](mean-time-elliptic-factoring.md). In both cases the successful proportion $\gamma$ on the binary cube of size $2P$, $P<p\le2P$, satisfies $\gamma^{-1}=\mathrm{polylog}(p)$ or $\exp(O(\log W_p))$, respectively.

For each possible input bit length take $R=\lceil b_0^{16}\rceil$ with $b_0$ that length, and list all $f$ which are products of two distinct primes in $(R,2R]$. The $N$ on one partner dyad have at most two bit lengths. If $p$ is below the height bounds, deterministic small-factor search already gives a split in the claimed scale. More precisely each guessed prime-size dyad has a separate trial cutoff bounding all possible denominators, numerators and cross-differences for its mark prefix. It is $b^{O(1)}\mathrm{poly}(H)$. If $p$ exceeds this cutoff then $p,q>4R^2+1$ and every mark in the prefix remains distinct and well-defined.

For fixed $p$ retain the larger of the two sign classes $G$ among the auxiliary primes. Its size is at least $M/2$, where $M\asymp R/\log R$ is the number of auxiliary primes. Any partner for which $\chi_q$ takes both signs on $G$ supplies the required $f$, by multiplying one prime of each $q$-sign. This automatically gives $\chi_p(f)=+1$, whichever sign defined $G$.

For a prime $q$ failing this test one has $|\sum_{s\in G}\chi_q(s)|=|G|$. Apply the [multiplicative large-sieve moment proof](average-conic-signs.md#a-small-exception-list-of-characters) with conductor cutoff $2Z$, coefficients $[s\in G]$ and $k=\lceil 2\log(2Z)/\log(2R)\rceil$. The number of exceptional $q$ is at most $(Ck\log R)^k$, since two ordered tuples of primes have the same product only up to permutation. With $R=b_0^{16}$ and $b_0\asymp\log Z$ for $p\le Z$, this is $Z^{1/8+o(1)}$, hence $O(Z^{1/4})$. The implied constants are independent of $p$ and of its choice of majority class. This argument is used only to bound runtime. The machine tests its full public list.

The verified Dirichlet GRH also gives one prime $f\ll b^2$ directly. The two prescribed signs define a coset of index four modulo $pq$, so Theorem 1.4 of Lamzouri–Li–Soundararajan applies. [Least prime in a coset](https://arxiv.org/pdf/1309.3595#page=3)

An alternative pointwise construction uses only primes $\le Cb^2$. Include single primes as well as products of two primes as candidate values of $f$. The restrictions of $\chi_q$ and $\chi_p\chi_q$ to small primes are both nontrivial by the least quadratic nonresidue bound, with the primes chosen away from $pq$. After trial division through the cutoff this follows directly by applying the bound at conductors $q,pq$. If $\chi_q$ is nontrivial and differs from $\chi_p$ on those primes, either a single prime has signs $(+,-)$ or two primes with the same $p$-sign have opposite $q$-signs. This supplies the one-conic witness pointwise. [Lamzouri–Li–Soundararajan, §1](https://arxiv.org/pdf/1309.3595#page=2)

## Partner bits and time moments

The machine guesses $P$ and the bit shift $j$, interleaves the factorial fallback, and for each guess uses $r$ starting words. With $2^k=2P$ the words are the lowest $r$ disjoint $k$-bit blocks of $\lfloor N/2^j\rfloor$, padding by zero as needed. At stage $a$ apply all $4^a$ explicit small-bias XOR shifts to **each** starting word and try the resulting parameters. The cost is at most $4^a b^{O_r(1)}W_p^{O(1)}$ in the subexponential case. In the pointwise $p^\theta$ case it is $4^a b^{O_r(1)}p^\theta$, because $H$ is polynomial in $b$ and the length of the odd scalar at cutoff $(2P)^\theta$ is $O(p^\theta b)$. Generate the scalar by successively applying the individual odd prime powers to the marked point. The sum of their binary lengths and the cost of sieving through the cutoff are $O(p^\theta\mathrm{poly}(b))$, keeping the coefficient of $\theta$ equal to one.

Fix $j=\lfloor\log_2 p\rfloor$ for the proof. The unreduced map $q\mapsto\lfloor(p/2^j)q\rfloor$ is injective with image inside an interval of length $O(Z)$. Each $rk$-bit word occurs at most $O(1+Z/(2P)^r)$ times. For a fixed good $f$, the fraction of $k$-bit starting words missing its target at stage $a$ is $\le k^2/(4^a\gamma)$. Thus the fraction of full $rk$-bit words missing in **all** blocks is at most $(k^2/(4^a\gamma))^r$ by the Cartesian product count. This calculation averages over integer words. It makes no probabilistic independence assumption about the binary digits of primes. Take the union over the polynomially many public $f$ which are admissible for at least one partner. Their targets depend only on $p,f$ and the common mark prefix, so the number of nonexceptional partners reaching stage $a+1$ is bounded by
$$
    O\!\left((Z+p^r)b^{O_r(1)}\gamma^{-r}4^{-ar}\right).
$$
There are $O_r(b)$ stages and the cumulative cost through one is within a constant of its final geometric term, apart from the preceding polynomial overhead. Multiplication by the next stage cost to the $r$-th power cancels $4^{-ar}$. Dividing by $\gg Z/\log Z$ prime partners proves the claim on these partners. For exceptional $q$ the normalized $r$-th power of the factorial charge is at most $b^{O_r(1)}p^{r/2}Z^{-3/4}$. If $Z\ge p^r$ this is bounded, and for $Z<p^r$ it is at most $p^r/Z$ because $Z^{1/4}\le p^{r/2}$. Taking the root gives the stated bound, in parallel with the pointwise factorial cap. In the subexponential cases the constant in $\log W_p$ absorbs all fixed powers of the mark and target overhead.

[Lean proof of the one-block missed-start inequality](../formal/CubeSampler.lean) · [Independent fixed-prime, conic and multiblock replay](../experiments/untwisted-partner-moments.py)

## Whole integer partners and rare failure of the conic list

The same moment bound gives one proper split for $N=pm$ with $m$ ranging over **all integers** in $(Z,2Z]$ or over those for which $p$ is the least prime factor. Exact prime powers give their prime and multiplicity directly. On composite partners a returned factor may be composite. In particular a composite partner with many factors supplies all $r$ blocks from its full integer value, independently of which prime divisor supplies the sign separation.

Here is a more general sparseness estimate. Given any fixed $0<\varepsilon\le1/2$, replace $R=b_0^{16}$ by $R=b_0^{C}$ for a sufficiently large constant $C=C(\varepsilon)$. The number of partners that pass a polynomial trial-division cutoff and have **no prime divisor** $q\ne p$ admitting the desired $f$ is $O_\varepsilon(Z^\varepsilon)$, uniformly in $p$. To see this, use the single fixed $p$-majority set for each of the at most two cofactor bit lengths. For dyads $U<q\le2U$, $R<U\le2Z$, the moment inequality gives
$$
                |E_p(U)|\le (C_1 k\log R)^k
                  \le b^{C_2}U^{\varepsilon/2},
 \qquad k=\left\lceil\frac{2\log(2U)}{\log(2R)}\right\rceil.
$$
Indeed $k\log R\ll\log(2U)$ and $\log R\ge C(\log\log(2U)-O(1))$, since $q\le2N$. The additive one in $k$ costs a polynomial factor. Remove primes through $b^{C_3}$ with $C_3$ exceeding $C$ and $2(C_2+2)/\varepsilon$. Every remaining exceptional $m$ factors over $\{p\}\cup E$ with $E=\bigcup_{U\ge b^{C_3}/2}E_p(U)$. Then
$$
 \sum_{q\in E}q^{-\varepsilon}
   \ll b^{C_2}\sum_{U\ge b^{C_3}/2}U^{-\varepsilon/2}\ll1
$$
over the dyadic scales. The Euler product $\prod_{q\in E\cup\{p\}}(1-q^{-\varepsilon})^{-1}$ is bounded in terms of $\varepsilon$. Rankin's inequality gives at most $O_\varepsilon((2Z)^\varepsilon)$ eligible products, allowing all multiplicities. The exception set remains hypothetical in the algorithm. For $\varepsilon=1/2$ one may use the original exponent $16$, giving the required bound $|E_p(U)|\le b^{C_2}U^{1/4}$.

If any other prime factor $q\mid m$ admits the sign separation, the proof only uses good reduction at $p$ and the forced even order or bad reduction at $q$. Every earlier discrepancy across other prime factors gives a proper gcd as well. For $j=\lfloor\log_2 p\rfloor$, the same monotone starting-word map now uses $m$ in place of $q$. Its fiber count over all integer partners and the union over the possible $f$ are unchanged. For the at most $O(\sqrt Z)$ remaining partners charge the factorial time at most $\sqrt p\,\mathrm{poly}(b)$. Its normalized $r$-th power is at most a polynomial times $p^{r/2}/\sqrt Z\le 1+p^r/Z$. The subset where $p$ is the least factor has at least $\gg Z/\log Z$ members, by including all prime partners, so conditioning costs only a polynomial factor.

The finite replay tested 913 sign-separating conics and 263 constant-sign partners in its reduced auxiliary-prime list. It independently checked the two local scalar multiplications and the composite gcd in 45 cases. All 36 multiblock counts passed, covering 20,144 cube words and 20,756 integer partners. The separate trace replay checked 634 ordinary traces in 93 prime fields, using 21,345 Legendre parameters. Equality $H(D)=2H(D/4)$ occurred 54 times. The partner estimates and asymptotic mean require the paper arguments above.
