# Exact limiting miss density of a prime-index coefficient search

Let $k\ge3$ be a fixed odd prime. Choose distinct ordered primes $p,q$ in $[X,2X]$, set $N=pq$, and supply $M=a\Phi_k(p)$ to the monic polynomial search. For each fixed coefficient height $H$ and fixed positive multiplier $a$, the limiting fraction of pairs missed by the whole box is **exactly the density of primes $p$ at which every nonpure degree-$k$ polynomial in the box is reducible**. Here pure means $X^k+c$. In particular the answer is rational and independent of the second prime. When $k=3$, the statement holds separately for all four possible residue-class pairs modulo three. The earlier upper bound for an arbitrarily large supplied multiplier uses a different argument. [Polynomial search and arbitrary-multiplier theorem](cyclotomic-order-multiples.md)

### Uniformity in the extra multiplier and the box

Put $A\ge1$ and $R=A\log(2H)/\log X$, with $H\ge1$. For $R=o(1)$ the following stronger statement holds outside a fraction $O_{k,\epsilon}(R^{1-\epsilon}+X^{-1/2+\epsilon})$ of the pairs, for any $0<\epsilon<1$. **Simultaneously for every integer $1\le a\le A$ and every polynomial in the box**, the proper gcds are precisely $p$, obtained exactly at nonpure degree-$k$ polynomials irreducible modulo $p$. Thus the first successful probe is determined as well. Both $H$ and $A$ may grow with $X$. The finite exceptional fraction can be much larger than the limiting miss density when the latter is very small.

First, put $L=\operatorname{lcm}(1,\ldots,k)$ and $G=\gcd(\Phi_k(p),q(q^L-1))$. For $2\le Y\le\sqrt X$,
$$
 \Pr(G>Y)\ll_{k,\epsilon}Y^{-1+\epsilon}+X^{-1/2+\epsilon}.
$$
For $Y<d\le\sqrt X$, each of the two fixed squarefree polynomials $\Phi_k(T)$ and $T(T^L-1)$ has $O_k(1)$ roots at each prime power. CRT gives at most $C_k^{\omega(d)}$ pairs of root classes modulo $d$, enlarging the constant to account for both polynomials. The interval Brun–Titchmarsh inequality for the two primes bounds the probability that $d$ divides $G$ by $O(C_k^{\omega(d)}/\varphi(d)^2)$. Summing over $d>Y$ gives $O_{k,\epsilon}(Y^{-1+\epsilon})$. For $d>\sqrt X$, fix $p$. Its cyclotomic value has size $X^{O_k(1)}$ and therefore $X^{o(1)}$ divisors. For each such $d$, at most $d^{o(1)}(1+X/d)$ integers $q$ in the interval can be roots. This costs $X^{-1/2+o(1)}$ after dividing by the prime count. The divisor $d=G$ is covered whenever $G>Y$. Conditioning on fixed reduced classes of positive density only changes the implied constant. [Prime-power root bound](cyclotomic-supply.md) · [Montgomery–Vaughan, Theorem 2](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=3)

Write $D=M/2^{v_2(M)}$. For a unit $X$ modulo a tested polynomial $f$ over $\mathbb F_q$, its order modulo scalar units divides $q(q^L-1)$ once $q>k$. The residue field degrees divide $L$ and the nilpotent kernel is killed by $q$. If $X^D$ is scalar there, then $X^g$ is scalar for $g=\gcd(D,q(q^L-1))\le aG$. At $p$, an input of degree below $k$ or a reducible degree-$k$ input has local residue degrees at most $k-1$. Put $L'=\operatorname{lcm}(1,\ldots,k-1)$. Since $k$ is prime, $\gcd(k,L')=1$. Thus
$$
 \gcd(\Phi_k(p),p(p^{L'}-1))=\gcd(k,p-1)\le k,
$$
by $\gcd(p^k-1,p^{L'}-1)=p-1$. The corresponding $g$ at $p$ is at most $ka$.

Every coefficient of $X^g\bmod f$ over the integers has absolute value at most $(1+kH)^g$ by iterating multiplication by $X$ in the power basis. Choose $Y=\log X/(2A\log(1+kH))$. On $G\le Y$ and for $X$ sufficiently large, both small exponents above have coefficient bounds strictly below $X$. A scalar reduction at either prime with such an exponent is a scalar identity over the integers, hence $X^D$ is scalar at the other prime too. If $f(0)=0$, a pure power of $X$ is nilpotent at both. Otherwise the zero-root component and a unit component both occur at both primes since $H<X$. Their powers cannot be a common scalar.

A degree-$k$ polynomial irreducible at $p$ gives a scalar $X^D$ at $p$ by the finite-field norm, since $\Phi_k(p)$ is odd. If such a polynomial admits $X^g$ scalar over the rationals for any positive $g$, all of its conjugate roots have the same absolute value. Take a real root $u$, which exists in odd degree. Its $k$th power is rational because $|u|^k$ is the absolute value of its nonzero integer norm. Its minimal polynomial is then $X^k-u^k$. A nonpure irreducible at $p$ therefore cannot give a scalar at $q$ on the good pairs. For a pure irreducible, $k\mid p-1$ because otherwise taking $k$th powers is bijective on $\mathbb F_p$ and the polynomial would have a root. Then $k\mid D$ and the pure polynomial gives a scalar at both primes. This proves the uniform assertion.

### Multipliers up to a power of the input primes

An average over the primes gives a stronger uniform range. Write $F_H=(2H+1)^k\log(2H)$. When $F_H A^2=o(X)$, the whole-box prediction holds simultaneously for all $a\le A$ outside a fraction
$$
 O_{k,\epsilon}\left((F_H A^2/X)^{1/3-\epsilon}+X^{-1/2+\epsilon}\right)
$$
for any fixed $0<\epsilon<1/3$. In particular a fixed cubic box retains its exact limiting miss density for **any pair-dependent extra multiplier up to $X^{1/2-\delta}$**, with arbitrary fixed $\delta>0$. The corresponding total supplied value may be much larger than $p^2+p+1$.

For each box polynomial and each $1\le j\le Z$ for which $X^j\bmod f$ is nonscalar over the integers, take one nonzero nonconstant coefficient. The log absolute value of their product is $O_k(F_H Z^2)$ by the power-basis bound. Thus at most $O_k(F_H Z^2/\log X)$ primes from the interval can turn any of those nonscalar powers into a scalar. The exceptional fraction for either prime is $O_k(F_H Z^2/X)$. Outside this set a small local exponent $g\le Z$ suffices for exactly the same proof as before. Take $Z=(AX/F_H)^{1/3}$ and apply the gcd tail at $Y=Z/A$. The covered prime's reducible exponent is at most $kA\le Z$ for sufficiently large $X$.

Restrict the scan to nonpure monic polynomials of degree $k$ **irreducible over the rationals**. Such polynomials already contain all the predicted successful probes. For this scan the same prediction remains exact in the wider range
$$
                  F_H A^{k/(k-1)}=o(X).
$$
At fixed cubic height this permits $A\le X^{2/3-\delta}$. To prove it, let $\alpha_0,\ldots,\alpha_{k-1}$ be the roots of one such polynomial. The $k-1$ ratios $\alpha_i/\alpha_0$ for $i>0$ are multiplicatively independent modulo roots of unity. Indeed the transitive Galois group contains a $k$-cycle. Its rational permutation representation on the coefficient vectors of sum zero is irreducible because $\Phi_k$ is irreducible over $\mathbb Q$. The relation kernel in this space, with multiplicative relations taken modulo torsion, is invariant. If it were the whole space, every ratio would be torsion and the real-root argument above would force the polynomial to be pure.

If a reduction is scalar at some $1\le j\le Z$, the reductions of all these ratios at any prime above it lie in a cyclic group of order at most $Z$ inside a finite field. Take $T=\lceil Z^{1/(k-1)}\rceil$. Two of the $(T+1)^{k-1}$ products with exponent vectors in $[0,T]^{k-1}$ must coincide. There are only $O_k(T^{k-1})$ possible nonzero difference vectors. For each, clear the denominators of the relation to get a nonzero algebraic integer divisible by the chosen prime ideal. The log norm of this difference is $O_k(T\log(2H))$ since the roots have absolute value at most $1+H$ and the splitting field has degree at most $k!$. The primes exceed $H$, so the original roots are units at them. Multiplying the norms and summing over the box costs $O_k(F_H Z^{k/(k-1)})$ in log size. The exceptional fraction is therefore bounded by
$$
 O_{k,\epsilon}\left(F_H Z^{k/(k-1)}/X+(A/Z)^{1-\epsilon}+X^{-1/2+\epsilon}\right).
$$
Choose $Z=(AX/F_H)^{(k-1)/(2k-1)}$. This argument counts collisions of bounded products in a group modulo a prime, as in classical multiplicative-order estimates. [Erdős–Murty and Pappalardi group-order bounds, stated in Elsholtz, Lemma 4.1](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/44403B3C5D401C6AAF9A70C0FCA8E097/S000497271600023Xa.pdf)

A multiplier common to the entire input interval can be much larger. For fixed $H$ let $a=a(X)$ satisfy $\log(2a)=X^{o(1)}$. The same one-prime limit holds. For either fixed polynomial $P(t)=t(t^J-1)$ used in the local exponents, the prime-power root estimate and Brun–Titchmarsh give
$$
 \mathbb E_t\log\gcd(a,P(t))
 \ll_k 1+\sum_{\ell\mid a}\frac{\log\ell}{\ell}
              +\frac{\log(2a)\log X}{\sqrt X}
 \ll_k 1+\log\log(3a)+X^{-1/2+o(1)} .
$$
For prime powers above $\sqrt X$ use the uniform root count and sum the log weights over the prime powers dividing $a$. For the middle sum split at $\log(3a)$ and apply the elementary weighted Mertens estimate below the split. Markov's inequality makes both gcds smaller than $X^{1/12}$ with probability tending to one. Apply the cross-prime gcd tail with this same threshold, and the coefficient-product argument with $Z=kX^{1/6}$. The proof also covers a uniformly sampled independent multiplier in $[1,B]$ **for any $B$**, with no upper bound on its bit length. In that case $\Pr(d\mid a)\le1/d$. The expected log gcd above is $O_k(1)$: the small prime-power sum is bounded by $O_k(\sum_{\ell^j}\log\ell/(\ell^j\varphi(\ell^j)))$, and at fixed $t$ the large powers contribute at most $X^{-1/2}\log|P(t)|$.

For a fixed field, testing a polylogarithmic box of elements together gives an exact criterion for every multiplier, with a power-saving exceptional prime count. [Small algebra generators and the supplied-order test](small-algebra-generators.md)

### The one-prime density

For fixed $H$, take the compositum of the splitting fields of all nonpure irreducible degree-$k$ box polynomials. Off finitely many bad primes, a polynomial is irreducible modulo $p$ exactly when Frobenius permutes its roots in one $k$-cycle. The desired one-prime density is the fraction of group elements with no such cycle in any of the projections, conditionally on the restriction to a fixed cyclotomic field when congruences are prescribed. Chebotarev applies in the dyadic interval by subtracting the prime counts at its endpoints. The second prime has no effect on this limit. In the cubic case both specified $p$ branches have density at least $\exp(-O(H^3))$: in the compositum with $\mathbb Q(\zeta_3)$ take the identity for $p\equiv1$ or complex conjugation for $p\equiv2$. Their projections have order at most two. There are $O(H^3)$ polynomials and each splitting field has degree at most six. [Chebotarev density theorem](https://websites.math.leidenuniv.nl/algebra/Lenstra-Chebotarev.pdf)

At the other end, the fixed-conductor cubic construction gives $m\gg H^2/\log(2H)$ pairs of distinct quadratic resolvents $\ell,-3\ell$, each with a nonpure cubic representative. A cubic field with either of these resolvents cannot have a pure representative, since a pure cubic has quadratic resolvent $-3$. On the branch $p\equiv2\pmod3$ exactly one sign in each pair is positive. Missing all these cubics costs at most $3^{-m}$ by independence of the distinct cubic blocks over the quadratic data. On $p\equiv1\pmod3$ the two signs agree, and the signs across the $m$ different primes $\ell$ are independent. Each positive pair costs $1/9$ and each negative pair costs one, giving at most $(5/9)^m$. These bounds concern the limiting one-prime density. [Fixed-conductor construction and independence](cubic-resolvent-profiles.md#bounds-as-the-coefficient-height-grows)

The modular replay compares 39,720 literal polynomial gcds to the one-prime prediction for indices three and five, including multipliers $1,2,3,5$. All 89 pair/multiplier choices passing the integer coefficient certificate agree probe by probe. Nine small choices exhibit an actual discrepancy outside the certificate. The asymptotic estimate is a proof about prime pairs. [Exact modular replay](../experiments/prime-index-misses.gp)

### Cubic probabilities through height five

The two columns give limiting miss probabilities conditional on the covered prime's residue modulo three. The first row is exact, and the other rows are rounded. The checker computes all ten as reduced fractions.

| Height | Distinct cubic fields | $p\equiv1\pmod3$ | $p\equiv2\pmod3$ |
|---:|---:|---:|---:|
| 1 | 3 | $8/27$ | $8/27$ |
| 2 | 18 | $3.27747\times10^{-4}$ | $3.48892\times10^{-4}$ |
| 3 | 56 | $5.01783\times10^{-12}$ | $2.44874\times10^{-10}$ |
| 4 | 106 | $2.86183\times10^{-21}$ | $9.79461\times10^{-20}$ |
| 5 | 213 | $2.39211\times10^{-40}$ | $2.39950\times10^{-37}$ |

Enumerate nonpure irreducible box polynomials and identify their fields with PARI's `polredabs`. For each quadratic sign profile weight absence of an inert cubic by $3^{-\sum w_K}$ over the positive resolvents, with $w_K$ the dimension of the joint cubic kernel over its quadratic resolvent. At $K=\mathbb Q(\sqrt{-3})$ the fields here are pure cubic fields with nonpure generators in the box. Kummer theory computes their joint rank from the radicands modulo rational cubes. A rational number that becomes a cube in this quadratic field was already a rational cube, by the norm and coprime degrees. For $K=\mathbb Q(\sqrt{-51})$ the three normal closures have relative conductors $(2),(3),(6)$ and the ray group modulo $(6)$ has 3-rank two. Any two distinct degree-three extensions are independent over $K$, giving rank two for the triple. Every other noncyclic block has at most two distinct fields. The cyclic cubic fields of conductors $7,9,13,19$ contribute a factor of $1/3$ each when present. Their conductors are pairwise coprime and their cubic characters remain uniform after conditioning on the quadratic signs. The joint noncyclic cubic blocks remain independent over this abelian data by the commutator argument. Integer sum-product elimination over the quadratic signs gives the entries shown. [Block independence proof](cubic-resolvent-profiles.md#several-galois-fields-with-separate-artin-conditions)

From the repository root run `gp -fq experiments/cubic-miss-fields.gp | python3 -B experiments/cubic-miss-density.py`. Setting `CUBIC_DENSITY_BRUTE=1` for GP and passing `-s 64000000` also checks the height-one and height-two fractions by independent CRT enumeration. Among 8,908 primes on each branch from 1,000 through 200,000, four on each branch had no inert height-two cubic. [Field and conductor checks](../experiments/cubic-miss-fields.gp) · [Exact rational probabilities](../experiments/cubic-miss-density.py)

### When the supplied multiple covers both primes

Suppose $M=a\operatorname{lcm}(\Phi_k(p),\Phi_k(q))$. For fixed $H$ and $a$, the limiting missed fraction is exactly the probability that two independent prime Frobenius elements have **the same irreducibility bits on every nonpure degree-$k$ polynomial**. Congruence branches at the two primes can be specified independently. This gives a different answer from covering only $p$.

Inert degree-$k$ probes give a scalar at either covered prime. For a reducible probe at $p$, the projective exponent common to $M$ and $p(p^{L'}-1)$ is at most $ka\gcd(\Phi_k(q),p(p^{L'}-1))$, and the symmetric bound holds at $q$. Apply the same cross-prime tail in the two directions. Outside the small projective-order exceptions, scalarity at a reducible prime is an integer scalar identity, as before. A nonpure rationally irreducible polynomial of degree $k$ cannot have such an identity. If a pure polynomial is irreducible at either prime, its $k$th power is scalar and $k\mid M$. Thus precisely the probes where the irreducibility bits differ split the pair, returning the prime where the probe is inert. The larger pair-dependent multiplier ranges above carry over with the factor $k$ absorbed in the constants.

The cubic probabilities below are exact rational limits rounded for display. At height one all entries are exactly $125/729$.

| Height | $p,q\equiv1$ | One prime in each branch | $p,q\equiv2$ |
|---:|---:|---:|---:|
| 1 | 0.171468 | 0.171468 | 0.171468 |
| 2 | $2.56593\times10^{-5}$ | $2.51550\times10^{-5}$ | $2.56918\times10^{-5}$ |
| 3 | $4.36706\times10^{-14}$ | $5.47656\times10^{-16}$ | $2.20049\times10^{-13}$ |
| 4 | $1.01073\times10^{-24}$ | $5.45844\times10^{-29}$ | $6.70013\times10^{-24}$ |
| 5 | $1.38665\times10^{-46}$ | $2.53094\times10^{-56}$ | $7.88736\times10^{-45}$ |

All branches in this table are modulo three. Conditional on the two quadratic sign profiles, each resolvent block of rank $w$ gives match probability one for two negative signs, $3^{-w}$ for opposite signs, and the collision probability of the ternary zero patterns for two positive signs. With independent field directions the latter is $(5/9)^w$. In the $-3$ block the radicand valuation vectors give the linear forms. In the $-51$ triple they may be taken as $u,v,u+v$ since any three distinct lines in the dual ternary plane are equivalent up to a basis and rescaling. Each cyclic conductor contributes $5/9$. Exact sum-product elimination now uses two independent values of each quadratic sign. At heights one and two, an independent Walsh calculation averages squared or mixed Fourier coefficients of the single-prime bit patterns and agrees with this result. Direct checks at indices three and five compare a further 22,230 modular powers to the predicted prime and detect both orientations. [Exact profile collision replay](../experiments/cubic-miss-density.py) · [Direct two-prime powers](../experiments/prime-index-misses.gp)

A certified balanced example reaches height six. Both primes have 488 bits, with $q/p$ between 1.10 and 1.11. Their two cyclotomic values have gcd 13. Supply their least common multiple $M$, which is coprime to $p(p^2-1)q(q^2-1)$. All **1,452** monic quadratic and cubic probes at height five give trivial gcds. Exactly 178 cubics in that box are irreducible at both primes, with matching bits on every cubic. The first height-six split is $p$ at $X^3+3X^2-6X-6$. The example came from matching two primes with the same irreducibility pattern on a prescribed height-five quadratic profile. The certificate tests both primes, the exponent conditions, the complete box and the next witness directly. It uses the two-order multiple above. [Exact primes and PARI/GP replay, `checkDualCubicHeightFive()`](../experiments/cyclotomic-multiples.gp)

### How far apart exact cubic orders must be

Put $H(t)=t^2+t+1$. For distinct primes $p>q\ge5$, if $H(q)\mid H(p)$ then
$$
                 H(p)/H(q)\ge19,\qquad p>\sqrt{19}\,q .
$$
The integer quotient bound is sharp: $H(163)=19H(37)$. Consequently an exact single supplied order cannot cover both full orders on *any* balanced pair $q<p\le2q$. The balanced height-five example above explicitly uses their least common multiple. This obstruction says nothing about local elements whose projective orders are proper divisors of $H(q)$.

Every prime factor of $H(p)$ is one modulo three except for 3, which has valuation at most one. Indeed $p$ has multiplicative order three modulo such a prime unless $p\equiv1$ there, in which case the prime divides 3. Thus the only integer quotients strictly between 1 and 19 are $3,7,13$. They are all $H(t)$, $t=1,2,3$. In each case $tq<p<(t+1)q$, by comparing $H(t)H(q)$ with $H(tq)$ and $H((t+1)q)$. For the upper comparison their difference in the order $H((t+1)q)-H(t)H(q)$ is $t(q+1)(q-t-1)>0$. Reduction modulo $q$ then gives $(p-t)(p+t+1)\equiv0$. Since $t+1<q$, the only possible primes in that interval would be $t(q+1)$ and $(t+1)(q-1)$, both even. Finally $(2p+1)^2=m(2q+1)^2+3(m-1)$ for the quotient $m$, giving the stated size inequality.

There is also an instance-level bound for very close primes, with no exceptional-density qualification. Write $s=p-q\ne0$. Then
$$
 \gcd(H(p),H(q))\le |s|(s^2+3),\qquad
 \gcd(H(p),q(q^2-1))\le s^2(s+1)^2+3\quad\text{if }q>H(s).
$$
The first follows from $H(p)-H(q)=s(2q+s+1)$ and $(2q+1)^2=4H(q)-3$. For the second, $q\nmid H(p)$ because $H(p)\equiv H(s)\bmod q$. The factors from $q-1,q+1$ divide $H(s+1)$ and $H(s-1)$ respectively, whose product is $s^2(s+1)^2+3$.

For the one-order search with $M=aH(p)$, use $E=\max(3,|s|(s^2+3),s^2(s+1)^2+3)$. If $q>H(s)$ and $(1+3B)^{aE}<\min(p,q)$, the height-$B$ probes return exactly $p$ on the nonpure cubics irreducible at $p$. A cubic irreducible at $q$ has projective exponent dividing $H(q)$. Every reducible cubic and quadratic there has projective exponent dividing $q(q^2-1)$ on its unit components. The covered prime's reducible exponent contributes at most $3a$. The integer scalar coefficient argument from the one-order theorem now applies to every probe. In particular this gives a uniform deterministic certificate at fixed height and multiplier for $|p-q|=o((\log q)^{1/4})$. The numerical replay checked the shifted orders at 136,592 prime pairs, including 1,076 pairs satisfying the extra $q>H(s)$ bound. [Shifted gcd and extremal quotient replay](../experiments/prime-index-misses.gp)

### Optimal fixed probe order for one covered prime

For every odd prime index $k$, a prescribed list of $j$ polynomial probes of degrees at most $k$ misses at least a limiting fraction $k^{-j}$ of the balanced inputs in the one-prime regime above. One fixed infinite list attains equality at **every prefix**. In particular, the optimal limiting mean number of probes through a growing cutoff is $3/2$ for cubics and $5/4$ for quintics. This counts modular polynomial tests, with the same list for every input. An algorithm that chooses its polynomial from the numerical values of $N$ or $M$ is outside this comparison.

To prove the lower bound, discard pure and rationally reducible probes, and those of degree below $k$. For the remaining $s\le j$ polynomials, let the joint Galois group act on the product of their root sets, of size $k^s$. An element fixing a tuple fixes a root of each polynomial, so all probes miss on its Frobenius class outside the exceptional fraction. The mean number of fixed tuples over the group is its number of orbits, at least one. Since an element fixes at most $k^s$ tuples, the proportion fixing any tuple is at least $k^{-s}$. For cubics the bound holds separately on both classes modulo three. Include the third roots of unity in the compositum and take the subgroup fixing them. On the nonidentity coset the mean number of fixed tuples equals the number of subgroup orbits preserved by the coset, by counting each fixed pair on its orbit. An involution permutes these orbits, and their total population is odd, so at least one orbit is preserved. The identity coset has the ordinary orbit count. [Coset orbit-counting identity, Fulman–Guralnick, Lemma 7.1](https://arxiv.org/abs/math/0208022)

For the attaining sequence, list the primes $\ell_i\equiv1\pmod{2k}$ in order and take the defining polynomial of the degree-$k$ Gaussian period of conductor $\ell_i$. The periods have trace $-1$, so their polynomials are nonpure. Off their polynomial discriminants they are reducible at $p$ exactly when $p$ is a $k$th power modulo $\ell_i$. This occupies $1/k$ of the reduced classes independently at each conductor. The CRT and the prime number theorem in fixed progressions give the exact prefix survival $k^{-j}$, also after conditioning on either prime's reduced class modulo $k$. The Gaussian-period fields and their construction are classical. [Bach–Shallit, §§3–4](https://www.ams.org/journals/mcom/1989-52-185/S0025-5718-1989-0947467-1/S0025-5718-1989-0947467-1.pdf)

There is a quantitative cutoff. Let $m$ be maximal with $Q_m=\prod_{i\le m}\ell_i\le\sqrt X$. Then $m\asymp_k\log X/\log\log X$ by the prime number theorem in the fixed progression. For *every* $j\le m$ the interval Brun–Titchmarsh bound summed over the $\varphi(Q_j)/k^j$ surviving classes gives an $O_k(k^{-j})$ fraction. The largest conductor is $O_k(\log X)$, so the coefficients of all these fixed-degree periods and their discriminants are $(\log X)^{O_k(1)}$. The rationally irreducible box estimate therefore contributes a single exceptional fraction $O_{k,\delta}(X^{-\eta})$ for some $\eta>0$, uniformly for pair-dependent $a\le X^{(k-1)/k-\delta}$. The cutoff misses at most $\exp(-c_k\log X/\log\log X)$ of the pairs for sufficiently large $X$. A cutoff using $N^{1/8}$ in place of $\sqrt X$ gives the same order and needs only the input. For each fixed prefix the actual survival tends to $k^{-j}$. Summing the geometric majorant and the total $O(mX^{-\eta})$ error shows that the expected truncated number of tests tends to $k/(k-1)$. The fixed-prefix lower bound proves optimality for any fixed ordered list taken to a cutoff tending to infinity.

For the first four cubic conductors the exact survivor counts out of 38,880 reduced CRT classes are 12,960, 4,320, 1,440 and 480. For the first three quintic conductors they are 2,400, 480 and 96 out of 12,000. Direct finite-field irreducibility agrees with the residue test on all 14,658 prime/polynomial combinations checked. [CRT and polynomial replay](../experiments/prime-index-misses.gp)

### Optimal cubic probes when both orders are supplied

For $M=a\,\mathrm{lcm}(\Phi_3(p),\Phi_3(q))$ the optimum depends on information visible from $N=pq$ alone. With the single-order ranges and normalizations above, the following are the smallest limiting miss probabilities of any prescribed prefix of $j$ cubic or quadratic probes. Each row is attained at every prefix of one list.

| Available congruence information | Minimum prefix miss probability | Limiting mean through the growing cutoff |
|---|---:|---:|
| No branching on $N$ | $(5/9)^j$ | $9/4$ |
| $N\equiv 1\bmod3$, or either specified equal pair of branches | $(5/9)^j$ | $9/4$ |
| $N\equiv 2\bmod3$, the mixed pair of branches | $3^{-j}$ | $3/2$ |

Choosing the list according to $N\bmod3$ gives overall optimal mean **$15/8$ probes** among such fixed lists. The two congruence outcomes have equal limiting weight. The numerical sizes of $N$ and $M$ supply no other branching information in this comparison.

For the first two rows, assign $X_i=(-1)^{I_i}$ to each probe, with $I_i$ its nonpure cubic irreducibility bit. For every subset $S$ of probes, $3^{|S|}\mathbb E\prod_{i\in S}X_i$ is an **odd integer**, both without conditioning and separately on either branch modulo three. To see this expand $\prod(1-2I_i)$. For nonempty $T\subset S$ consider the simultaneous inert event at those probes. Ignore a zero event. On the selected rationally irreducible cubics, the joint group embeds in $S_3^{|T|}$. Its sign image is an elementary binary group and its sign kernel is an elementary ternary group of rank $w\le |T|$. All inertness requires positive signs. Given the branch modulo three, the all-positive sign probability is either zero or $2^{-d}$ for $d\le |T|$. If the branch field lies in the joint splitting field, its quadratic character factors through the sign image. Otherwise it is independent. The remaining probability is $v/3^w$ where $v$ counts kernel vectors nonzero in each selected coordinate. Inversion pairs them without a fixed point, so $v$ is even. Multiplication by $(-2)^{|T|}3^{|S|}$ now gives an even integer. The empty term contributes the odd integer $3^{|S|}$. Permanently reducible or pure probes have zero bit and obey the same bound.

For two independent primes with the same law, the Walsh identity for pattern collision is
$$
  2^{-j}\sum_{S\subseteq[j]}
       \left(\mathbb E\prod_{i\in S}X_i\right)^2
       \ \ge\ 2^{-j}(1+1/9)^j=(5/9)^j .
$$
This applies separately to two primes on either equal branch and to two unconditioned primes. Independent cyclic periods attain equality since each bit has probabilities $1/3,2/3$ and the conductors are disjoint. At the logarithmic cutoff above, summing Brun–Titchmarsh for the two primes over the matching pairs of reduced CRT classes gives an $O((5/9)^j)$ survival bound for every prefix.

For unequal branches fix *both* quadratic sign profiles in the full joint field. On either profile choose a lift $g$ of its signs and replace it by $g^3$. Each positive coordinate of this lift is the identity, and its signs are preserved. Other lifts then correspond to a uniform vector in the common ternary kernel. On a positive coordinate the inertness bit is the nonvanishing of one linear form on that vector; on a negative coordinate it is zero. To force a match, require equality of the two linear forms for each coordinate positive at both primes, or vanishing of the form on the positive side when exactly one is positive. These are at most $j$ homogeneous equations on two independent ternary vectors. Their joint probability is at least $3^{-j}$. Conditioning on an extra branch modulo three preserves the ternary kernel, as above.

To attain the bound on the mixed branch, use $(X-1)^3-\ell_i$ for distinct primes $\ell_i\ne3$. At the prime two modulo three they always have a root. At the prime one modulo three all the first $j$ have a root precisely when that prime splits completely in $\mathbb Q(\zeta_3,\sqrt[3]{\ell_1},\ldots,\sqrt[3]{\ell_j})$. The $\ell_i$ are independent modulo cubes over $\mathbb Q(\zeta_3)$ by valuations, so conditional splitting costs $3^{-j}$. For the growing-cutoff statement choose the first primes other than three and stop when their product exceeds a small fixed power of $X$ (omit that last prime). Over the fixed quadratic base, each cubic character has conductor dividing the polynomial discriminant ideal $(27\ell_i^2)$. The conductor of a product divides the least common multiple of the individual conductors, so the maximum conductor norm is at most $27^2(\prod_{i\le j}\ell_i)^4$. Thorner–Zaman's abelian Brun–Titchmarsh bound therefore makes the fraction of primes splitting completely $O(3^{-j})$ uniformly through this cutoff. There are $\asymp\log X/\log\log X$ probes of polylogarithmic coefficient height. The exceptional fraction for the actual gcds is again a negative power of $X$ for $a\le X^{2/3-\delta}$ on these rationally irreducible probes. Summing the prefix survival probabilities proves the mean and gives cutoff failure $\exp(-\Omega(\log X/\log\log X))$. [Thorner–Zaman, Theorem 1.1](https://arxiv.org/pdf/1606.09238#page=3)

An independent finite check enumerates all 60 subgroups of $S_3^2$ and all their index-two subgroups with transitive coordinate projections in the original group. Across 37 same-law comparisons and 12 mixed-coset comparisons, the exact two-probe minima are $25/81$ and $1/9$. It checks the odd scaled Walsh coefficients on every selected coset. [Exact enumeration](../experiments/cubic-miss-density.py)
