# Deterministic elliptic-curve factoring on almost all balanced semiprimes

Let $p,q$ range independently over distinct primes in $(X,2X]$, let $N=pq$, and write $b$ for the bit length of $N$. A single deterministic algorithm, given only $N$, factors a proportion $1-o(1)$ of these products within the following bounds.

| Analytic input | Bit operations |
| --- | --- |
| Classical Vinogradov–Korobov zero-free region, fixed $0<\epsilon<1/6$ | $\exp(O_\epsilon(b^{5/6+\epsilon}))$ |
| A fixed $\delta>0$ with $\Re\rho\le1-\delta$ for the nontrivial zeros of $\zeta$ | $\exp(O_\delta(\sqrt{b\log b}))$ |

The first row uses classical unconditional theorems. The second is an implication of ordinary RH. It also follows from the weaker strip $\delta=1/32$ stated for Dedekind zeta functions by Cureton–Thorner. Alpöge's November 20 theorem includes ordinary RH and Sutherland reports independent Lean checks of both the ordinary and the Dirichlet statements. The factoring argument itself needs only the ordinary strip in the second row. The proportion is relative to the indicated semiprimes at each dyadic scale. The proof allows exceptions within that population. [Cureton–Thorner, Theorem 1.1](https://hexagonmath.org/pdf/2610.00200v2#page=3) · [Alpöge's theorem](https://alpo.ge/remark.pdf) · [Sutherland's independent checks](https://math.mit.edu/~drew/grh/)

## Obtaining sufficiently many parameters at one prime

Let $L=\log X$, let $Y=\exp(L^{5/6+\epsilon})$ or $Y=\exp(C_\delta\sqrt{L\log L})$ as appropriate, and put $V=\exp(16L\log L/\log Y)$. For all but $O(XV^{-11})$ primes $p\in(X,2X]$, there are at least $\sqrt X/V^2$ different orders $n$ with

$$|n-(p+1)|\le\sqrt p,\qquad n=4m,\qquad m\ \text{odd and }Y\text{-smooth}.$$

We discard the single possible order with trace $t=p+1-n=0$. Every remaining trace is ordinary. [Proof of the odd smooth Hasse interval estimate](odd-smooth-hasse.md)

Write $D=t^2-4p$ and let $H(D)$ be the sum of $h(\mathcal O)/|\mathcal O^\times|$ over the overorders of $\mathbb Z[\pi]$, where $\pi$ satisfies $\pi^2-t\pi+p=0$. This is the elliptic-curve mass at trace $t$, weighting each $\mathbb F_p$-isomorphism class by the reciprocal of the size of its automorphism group. The mass with $E[2]\subset E(\mathbb F_p)$ is $H(D/4)$. Indeed $\alpha=(\pi-1)/2$ has integral trace $(t-2)/2$ and integral norm $n/4$. Rationality of $E[2]$ is equivalent to $\pi-1$ factoring through the separable isogeny $[2]$, hence to $\alpha\in\operatorname{End}(E)$. The order $\mathbb Z[\alpha]$ has index two over $\mathbb Z[\pi]$. The ordinary classification by endomorphism orders therefore gives the claimed restricted mass. [Lenstra, §1, especially (1.5)](https://pages.cs.wisc.edu/~cs812-1/Lenstra1987.pdf#page=4) · [Schoof, ordinary curves and prescribed rational torsion](https://doi.org/10.1016/0097-3165(87)90003-3)

The order class-number formula shows $H(D)\le4H(D/4)$. If the conductor of $\mathbb Z[\pi]$ is $2^a f$ with $f$ odd, the conductor for $D/4$ is $2^{a-1}f$. For each $g\mid f$ compare the missing order at conductor $2^a g$ to the one at $2^{a-1}g$. The ratio of the weighted class numbers is $2$ when $a>1$ and $2-\chi_{D_K}(2)\le3$ when $a=1$. Thus the extra mass is at most three times the retained mass. Lenstra's Proposition 1.9(b) gives a total mass $\gg (\#S-2)\sqrt p/\log p$ for any set $S$ of central orders. Applied to the orders above, it yields full-two-torsion mass $\gg p/(V^2\log p)$. [Lenstra, (1.7)–(1.9)](https://pages.cs.wisc.edu/~cs812-1/Lenstra1987.pdf#page=5)

Every curve with full rational two-torsion in odd characteristic is a quadratic twist of
$$E_\lambda:\ y^2=x(x-1)(x-\lambda),\qquad\lambda\in\mathbb F_p\setminus\{0,1\}.$$
In a split cubic model order the three roots, translate one to zero, and divide their differences by the second. The resulting leading coefficient gives the twist. For each $\lambda$ at most two isomorphism classes occur as its quadratic twists, each with weight at most one. For a good prime $p$, the set $J_p$ of parameters having a twist of the required order consequently has size $\gg p/(V^2\log p)\ge p/V^3$. Record for each such parameter a sign $s\in\{-1,+1\}$ of a good twist, choosing either if both work. These local sets appear only in the proof.

## Marking the point and keeping its order even at the other prime

For each public integer $c\ge2$ vary the rational mark $a$ subject to $a=cu^2$ and $a-1=(c-1)v^2$. Substituting $v=1+t(u-1)$ in the conic $cu^2-(c-1)v^2=1$ gives its second intersection
$$u=\frac{(c-1)(t-1)^2+1}{(c-1)t^2-c}.$$
The rational map $t\mapsto a$ has degree at most four and is nonconstant when $c\ne0,1$. Enumerating $4\le t\le 8H+20$ gives at least $H$ distinct rational $a\ne0,1$, after discarding poles and duplicates. Their heights are polynomial in $c,H$. For $H=\lceil V^6\rceil$ and $c\le O(b)$ all their reductions at $p,q$ are defined, distinct and different from $0,1$ for large $X$. This follows by bounding each numerator, denominator, and cross-difference by $X^{o(1)}$.

Given $a$ and $\lambda$, put
$$d=a(a-1)(a-\lambda),\qquad E:\ y^2=x(x-d)(x-d\lambda),\qquad P=(da,d^2).$$
The point satisfies the equation, and $E$ is the twist of $E_\lambda$ with squareclass $d$. At any odd prime of good reduction where $d\ne0$, the three squareclasses governing rational divisibility of $P$ by two are those of
$$ (a-1)(a-\lambda),\qquad a(a-\lambda),\qquad a(a-1).$$
These follow by substituting $x(P)$ in $x,x-d,x-d\lambda$. A point away from the three roots belongs to $2E(\mathbb F_p)$ exactly when all three differences are squares, by two-descent on a split cubic. [Bekker–Zarhin, §2](https://arxiv.org/abs/1702.02255)

Suppose that for the chosen twist sign $s$ the same $c$ satisfies
$$\chi_p(c)=\chi_p(c-1)=s,\qquad \chi_q(c(c-1))=-1.$$
If $\chi_p(a-\lambda)=s$, the twist at $p$ has the chosen sign and $P\in2E(\mathbb F_p)$. Since $\#E(\mathbb F_p)=4m$ with $m$ odd and $E[2]$ rational, its Sylow two-subgroup is $(\mathbb Z/2)^2$, so $P\bmod p$ has order dividing $m$. At $q$ the third difference is a nonsquare. Thus $P\notin2E(\mathbb F_q)$ and has even order. The conclusion at $q$ is independent of the parameter $\lambda$ whenever the curve has good reduction there.

For each fixed $c$, choose $H$ different reductions $a_i$ from the conic. Direct summation of the complete quadratic character correlations gives
$$\sum_{\lambda\in\mathbb F_p}\bigg|\sum_{i=1}^H\chi_p(a_i-\lambda)\bigg|^2=Hp-H^2.$$
The diagonal correlations are $p-1$ and the others are $-1$. If no $i$ gives a specified sign, the inner sum has magnitude at least $H-1$, since at most one term is zero. At most $O(p/H)$ parameters miss that sign. Consequently, for any fixed pair of public choices $c_+,c_-$ having the required respective characters at $p$, at least $p/V^4$ parameters in $J_p$ have a suitable mark on the corresponding conic. Call the resulting set $J_p(c_+,c_-)$. Its construction depends only on $p$ and the two constants.

The pair of signs is available for a density-one set of ordered prime pairs using only $2\le c\le b$. To prove this, recursively construct positive integers $c_i$ such that all the squareclasses $c_i,c_i-1$ are independent in $\mathbb Q^\times/\mathbb Q^{\times2}$. Choose distinct primes $r_i,s_i$ exceeding all preceding integers, and impose $c_i\equiv r_i\pmod{r_i^2}$, $c_i\equiv1+s_i\pmod{s_i^2}$. The two new odd valuations occur in different members of the new pair. Looking at the last selected index proves independence. For fixed $k$ the prime number theorem in fixed progressions gives independent uniform sign vectors for $c_1,c_1-1,\ldots,c_k,c_k-1$ as $p$ ranges over $(X,2X]$. This follows equivalently by character orthogonality for the associated independent quadratic characters. Independent selection of $p,q$ therefore gives probability $1/8$ per index for a prescribed sign $s$ at $p$ and opposite signs at $q$. Both prescribed signs are supplied except on a fraction at most $2(7/8)^k+o_k(1)$. The algorithm enumerates all these fixed $c_i$ for sufficiently large $X$. Taking the upper limit in $X$ and then sending $k$ to infinity proves the asserted density.

## Reaching the parameter from the integer input

Start at $x_0=\lfloor\sqrt N\rfloor$ and evaluate words in the four fixed integral determinant-one matrices
$$U=\begin{pmatrix}1&2\\0&1\end{pmatrix},\quad U^{-1},\quad W=\begin{pmatrix}1&0\\2&1\end{pmatrix},\quad W^{-1}.$$
Use their fractional linear action on the projective line. The subgroup they generate is non-elementary, and its reduction generates $\mathrm{SL}_2(\mathbb F_p)$ at every odd prime because powers give both elementary unipotents of coefficient one. Bourgain–Gamburd uniform expansion, applied to the lazy walk and then its quotient on $\mathbb P^1(\mathbb F_p)$, gives a fixed $0<\theta<1$ bounding its operator norm on the orthogonal complement of constants. The Cayley graph spectrum bounds that of the transitive quotient by lifting functions to the group. Kowalski supplies an explicit version if a numerical walk constant is desired. [Bourgain–Gamburd, uniform expansion](https://annals.math.princeton.edu/2008/167-2/p07) · [Kowalski, explicit expansion bounds](https://arxiv.org/abs/1201.1139)

For a set $J$ of uniform measure $\alpha$, the proportion of starts from which no word of length $\le j$ reaches $J$ is at most $\theta^{2j}/\alpha$. Indeed the $j$-step average of $1_J$ vanishes at each such start, and its squared distance from the constant $\alpha$ is at most $\theta^{2j}\alpha(1-\alpha)$. Choose $j=\lceil C\log V\rceil$ for an absolute $C$ with $\theta^{2j}\le V^{-12}$. For each eligible pair $c_+,c_-$ the miss fraction is $O(V^{-8})$. There are $O(b^2)$ choices uniformly over the dyad. The union of the missed starts has cardinality $O(pV^{-7})$ for large $X$.

For fixed $p$ and variable integer $q\in(X,2X]$, each residue of $\lfloor\sqrt{pq}\rfloor\bmod p$ occurs $O(1)$ times. The range has length $O(X)$, and each individual integer value has a fiber of bounded size because the derivative $\sqrt{p/q}/2$ is bounded below. Thus $O(XV^{-7})$ choices of $q$ miss some eligible pair of conics, even before restriction to primes. This is $o(X/\log X)$ uniformly in $p$. The character condition, smooth Hasse estimate, and this starting-point count now give density one among the ordered prime pairs. The normalization by distinct unordered products gives the same result.

## Deterministic algorithm and cost

The machine uses the displayed formulas for $Y,V$ at $X_0=\sqrt N$. Both cutoffs increase for large $X$ and $X\le X_0\le2X$ on the tested dyad. To keep all proof-side sets independent of $q$, use in the estimates only $H=\lceil V(X)^6\rceil$, $j=\lceil C\log V(X)\rceil$, and $2\le c\le\lceil\log_2(4X^2)\rceil$. The actual search includes all their required choices with $c\le b(N)$. Round a cutoff upward, for example to a power of two using an upper approximation within one unit of its base-two logarithm. This affects each cutoff by a bounded factor and allows deterministic computation in time polynomial in $b$. An arbitrary fixed real $\epsilon$ may be handled by choosing a rational exponent strictly between $5/6$ and $5/6+\epsilon$.

Form the odd scalar
$$M=\prod_{3\le r\le Y(X_0),\ r\ {\rm prime}}r^{\lfloor\log_r(2N)\rfloor}.$$
Enumerate words up to depth $j(X_0)$, $2\le c\le b$, and the conic marks from $t\le 8H(X_0)+20$. Use the word matrix as a whole to evaluate $\lambda$ at $x_0$. Every denominator, every factor defining smooth reduction, and the denominators in the group law have their gcd with $N$ checked. A proper gcd is returned immediately. If the projective denominator vanishes everywhere, or a defining factor vanishes everywhere, skip that case. Check $d,\lambda,\lambda-1$ individually for smooth reduction. In a case promised by the proof, the word lies at a finite nonsingular parameter at $p$. Any failure of smooth reduction solely at $q$ already gives a proper gcd.

Otherwise compute $[M]P$ by gcd-checked group operations. One explicit implementation represents the identity separately. With affine inputs compare $x_1-x_2$ by a gcd. At a unit use the chord formula. If both abscissae coincide, check $y_1+y_2$ and $y_1-y_2$ for a proper gcd, then use the identity for opposite points or the tangent formula for equal points after checking $2y_1$. This simulates the field operations at both primes simultaneously until a discrepancy exposes a factor. A marked point has $[M]P=O$ modulo $p$ and $[M]P\ne O$ modulo $q$, because all odd prime powers dividing $m$ occur in $M$. This discrepancy forces a nontrivial gcd. Returning both the factor found and its complementary factor gives the full semiprime factorization.

The scalar has $O(bY(X_0))$ bits and can be formed by sieving and integer multiplication in time polynomial in $bY(X_0)$. Each scalar multiplication and each word requires polynomially many bit operations in $bY(X_0)$ and $j(X_0)$. The number of candidates is at most $O(bH(X_0)4^{j(X_0)+1})$. Combining these bounds proves both time estimates. An unsuccessful capped search may report failure. One can append any total deterministic factoring algorithm to obtain complete factorization on every input, with the faster bounds established here on the density-one family.

## Relation to earlier algorithms

Lenstra's original ECM uses randomized curve and point selection. Lenstra–Pomerance's class-group algorithm gives an all-input expected running-time bound $L_N[1/2,1+o(1)]$, and their §7 treats a related density-one Hasse interval hypothesis for randomized ECM. Pomykała–Jurkiewicz study separation of the two-adic orders of marked points, with a conjectural subexponential factoring bound. Here the conic mark forces opposite parity once the three local character conditions hold, and a deterministic projective walk from a public function of $N$ supplies parameters on average over the other prime. The construction makes no claim on the worst-case size of the set of missed prime pairs beyond its density estimate. [Lenstra's ECM](https://annals.math.princeton.edu/1987/126-3/p09) · [Lenstra–Pomerance](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/rigorous.pdf) · [Pomykała–Jurkiewicz](https://arxiv.org/abs/2503.00950)

## Finite replay

Run `gp -q experiments/moving-legendre.gp` and `python3 -B experiments/moving-legendre.py`. The GP calculation enumerated 64,728 nonsingular short Weierstrass models. At 68 ordinary orders with valuation two it matched both class-number masses, including 4,012 models with full rational two-torsion. It compared the two-descent squareclasses against exhaustive doubling for 17,756 marked points, including 1,376 forced odd-order points and 9,608 forced even-order points.

At the smaller fixed smoothness bound 17, 157 of the 1,033 primes in $(10^4,2\cdot10^4]$ had empty central Hasse intervals of the specified type. The Python search factored all 210 products of two different primes in $(100,200]$ using $N$ alone at smoothness bound 11, four marks per conic and word depth two. Separately, 165 of the 210 ordered orientations exhibited the sufficient proof witness at these finite caps, with first hits at word lengths $0,1,2$ in 46, 66, and 53 cases. The blind algorithm can return a proper gcd before a full proof witness occurs. [Local arithmetic replay](../experiments/moving-legendre.gp) · [Integer-only search and Hasse counts](../experiments/moving-legendre.py)
