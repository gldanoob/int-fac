# Second parallel search

Work on November 24, 2026. The target is a deterministic bound below $2^{O(b/\sqrt{\log b})}$ on every $b$-bit input in the sense of improving the logarithmic saving exponent. The [first search](swarm-research.md) describes the coefficient and order computations that would suffice. This round examines methods of performing them. No improved all-input exponent has been established here. [Leaderboard and model](https://bigospeedrun.com/integer-factoring)

## Results inherited from the reference repository

| Upstream result | How this search uses it | Scope of the local check |
| --- | --- | --- |
| The theorem at the leaderboard commit gives deterministic smallest-prime-factor computation with logarithmic saving exponent $1/2$. Its constructor uses a prefix-count evaluator. | This is the baseline for every proposed improvement. | The leaderboard reports a kernel rebuild at commit e91442d3. The local run checks two much smaller lemmas. [Upstream theorem](https://github.com/1337isnot1337/integer-factoring/blob/e91442d3162cae7f775e008efb2ea998c4478344/formal-appendix/HalfTheorem.lean) |
| In namespace IntegerFactoring.HalfPad, the definition padExponent contains $\lfloor P^2\lambda/r\rfloor+1$. The lemma half_need_le_padExponent supplies an explicit sufficient pad for the specified evaluator schedule. | Both network arguments retain this specific pad. Prices derived for other evaluators would need separate analysis. | RawClique.lean checks the arithmetic step in the raw-message lower bound. GP checks partial inverse transforms and unit determinants in round two. [Upstream pad arithmetic](https://github.com/1337isnot1337/integer-factoring/blob/e91442d3162cae7f775e008efb2ea998c4478344/formal/HalfPad.lean) |
| The weight-one coefficient is a normalized character sum over divisors. Upstream already recovers divisors via odd moments on squared divisor nodes. | The first handoff evaluates the unnormalized integral coefficient under selectable reductions to obtain scalar moments, then locates the smallest divisor by a definiteness test. Round two investigates linear digit evaluation of those scalars. | GP tested reconstruction from supplied coefficients and evaluated the displayed rank witnesses directly. Computing a coefficient at an arbitrary input within the target bound remains open. [Upstream coefficient](https://github.com/1337isnot1337/integer-factoring/blob/main/research/sparse-faithful-character.md) · [Upstream moment recovery](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/divisor-moment-recovery.md) |
| The small-index theorem gives smooth density on subgroups of index at most $D^\kappa$ for $\kappa<1/4$ under the principal split-prime estimate. For cosets the proof requires the full pinned character estimate and $\kappa<1/64$. | A class-group selector can use this density once the target index is bounded. A deterministic first-hit estimate still requires control of gaps on the actual orbit. | These are upstream analytic hypotheses and results. The local class-group runs measure finite orbits. [Density and row-change consequences](https://github.com/1337isnot1337/integer-factoring/blob/main/research/small-index-smooth-density.md) |

## Separating equal elliptic point orders

For an odd semiprime $N=pq$ try the two cubics $f_4(x)=x^3-x$ and $f_3(x)=(x-1)^3+1$. Choose an integer $s$ and the marked point $P=(s,1)$ on $f(s)y^2=f(x)$. A proper $\gcd(6f(s),N)$ already splits the input. Skip the seed if this gcd is $N$. Otherwise the curve has good reduction at both primes. Compute $[m]P$ on the projective $x$-line, obtaining $(X:Z)$. The gcd of $Z$ with $N$ detects infinity at one prime. For each rational root $r$ of $f$, the gcd of $X-rZ$ with $N$ detects the point $(r,0)$ at one prime. The homogeneous coordinates cannot both vanish modulo a good prime for the given ladder with starting abscissa a unit. Roots $0,1,-1$ serve for $f_4$ and root $0$ for $f_3$. [Montgomery on elliptic-curve arithmetic](https://doi.org/10.1090/S0025-5718-1987-0866113-7)

Take $N=10403=101\cdot103$, $f=f_4$, $s=2$. The point has order 52 at **both** primes, as checked independently on $y^2=x^3-36x$ at $(12,36)$. Thus for every scalar the infinity gcd is either 1 or $N$. Nevertheless $[26]P$ gives $(8989:590)$ modulo $N$. Its denominator is a unit, $\gcd(8989,N)=101$, and $\gcd(8989+590,N)=103$. The two reductions reached distinct rational points of order two. The composite-modulus calculation needs neither prime as input.

**Choice of scalars.** Put $M_B=\operatorname{lcm}(1,\ldots,B)$. Try $M_B$ and each $M_B/\ell^j$, where $\ell$ is prime and $1\le j\le v_\ell(M_B)$. For two different local orders this menu splits by an infinity gcd precisely when at least one of the orders divides $M_B$. Indeed, if both divide $M_B$, remove just enough of a prime power to distinguish their valuations. Intermediate powers matter. For one order-40/order-20 point on $137\cdot199$, at $B=8$ only removing a *partial* prime power gives a split among the removal tests. The point is on $f_4$ with $s=5$ and $\gcd(Z([420]P),N)=199$. On $2663\cdot6659$ all eight fixed seeds have identical first plain-hit thresholds across the two factors. The first seed has orders 333 and 3330 and $M_{64}/25$ distinguishes them.

To batch the infinity tests, build a balanced product tree of the maximal prime powers in $M_B$. At a node of product $K$, carry $[M_B/K]P$. Multiply by the sibling product to reach each child. At a leaf restore the prime factors one at a time. First test $[M_B]P$. A proper gcd terminates, a unit rules out infinity splits for its divisors, and a full gcd starts the tree. A full gcd at a child prunes the subtree for infinity checks. When rebasing a differential ladder, inspect both coordinates for a proper divisor and handle a globally infinite base or the marked point $x=0$ separately. This yields $O(B\log(2+w))$ group operations per seed for the infinity schedule, where $w$ counts the distinct prime divisors of the point order at any one factor. At depth $j$ only $\min(2^j,w)$ blocks can expand, and a balanced block has $O(B/2^j)$ scalar bits. A separate implementation checked 9,888 seed/input/cutoff combinations against prime-field orders and found 30 extra splits through the coordinate guards. At $B=1024$ on $2663\cdot6659$, the order-6 seed on $f_3$ with $s=3$ visited 15 of 343 nodes. The shared integer product tree costs $O(\mathsf M(B)\log B)$ bit operations. The checked GP code uses a fresh ladder per scalar so that it also inspects finite torsion endpoints when the full scalar has unit denominator. [Differential ladder exceptional cases](https://eprint.iacr.org/2017/212.pdf)

**Coverage.** With fixed $s=2,3,4,5$ on each curve the extended infinity schedule at $B=16$ splits all 231 pairs of distinct primes in $[101,211]$. A second set uses every pair of primes congruent to $443\bmod444$ in $[1000,20000]$, or 78 pairs. Plain $M_B$ at any integer cutoff can separate 63 of them with the eight fixed seeds. The table gives exact composite-modulus results. The variable starts are $s=\lfloor\sqrt N\rfloor+i$ for $0\le i<4$ on each curve. Each entry counts an input once. A factor exposed during the initial gcd also counts.

| $B$ | Fixed, infinity | Fixed, with torsion | Variable, infinity | Variable, with torsion | Either, infinity | Either, with torsion |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 16 | 12 | 12 | 16 | 16 | 25 | 25 |
| 32 | 33 | 33 | 24 | 25 | 47 | 48 |
| 64 | 78 | 78 | 78 | 78 | 78 | 78 |

The additional torsion split at $B=32$ is $283841653=14207\cdot19979$. On $f_4$ at $s=16850$, the point orders are 64 and 3330. At $M_{32}=144403552893600$ the two abscissas are 1 and 14076 in the respective fields. The numerator $X-Z$ exposes 14207.

## A worst-case obstruction for those two curve families

Here is an unconditional paper argument for a common menu of starts
$$s=a+uN+w\lfloor\sqrt{kN}\rfloor+d.$$
Allow a menu of $X^{o(1)}$ tuples $(f,a,w,k)$, with magnitudes $X^{o(1)}$, $k\ge1$, $w\ne0$, and every integer $|d|\le X^{1-\epsilon}$ for fixed $0<\epsilon\le1$. Selection within the menu and $u$ may depend on $N$. The primes in the construction lie in $[X,5X/4]$, so $X^{o(1)}=2^{o(b)}$. For any fixed $0<\theta<1/4$, there are infinitely many balanced inputs on which every one of these starts misses every infinity and rational 2-torsion endpoint for **all positive scalars with prime factors below $X^\theta$**.

*Supply of primes.* Use primes $p\equiv11\bmod72$, so $p+1=12r$ with $\gcd(r,6)=1$. For squarefree $d$ coprime to 6, $d\mid r$ selects one reduced residue class modulo $72d$ of relative density $1/\varphi(d)$. Bombieri–Vinogradov gives a level $X^\delta$ for any fixed $\delta<1/2$. The dimension-one lower linear sieve with $2\theta<\delta$ leaves $\gg X/\log^2 X$ primes with no factor below $X^\theta$ in $r$. [Bombieri–Vinogradov](https://kskedlaya.org/ant/chap-bombieri.html) · [Lower linear sieve](https://ford126.web.illinois.edu/Sieve_methods_notes_part6.pdf)

*Eleven exceptional residues.* For these primes both cubics and their quadratic twists have $p+1$ points. On $f_4$ the quadratic-character sum cancels under $x\mapsto-x$. On $f_3$, cubing permutes the field. Each twist has exactly 12 rational points killed by 12 because its 2,3-primary part has order 12. Delete infinity in the two twist classes. The remaining 22 points account for two per exceptional abscissa, including a point on each twist at a root of $f$. Hence exactly 11 possible residues of $s$ per cubic give a singular start or point killed by 12. All other starts have a prime at least $X^\theta$ in the local point order.

*Simultaneous avoidance.* Fix $p$, a tuple and $d$. The bad starts prescribe at most 11 residue classes modulo $p$ for $t=\lfloor\sqrt{kpq}\rfloor$. Each has $O(1+\sqrt k)$ lifts, and each lift restricts $q$ to an interval of length $(2t+1)/(kp)=O(k^{-1/2})$. Summing gives at most $D=X^{1-\epsilon+o(1)}$ bad integer partners per prime. With $m\gg X/\log^2X$ rough primes, at most $mD=o(m^2)$ unordered pairs have a bad orientation. For each remaining pair, a smooth scalar leaves a rough prime in both point orders. Even doubling that scalar leaves the point nonidentity, which excludes a finite 2-torsion hit.

*Fixed starts and intermediate gcds.* For the eight fixed starts, any nontorsion rational point excludes only finitely many primes via the denominator of $[12]P$. A rational point killed by 12 has the same order and labeled endpoint at all but finitely many good primes (exclude reductions that identify distinct rational points or distinct finite abscissas being compared). This extends the obstruction to the fixed starts in the table. For other fixed rational CM curves with a fixed set of CM fields, one can likewise pick $p\equiv-1$ modulo a fixed multiple $L$ of their discriminants and sieve $(p+1)/L$ for roughness. Smooth multiples then detect only the $L$-part. Prelisted curves and points of total explicit description length $X^{o(1)}$ require a corresponding height bound on the exceptional reductions of $[e]P$ for $e\mid L$. In contrast, if one varies discriminants up to $c b$, the common-inert construction $m=r\operatorname{lcm}(1,\ldots,\lfloor\log r\rfloor)$ with large prime $r$ and Linnik primes $p,q\equiv-1,m-1\bmod 2m$, respectively, only forces $r$ into the whole group exponent for fields with discriminant dividing $m$ (choose $c>0$ sufficiently small). An individual point can still have small order. [Lenstra](https://annals.math.princeton.edu/1987/126-3/p09) · [Linnik bound](https://doi.org/10.4064/aa150-1-4)

Intermediate additions can expose factors missed by endpoints. At $p=10000451$, $q=12000467$, $s=\lfloor\sqrt{pq}\rfloor-291743$ on $f_4$, the local orders are 7 and 6000234. Both endpoints at 60 are finite, but a binary chain computing 60 visits 7 and can split. For a common prelisted menu of chains with total index bit length $X^{o(1)}$, discard the primes $p\equiv-1\bmod\ell$ for every prime $\ell\ge X^\theta$ dividing any nonzero intermediate index or relevant sum or difference of indices. This removes $O(X^{1-\theta+o(1)})$ primes and preserves the pair count. The endpoint proof alone makes no claim about arbitrary input-dependent chains or other input-dependent curves. [Lenstra’s group law](https://pages.cs.wisc.edu/~cs812-1/Lenstra1987.pdf)

## Extracting divisor sums from digits of the index

The proposed scalar is $f_j(n)=\sigma_j(n)\bmod q$ at an odd prime level $q$ and odd exponent $j$. Its Lambert series is
$$
\sum_{n\ge1}f_j(n)x^n=\sum_{d\ge1}d^j\,x^d/(1-x^d)\quad\text{over }\mathbb F_q .
$$
One idea was to process the digits of the coefficient index through a small space of series sections, as in fast algorithms for algebraic series. Yazdani already proves nonautomaticity for these divisor sums. The following finite calculation gives a quantitative obstruction for *linear* digit representations, even when a separate representation is chosen at each maximum input length. [Yazdani](https://doi.org/10.5802/jtnb.342) · [Bostan–Christol–Dumas](https://arxiv.org/abs/1602.00545)

**A full-rank cut.** Fix an odd prime $q$ and odd $j\ge1$. Take an odd auxiliary prime $p\equiv-1\bmod q$. For $0\le u<p$ put $r_u=1+2qpu$. Choose $Q$ the least power of 2 strictly larger than all $r_u$. For each $v$ choose a prime $\ell_v$ in the reduced class
$$
\ell_v\equiv r_v p^{-2}\pmod Q,\qquad \ell_v\equiv1\pmod{qp}.
$$
Put $h_v=(p^2\ell_v-r_v)/Q$. These are nonnegative integers. In the table $T_{uv}=f_j(Qh_v+r_u)$, every index $Qh_v+r_u$ is odd and coprime to $q$. The diagonal index is $p^2\ell_v$, with $\ell_v\ne p$. Its divisor sum is $2\bmod q$ by multiplicativity. For $u\ne v$, the index is $p^2\ell_v+2qp(u-v)$, divisible by $p$ exactly once. Since $1+p^j=0\bmod q$, this entry vanishes. Thus $T=2I_p$ over $\mathbb F_q$. The construction works for all odd $j$ simultaneously.

For fixed $q$, Linnik's bound gives $\ell_v\le(Qqp)^{O(1)}$ and $Q=O_q(p^2)$. The largest index therefore has $b=O_q(\log p)$ bits. Taking unbounded auxiliary primes in this residue class gives ranks $p=2^{\Omega_q(b)}$ along a sequence of input bounds. At the bit cut after the low $\log_2 Q$ bits, any exact representation of the form $\sum_{i=1}^w L_i(r)R_i(h)$ over $\mathbb F_q$ has $w\ge p$. This includes a product of fixed digit-transition matrices of width $w$ on that cut. If a machine insists on equal canonical lengths, retain a largest set of columns of one high-part length and the matching rows, losing at most a factor $O(b)$. [Xylouris on Linnik's theorem](https://doi.org/10.4064/aa150-1-4)

The rank concerns the all-index scalar and explicit linear interfaces. A program can store a low word in $O(b)$ bits and perform nonlinear arithmetic on both halves. Moreover, a scalar routine needed only after a roughness sieve has a different input promise. This argument supplies no time lower bound for those programs or for factoring.

**Exact finite checks.** PARI/GP independently computed each divisor sum and the rank in the finite field. The entries of the table below are the auxiliary prime, digit split, maximum bit length in the matrix, and rank.

| $q$ | $j$ | $p$ | $Q$ | Maximum bits | Rank |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 7 | 1 | 13 | 4096 | 30 | 13 |
| 7 | 5 | 41 | 32768 | 39 | 41 |
| 7 | 1 | 83 | 131072 | 44 | 83 |

Use the [GP checks](swarm-round-2.gp) from this directory.

~~~sh
gp -fq swarm-round-2.gp <<'GP'
print(coefficientCut(13,7,1))
print(coefficientCut(41,7,5))
print(coefficientCut(83,7,1))
GP
~~~

## Multiplication messages after enforcing partial product bits

The earlier raw-width bound counted inconsistent settings. Here both operands can be positive balanced primes, and only messages produced by actual multiplications are counted. Let $A=2^{s+1}$, $h=A/2$, $L=Ah$, digit base $B=2^L$ and transform modulus $M=2^{4L}+1$. For digit polynomials $P,Q$ write $C(X)=P(X)Q(X)=\sum c_iX^i$. If $C(B)<2^b\le B^L$, then $c_i=0$ for $i\ge L$ by nonnegativity. Every coefficient fits below $M$. Expansion of the source forward and partial inverse transforms gives
$$
z_{k,j}=A\sum_{t<h} c_{j+At}(\eta^k)^t\bmod M,\qquad \eta=16^A\bmod M .
$$
These are the messages sent from middle row $k$ into inverse column $j$. For every prime $\pi\mid M$, $\eta^{A/2}=16^L=-1\bmod\pi$, hence $\eta$ has order $A$ modulo $\pi$. Distinct evaluation points have unit differences modulo $M$. Any $h$ rows therefore recover every column's coefficients by Vandermonde interpolation, including for composite $M$. [Pinned transform](https://github.com/IsaacRudich/SubexponentialDeterministicFactoring/blob/c91cc3f4947caca8977e81a5d14244f73b5ae2b1/FactoringAux/Transform.lean) · [Pinned gates](https://github.com/IsaacRudich/SubexponentialDeterministicFactoring/blob/c91cc3f4947caca8977e81a5d14244f73b5ae2b1/FactoringAux/MulNet.lean)

For a family $\mathcal C$ of distinct reachable product polynomials, its exact two-half consistency matrix is a permutation matrix after empty rows and columns are deleted. More generally, let $W$ be the total fixed crossing-message width after lossless encoding and $E$ the log of the maximum number of reachable local settings explicitly enumerated at a group. If no group holds more than $h$ middle gates, at least $h$ samples enter each inverse column from outside its group. Otherwise there is one majority group. Each inverse column outside that group receives at least $h$ samples from it, and its local settings determine the columns inside it. Hence $E+W\ge\log_2|\mathcal C|$ under this interface. The pinned common-width pad charge then gives an exponent at least $2\log_2|\mathcal C|/(r+2)$, $r=\Theta(\sqrt{\log b})$. The agent checked the transform identity and interpolation for all 2, 6, and 70 choices of half the rows at $A=2,4,8$.

For any fixed mask prescribing $b-g$ product bits, some bit pattern leaves $\Omega(2^g/b^2)$ distinct balanced prime products. Take pairs of different primes in $[3\cdot2^{b/2}/4,7\cdot2^{b/2}/8]$ and apply the prime number theorem and pigeonhole principle. Their products are distinct $b$-bit integers. Thus to obtain score $0.6$ with this explicit interface, the worst-case remaining freedom must satisfy $g=O(b/(\log b)^{0.1})$. This statement concerns applying a partial product mask before enumeration. Once the full target is enforced, a fixed semiprime has only one ordered prime pair with the smaller operand first. The argument places no lower bound on how cheaply that full constraint can be exploited. [Pinned evaluator pad](https://github.com/1337isnot1337/integer-factoring/blob/e91442d3162cae7f775e008efb2ea998c4478344/formal/HalfPad.lean)


## Carry-free predicates on the full target

Take the reference network's digit base $B=2^\ell$, $\ell=\Theta(\sqrt b)$. For $m_d=B^d-1$, the digits of a candidate operand can be evaluated by repeated modular multiply-add. Check the product modulo every $m_d$ while sharing both operands' original digits. If $K_D=\operatorname{lcm}_{d\le D}m_d>2^{2b}$ and both operands are below $2^b$, these congruences exactly enforce the target. The strong-divisibility identity gives $K_D=\prod_{j\le D}\Phi_j(B)$ and $\log_2 K_D=\Theta(\ell D^2)$, by summing Euler's totient. It suffices to take $D=O(b^{1/4})$. Local residues then have $O(b^{3/4})$ bits, so even spelling out every local digit or modular product relation fits $\operatorname{poly}(b)2^{O(b^{3/4})}$. The missing step is evaluating these relations jointly with shared bounded operands. An unrestricted residue join has at least $\varphi(K_D)\ge\sqrt{K_D}>2^b$ pairs, one for each unit $u$ via $(u,Nu^{-1})$. [Strong-divisibility identity](https://arxiv.org/pdf/1907.06700) · [Reference construction](https://github.com/1337isnot1337/integer-factoring/blob/main/research/half-top-constructor.md)

An alias persists even with the *full* target and actual positive digit operands. In radix 256, $193545=765\cdot253=255\cdot759$. The two uncarried polynomials are $253(2X+253)$ and $255(2X+247)$, with difference $4(256-X)$. In the pinned transform modulo $256^4+1$ the 16 points are $16^k$. Since 16 has order 16 at every prime divisor of the modulus, the difference is a unit at all 15 points other than 256. Thus a full target equality does not force those coordinates to agree. The network agent also tested the CRT predicate against direct multiplication on 127,008 six-bit target/operand triples. [Reference transform](https://github.com/IsaacRudich/SubexponentialDeterministicFactoring/blob/c91cc3f4947caca8977e81a5d14244f73b5ae2b1/FactoringAux/Transform.lean)

## Multiplicative orders and a batched discrete-log collision search

Let $s=N-1$, $x=a^A\bmod N$, $\gcd(a,N)=1$. Test the entire rectangle $x^{us+d}-1$ for $1\le u\le U$, $|d|\le H<s$. A deterministic baby-step/giant-step algorithm returns a factor whenever **any individual probe gives a proper gcd**. It can also report a global order multiple when a probe vanishes modulo $N$. A global hit at one exponent can coexist with a proper gcd at another.

Write each exponent as $e_0+i\sigma+j\tau$, where $e_0=s-H$, the longer side has length $M$ and stride $\sigma$, and the shorter has length $n$ and stride $\tau$. Set $L=\lfloor\sqrt{M/n}\rfloor$, write $i=kL+r$ and form $y_k=x^{e_0+kL\sigma}$ and $z_{rj}=x^{-r\sigma-j\tau}$. Then $y_k-z_{rj}=z_{rj}(x^e-1)$, with unit multiplier. Handle the last short block separately. There are $O(T)$ evaluation points and roots, $T=\lceil\sqrt{U(2H+1)}\rceil$. Deduplicate roots and retain one exponent offset per residue. For $P(t)=\prod_z(t-z)$ evaluate $P,P'$ at all $y_k$ using monic product and remainder trees. If $y_k$ equals a root, record the global exponent and use $P'(y_k)$ to remove that exact match. Otherwise use $P(y_k)$. A proper gcd splits. A gcd of $N$ requires at most one scan of the distinct nonmatching roots, since some difference then has a proper gcd. With fast polynomial arithmetic and $\log U=O(b)$ the bit cost is $\widetilde O(b[T+b+\log(2A)])$. The GP reference uses the same algebra and charges no asymptotic guarantee to its library implementation. [Hittmeir’s polynomial collision search, Algorithm 3.2](https://publications.sba-research.org/publications/042021_Hittmeir_A%20time-space%20tradeoff%20for%20Lehman%27s%20deterministic%20integer%20factorization%20method.pdf)

If $\operatorname{ord}_p(x)<(U+1)(H+1)$ for a prime $p\mid N$, two of $(i s+j)\bmod\operatorname{ord}_p(x)$ coincide among $0\le i\le U$, $0\le j\le H$. When the order exceeds $H$ the two $i$ differ. For order at most $H$ one can choose $u=1$ and a suitable $d$ directly. Either way at least one probe has gcd exceeding 1. A global order multiple may be the only outcome. The parent GP implementation agrees with exhaustive individual gcds for 3,670 rectangles. A separate agent implementation checked 15,252 tuples including 749 full-product gcd recoveries.

A second experiment uses exponents $420|u(N-1)+w\lfloor\sqrt{kN}\rfloor+d|$ with $u=0,1$, $w=-1,0,1$, $k=1,2,4$, $|d|\le2$, omitting zero and trying bases 2 through 7. The 192 inputs have prime factors in $[1000,1100)$ and $[1500,1600)$. The two columns give direct proper gcds and total hits after trying repeated removal of each of 2, 3, 5, 7 from an exponent that gave a global hit.

| Allowed terms | Direct | Including prime removals |
| --- | ---: | ---: |
| $w=0$ | 64 | 66 |
| $uw=0$ | 105 | 106 |
| All | 139 | 140 |

**Limits of short exponent windows.** For comparable primes $p,q\asymp X$, consider $A|u(N-1)+v+w\lfloor\sqrt{kN}\rfloor+d|$ with a common $X^{o(1)}$-sized menu of coefficients of magnitude $X^{o(1)}$, $k\ge1$, and $|d|\le X^{2/3-\epsilon}$ for fixed $0<\epsilon<2/3$. The multiplier $A$ may depend on $N$ and have arbitrary size if its prime factors are at most $X^{2/3}$. A positive proportion of comparable semiprimes miss every nonzero direct exponent for every base $2\le a\le X^{o(1)}$. Use the positive proportion of primes with some $\ell\mid p-1$ exceeding $p^{0.677}$ in the Baker–Harman estimate. Use comparable intervals supporting that proportion, or sum across dyadic intervals to obtain an infinite sequence of such scales. Exclude primes at which one of the bases has order at most $C X^{1/3}$ for a fixed sufficiently large $C$. The product of all $a^j-1$ in this range has log size $X^{2/3+o(1)}$. At the remaining primes, $\ell$ divides every base order, since $(p-1)/\ell<C X^{1/3}$. [Large prime factors of shifted primes, Lemmas 19–20 and cited Baker–Harman result](https://math.dartmouth.edu/~carlp/PDF/par11.pdf)

For fixed $p$, reduction modulo $\ell$ uses $p\equiv1$. A local hit forces $F(q)=u(q-1)+v+w\sqrt{kpq}$ within $H+|w|$ of a multiple of $\ell$, $H=X^{2/3-\epsilon}$. The range meets $X^{1/3+o(1)}$ relevant multiples. If $w\ne0$, $|F''|\gg1/X$, so the interval with $|F'|<X^{-\epsilon/2}$ has length $O(X^{1-\epsilon/2})$. On the at most two remaining monotone pieces each window captures $O(1+(H+|w|)X^{\epsilon/2})$ integers. The total is $X^{1-\epsilon/2+o(1)}$. With $w=0,u\ne0$ the nonzero integral slope directly gives the bound. With $w=u=0$, every nonzero exponent before multiplying by $A$ is too small to be divisible by $\ell$. Summing over the menu and counting bad edges in both orientations leaves a positive proportion of pairs on the indicated scales. This proof concerns small bases and these particular exponent formulas. Finding a uniformly small residual order or a different way to exploit global relations is still open here.

## Lattice hints and modular sieves for factor sums

For $Y<p<5Y/4$, $3Y<q<4Y$, consider a factor-location algorithm which initially sees only $N\bmod M$ for fixed $M\le Y$. At each step it may test a set containing at most $H$ candidate values of a factor and receives binary success/failure. For each residue of $N$, the first $K$ guesses on the all-failure path are fixed. Each unit candidate $x$ can occur with only one residue class of its partner modulo $M$. Summing over $M$ residue classes gives $O(KH(M+Y))$ covered pairs, against $\gg Y^2/\log^2Y$ possible pairs. Thus full coverage needs $KH\gg Y/\log^2Y$, or the same lower bound divided by the number of allowed extra transcripts if extra side information is supplied. With $H\asymp\sqrt Y$ even subpolynomially many transcripts leave $N^{1/4-o(1)}$ guesses. One finite check with $M=256$ covered 48,799 of 251,954 prime pairs using eight residue-orbit guesses. This restriction on how the algorithm accesses $N$ is essential.

For algorithms using full $N$, a different limited result concerns explicitly covering modularly admissible sums $S=p+q$. Take $9/4\le q/p\le4$, so $13\sqrt N/6\le S\le5\sqrt N/2$. Sieve by requiring $S^2-4N$ to be square modulo a wheel coprime to $N$. Write $R$ for the product of its distinct primes $\ge5$. At each such $\ell$, retain only residues with nonzero square discriminant. Their density is at least $(\ell-3)/(2\ell)$, and every such residue lifts to all prime powers. A nonzero additive Fourier coefficient of the indicator (unnormalized) is bounded by $\sqrt\ell+1$ via the Kloosterman bound on $x+N/x$. Multiplying Fourier coefficients by CRT and completing the interval gives discrepancy $O(2^{\omega(R)}\tau(R)\sqrt R\log(2R))$: group frequencies by their gcd with $R$ and use the geometric-sum bound. At 2 and 3 one may restrict $S$ to a compatible fixed progression of step $2^7 3^3$ where the discriminant is a local square (choose $S=x+N/x$ locally with controlled valuation of $x-N/x$). Thus for $R\le N^{1-\epsilon}$ at least $N^{1/2-o(1)}$ sums survive. Mapping $S$ to $\lfloor(S+\sqrt{S^2-4N})/2\rfloor$ is injective on this interval. Any *explicit interval cover of all these candidates* by hints of width $N^{1/4+o(1)}$ therefore needs $N^{1/4-o(1)}$ hints. An algorithm selecting hints by another arithmetic property is outside this count. [Hittmeir on modular hyperbolas](https://arxiv.org/pdf/2205.10074) · [Cohn–Heninger on Coppersmith's theorem](https://arxiv.org/pdf/1008.1284)

At $N=3000026000051$, the lattice agent counted 577352, 6228, 508 and 142 surviving sums using respectively no wheel, primes through 13, powers $64,27,25,49,121,169$, and those powers together with 17 and 19. The respective minimum numbers of contiguous hints at the tested width were 329, 316, 203 and 102. Subdividing a surviving interval gave center 3000068, radius 82, with the factor 3000017 at offset $-51$. These counts and the six-bit network sweep are auxiliary agent experiments. The self-contained GP commands below cover the core results.

## Reproduce the checks

~~~sh
gp -fq swarm-round-2.gp <<'GP'
print(checkEqualOrders())
print(checkTwists())
print(checkAdaptiveTwists())
print(checkRectangles())
print(checkProgressions())
print(checkTransforms())
print(coefficientCut(13,7,1))
print(coefficientCut(41,7,5))
print(coefficientCut(83,7,1))
GP
~~~

The order-rectangle check returns 3670, the transform check returns $[2,6,70]$, and the other expected outputs appear in their sections. The analytic arguments in this report are paper proofs. The two existing Lean files cover their earlier finite-cover and network cost statements.

## Open computations

1. Enforce the shared bounded operand digits *during* the CRT join. The local CRT tables already fit below the target cost. An advance needs a contraction with a bound on the number of entries actually produced, including intermediate joins.
2. To extend the order rectangle, give a deterministic construction of a small residual order on all inputs, or extract a factor from the global-relation-only outcome with a bounded number of additional probes.
3. For the divisor-moment approach, compute the scalar on rough indices or use a nonlinear representation with a cost analysis. The digit-rank theorem addresses only the explicit all-index linear representation.
