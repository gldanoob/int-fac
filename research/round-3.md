# Third parallel search

The preceding [research round](round-2.md) identified the joint multiplication constraint, coefficient evaluation and class-group probe selection as open computations. This round tests those steps. The stronger whole-input deterministic factoring bound remains open. [Upstream factoring project](https://github.com/1337isnot1337/integer-factoring)

## Explicit CRT joins remain large inside balanced operand boxes

Let $N=pq$ be a balanced $b$-bit semiprime. In the radix construction of [round two](round-2.md#carry-free-predicates-on-the-full-target) each leaf modulus $B^d-1$ has $O(b^{3/4})$ bits, and their lcm exceeds $2^{2b}$. Let operand boxes $I,J$ contain $H=\Theta(\sqrt N)$ consecutive integers each. An explicit table at a node stores every distinct residue pair modulo its lcm $K$ supported by a pair in those boxes satisfying the node's congruences. For large balanced inputs every leaf modulus is smaller than either prime factor and $N$ is coprime to $K$.

When $K\le H$ both boxes represent every residue, giving exactly $\varphi(K)$ rows. When $H<K$ reduction of either box is injective. The modular-hyperbola rectangle estimate gives
$$
R(K)=\varphi(K)H^2/K^2+O_\epsilon(K^{1/2+\epsilon}).
$$
A wrapping interval splits into at most two pieces. The estimate is uniform for unit targets and permits composite $K$. [Rubinstein, Eq. 17 and Theorem 4.3](https://math.colgate.edu/~integers/n12/n12.pdf#page=10)

In **every binary join order**, take a lowest node crossing $H^{2/3-\eta}$ for any fixed $0<\eta<1/6$. Its lcm is at most $H^{4/3-2\eta}$, by the child bounds. Below $H$, the exact count is at least $H^{2/3-\eta-o(1)}$. Above $H$, the main term is at least $H^{2/3+2\eta-o(1)}$ and the error is at most $H^{2/3-\eta+o(1)}$ (choose the error exponent sufficiently small). Taking arbitrarily small fixed $\eta$ proves an intermediate table of at least $2^{b/3-o(b)}$ rows. For sequential joins, the last node below $H$ has $K>H/\max_d(B^d-1)$ and already has $2^{b/2-o(b)}$ rows. These bounds apply after deduplication and box filtering. A symbolic operation or a join using constraints from outside its subtree is outside the model.

One can even require the candidate operands to be prime for a typical-target version. Use $H=2^h$, boxes $[4H,5H)$ and $[5H,6H)$, and $P\asymp H^2/\log^2 H$ distinct prime products of equal bit length. For a fixed subset lcm $K$, fewer than $P/L$ targets are in residue classes with fewer than $P/(KL)$ prime pairs, where $L=2^D b^2$ and $D=O(b^{1/4})$ counts leaf moduli. A union bound makes all subset counts simultaneous for a $1-O(b^{-2})$ fraction of targets. Each residue pair has at most $\lceil H/K\rceil^2$ lifts. At a lowest node crossing $H^{2/3}$, use $H^{2/3}<K\le H^{4/3}$ to obtain $2^{b/3-o(b)}$ prime-supported rows.

For $N=541\cdot701$, $B=4$, $I=[512,640)$ and $J=[640,768)$, the successive lcms are 3, 15, 315, 5355 and 1826055. Counts of distinct rows are 2, 8, 22, 2 and 1. At the fourth prefix the extra pair is $(607,713)$. The [GP check](../experiments/round-3.gp) enumerates the integer boxes and deduplicates the residues.

## Two ordinary divisor sums suffice on squarefree triprimes

Suppose $N=pqr$ for three distinct primes. Write $e_1=p+q+r$, $e_2=pq+qr+rp$, $S=\sigma(N)-1-N=e_1+e_2$ and $C=1+e_1-N$. Let $\zeta$ be a primitive cube root of unity. The polynomial $f(X)=X^3-e_1X^2+e_2X-N$ gives $f(\zeta)=C+S\zeta$. Hence
$$
\sigma(N^2)=\prod_{s\in\{p,q,r\}}(1+s+s^2)=C^2-CS+S^2.
$$
Since $C<0<S$, $C=(S-\sqrt{4\sigma(N^2)-3S^2})/2$. Recover $e_1=N-1+C$ and $e_2=S-e_1$, then recover all three primes by factoring the cubic over the rationals in deterministic polynomial bit time. The needed ordinary divisor sums are at inputs of $b$ and at most $2b$ bits. This transfer preserves each fixed logarithmic-saving exponent on the promised family. Computing either divisor sum from its unfactored input is still the expensive step.

There is a second version using $\sigma_1(N)$ and $\sigma_3(N)$ at the original index. Put $T=N+1$ and $R=\sigma_3(N)/\sigma_1(N)$. Evaluation at a primitive sixth root gives
$$4R-4T^2+4TS-S^2=3(e_2-e_1)^2.$$
Here $e_2>e_1$ fixes the square-root sign. Both formulas passed all 560 triples of distinct primes at most 53. The test passes known sums to the decoder. These norm identities are related to cyclic-resultant reconstruction. Bach, Miller and Shallit also give a randomized reduction from general factoring to sums of divisors. [Hillar and Levine](https://arxiv.org/abs/math/0411414) · [Bach, Miller and Shallit](https://doi.org/10.1137/0215083)

More generally let $N=\prod p_i^{e_i}$, $d_i=p_i^{e_i}$. Expanding $\sigma(N^k)=\prod_i (p_i d_i^k-1)/(p_i-1)$ gives a signed exponential sum on the $2^{\omega(N)}$ distinct subset products of the $d_i$, each with a nonzero rational coefficient. Given an upper bound $t$ on $\omega(N)$, samples for $0\le k<2^{t+1}$ determine those nodes by exact linear recurrence recovery. At the actual order the Hankel matrix is invertible by Vandermonde factorization. The minimal nonidentity nodes under divisibility are exactly the individual prime-power blocks. This is a fixed-weight reduction for bounded $\omega(N)$, with input length increasing by a factor exponential in $t$.

A related rounding formula gives $\varphi(N)$ from a single ordinary divisor sum at a larger input. If the least prime exceeds $Y\ge2$, choose $k$ with $bY^{-k}<1/(4N)$. The product $\prod_{p^e\parallel N}(1-p^{-ek-1})$ lies between $1-bY^{-k}$ and 1. Consequently $N^{k+1}/\sigma(N^k)$ rounds to $\varphi(N)$, by Euler's product. Trial division to $Y=2^{b/(\log b)^\beta}$ allows $k=O((\log b)^\beta)$. Alpöge’s verified Dirichlet GRH supplies the hypothesis for Miller’s deterministic reduction, and the one exact totient at this input suffices throughout factor recovery. For a fixed-weight engine of score $\alpha$, balancing this particular trial division and the larger query gives at most the guaranteed score $\alpha/2$ from the displayed costs. No fast coefficient engine follows from this rounding observation. [Miller](https://www.cs.cmu.edu/~glmiller/Publications/Papers/Mi76.pdf)

Miller's single-value recovery step also works using the more recent $31/32$ strip and a larger polynomial witness search. The [source index](known-results.md#totients-and-multiplicative-orders) identifies the two lemmas and the least-nonresidue bound. The score calculation above still charges the cost of supplying $\varphi(N)$. A separate unconditional reduction applies when the totient procedure can answer successive inputs. Źrałek’s Corollary 8.2 completely factors $N$ from its chain of numeric totient iterates down to 1 in $L_N[1/3,1]$ deterministic time beyond the queries. The cost of supplying each iterate must be charged. Morain–Renault–Smith §6.3 also gives an earlier cubic reconstruction for every squarefree triprime given the two exact values $\varphi(N)$ and $\sigma(N)$. [Totient reduction](https://arxiv.org/pdf/0707.4102#page=18) · [Triprime result](https://arxiv.org/pdf/1802.08444#page=20)

## Class-number windows from proved Dirichlet GRH

For $D<-4$, put $d=|D|$ and let $h$ be the quadratic-order class number. The class-number formula and a smoothed prime Euler sum through $2Q$ give a center $H$ with $\log(h/H)=O((\log d)/(\sqrt Q\log Q))$ by the verified Dirichlet GRH for the relevant quadratic character; the finite conductor corrections are included for an imprimitive discriminant. Alpöge’s verified Dirichlet GRH applies to this character, including the imprimitive case. [Exact statements and verification](https://math.mit.edu/~drew/grh/)

The GP example implements the weighted prefixes for $Q\ge5000$ with logarithmic radius $(6.593\log d+19.321)/(\sqrt Q\log Q)+\log d/((Q-1)\log Q)$. The numerical check uses ordinary GP real arithmetic. A certified use would round the interval outwards. [Jacobson, §3.1](https://cspages.ucalgary.ca/~jacobs/PDF/mthesis.pdf) · [Schoof, §3](https://reneschoof.github.io/mcpaper.pdf)

At $Q=d^\alpha$, the absolute width is $W=O(d^{(1-\alpha)/2+o(1)})$. For a supplied seed $g$, search the interval for a group annihilator by baby-step/giant-step. Since $h$ lies inside, a hit exists. Strip its powers of two to obtain an odd multiple of the odd part of the seed order and apply the [deep-root construction](round-2.md#constructing-the-upstream-deep-root-from-a-shifted-order-interval). Enumeration and searching cost $d^{\max(\alpha,(1-\alpha)/4)+o(1)}$. The optimum $\alpha=1/5$ gives Schoof's classical $d^{1/5+o(1)}$ balance, too expensive for this benchmark. At $D=-56444$, $Q=5000$, the integer interval is $[131,176]$, the class number is 152, and the odd window at scale $1/8$ contains the annihilator 19. The resulting involution gives $103\cdot137$. An estimate for a supplied seed and a uniform algorithm for choosing useful seeds have distinct hypotheses.

## Why endpoint mixing alone does not derandomize Lenstra–Pomerance

For generators $g_1,\ldots,g_m$ of the class group $C$ write $\phi(r)=\prod_i g_i^{r_i}$, $L=\ker\phi$ and $K=L\cap 2\mathbb Z^m$. Lenstra–Pomerance use both the distribution of $\phi(r)$ and the conditional distribution of $r\bmod 2L$ given $r\bmod K$. The map $K/2L\to C[2]$, $v\mapsto\phi(v/2)$, is an isomorphism. Lemma 5.4 of the paper controls the probabilities of these lifts. A short GRH expander walk on endpoints alone does not supply this second property. [Lenstra–Pomerance, §5 and Theorem 10.3](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/rigorous.pdf) · [Jao–Miller–Venkatesan](https://arxiv.org/abs/0811.0647)

At $\Delta=-55$ the prime-2 form $g=(2,1,7)$ generates a cyclic group of order four. Uniform exponents $6,7,8,9$ visit every class. Every leading coefficient is 2-smooth. Yet the signed factor-base exponents $t$ are respectively $2,1,0,-1$, so $r+t=8$ in every row. Dividing any binary dependency by two gives the principal class. Replacing 6 with 10 preserves the class and parity and produces the row $(10,2)$, whose half exponent gives $g^6=(4,3,4)$ and the factors 5 and 11. This supplies a test for any proposed replacement of the original exponent box.

For signed steps in distinct split prime forms of norm at most $X$ in the factor base, let $a=\prod p^{|r_p|}$ after opposite steps cancel. If $4a^2<|\Delta|$, prime-form composition gives a primitive representative of leading coefficient $a$ and the prescribed local middle-coefficient signs. Center its middle coefficient in $(-a,a]$. The last coefficient is strictly larger than $a$, so it is already reduced and the factor-base row simply reads the vector back with opposite sign. In particular $X^\ell<\sqrt{|\Delta|}/2$ ensures that all such length-$\ell$ words yield tautological rows. At $a=2^k,\Delta=1-4a^2$, the words $f_2^{\pm k}$ instead meet at $(a,1,a)$; GP checks $1\le k\le12$. This measures individual prime steps. Binary powering represents different costs.

Independent random walks $U,V$ with pointwise endpoint probability in $[(1-\delta)/|C|,(1+\delta)/|C|]$ do recover the required lift control via $r=U+2V$. For fixed $U$ and a compatible coset of $K$, the possible $\phi(V)$ are the $|C[2]|$ roots of one square. Each has conditional probability at least $(1-\delta)/((1+\delta)|C[2]|)$. Averaging over $U$ preserves this bound. Enumerating a whole distribution with positive mass on every endpoint still requires $|C|$ endpoints. A uniform deterministic rule hitting useful lifts within the time budget remains open.

## Splitting from an unfactored global order multiple

For $N=pq$ with distinct odd primes, suppose $\gcd(a,N)=1$ and $a^M=1\bmod N$. Compute $c=\gcd(M,N-1)$, $R=M/c$, and $z=a^c\bmod N$. Write $s,t$ for the two local orders of $a$. Their gcd divides $c$, since it divides both $M$ and $N-1$. Thus $s/\gcd(s,c)$ and $t/\gcd(t,c)$, the two local orders of $z$, are coprime. Their product divides $R$. If $z\ne1$, these orders differ and the first $k>0$ with $\gcd(z^k-1,N)>1$ is at most $\lfloor\sqrt R\rfloor$ and gives a proper divisor.

The implementation binary-searches for the first positive prefix. In blocks of $s_0=\lfloor\sqrt h\rfloor$ terms, compare $z^{i s_0}$ with $z^{-j}$ for $1\le j\le s_0$. Product and monic remainder trees test all full blocks, and at most $s_0-1$ tail terms remain. A full product gcd is a positive answer to the prefix test even if it masks two separate prime hits. With fast polynomial arithmetic this gives $\widetilde O(R^{1/4})$ modular operations beyond setup, including the binary search. At $z=1$ the reduced exponent $c$ still annihilates the base, but this particular guarantee ends. [Hittmeir's polynomial collision searches](https://arxiv.org/abs/2006.16729)

For $N=1333$, $a=3$ and $M=210$, the residual order bounds come from $c=6$, $R=35$ and $z=729$. The fifth power exposes 31 and the seventh exposes 43. The [GP implementation](../experiments/round-3.gp) was checked against field orders on 11,828 tuples, splitting all 11,056 cases with $z\ne1$. On the previous 192-input schedule this extra mechanism did not increase the 140-input coverage.

There is also a limitation on explicitly constructing a cyclotomic separator. Suppose $M=uv$ for distinct primes, coprime to $N$, and the local orders are $u,v$. Every monic integral divisor of $X^M-1$ that separates the two roots includes exactly one of $\Phi_u,\Phi_v$. Strip $X-1$ if present and evaluate at 1. The value is the corresponding factor of $M$ since $\Phi_{uv}(1)=1$. Constructing such a separator can therefore already encode a factor of the supplied exponent. [Cyclotomic evaluation identities](https://arxiv.org/abs/1611.06783)

## Mixed relations can recover several deep roots at once

Let $Q=2^L\ge|G|$ in a finite abelian class group $G$, and set $h_i=g_i^Q$. Verify rows $r$ with $\prod_i h_i^{r_i}=1$, and let $\Lambda$ be their integer span. A positive multiple of a target word $a$ belongs to $\Lambda$ exactly when $a$ belongs to its rational span. At full column rank, the largest Smith invariant $d$ of the row lattice kills every $h_i$. Remove its power of two to obtain an odd annihilator $M$. The same $c=(Q^2)^{-1}\bmod M$ gives all roots $z_i=h_i^c$ and all exact two-primary projections $g_i/z_i^Q$. When $M=1$ take each $z_i=1$. The criterion concerns what the rows certify. [Upstream deep-root contract](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/deep-class-root-projection.md) · [Odd-quotient relations](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/odd-quotient-relations.md)

At $N=479348657$, $D=-4N$, use split-prime forms at 167 and 653. After six simultaneous squarings of $(h_1,h_2)$, the pair reaches $(h_2/h_1,(h_1h_2)^{-1})$. The relation matrix has rows $(65,-1),(1,65)$ and Smith invariants 1 and 4226. Both odd parts have order 2113, while the two mixed rows have already been acquired. The second projected form is $(2018,2018,238041)$ and its leading coefficient exposes the factor 1009. An individual search from 1 would first hit at the 1,057th odd exponent, with baby-step/giant-step available to batch that search. The comparison counts candidates, not elapsed work. The seed pair and target pattern are specific to this witness. Uniformly acquiring enough useful rows is the expensive open step.

## Blind multistride selection on the archived event cycles

Probe offset 0, then consider $k2^j$ for $j\ge0,k\ge1$ in order of increasing $k(j+1)(j+2)$, breaking ties by smaller $j$. Skip repeated integer offsets. This deterministic rule can run without the period or event list. If the first $m$ probes at stride $2^j$ hit from all starts, it hits within $1+(m-1)(j+1)(j+2)$ probes. The reciprocal weights telescope to one, so through priority $t$ at most $t$ pairs have appeared.

For an evaluation against a saved event set $E\subset\mathbb Z/h$ and a schedule prefix $S$, the successful starting points are exactly $E-S$. Exhausting all 198,850 starts gave worst counts of 20,322 and 5,090 on generators 5 and 7, with final witnesses at starts 90,458 and 83,315. The corresponding stride-1 counts were 17,940 and 4,509. These controls distinguish a stride that can be prescribed in advance from the optimized steps that used the entire archived orbit. [Event diagnostics and source data](round-2.md#deterministic-selectors-on-two-upstream-archived-cycles)

## Extracting all available square-root splits from two modular relations

For odd $N$ and units $a,b$, write $f(i,j)=a^i b^j\bmod N$. Suppose two independent relations $r,s$ are supplied and verified. For each of $r,s,r+s$ with even coordinates, evaluate $z=f(u/2)$. If $z\ne\pm1$, its square is one and $\gcd(z-1,N)$ splits. If $z=1$, adjoin $u/2$ as a new relation. Replace $r$ by $r/2$ or $(r+s)/2$, or $s$ by $s/2$, as appropriate. The lattice still contains the old one and its determinant halves. With initial absolute determinant $D$, at most $3(1+\lfloor\log_2 D\rfloor)$ power-product evaluations suffice after validation.

When no further halving is possible, the final lattice $R$ has odd index $k$ in $\ker f$. Otherwise an order-two element of $\ker f/R$ gives an untested halving, since $r,s,r+s$ represent all nonzero parity vectors relative to the basis. For any root $f(v)^2=1$, $2kv\in R$ and $f(kv)=f(v)$. Its value is among the finally tested halves or the identity. Thus a miss certifies that this particular subgroup has no nontrivial square-root split. The cost of finding the two original relations is external. [Related order-based algorithms of Źrałek](https://arxiv.org/abs/0707.4102)

For $N=65$, $a=8$, $b=18$, start with $(4,4),(4,-4)$. The first half $(2,2)$ is also a relation. Its half $(1,1)$ gives $14\bmod65$, exposing 13. Our implementation agreed with exhaustive subgroup enumeration for all 2,304 ordered pairs of units modulo 65, with 2,052 splits. The investigating agent also checked 45,558 small cases independently.

## Heterogeneous wire widths and explicit Hecke matrices

In the upstream cluster map, index $i$ of each of the four transform layers goes to the same group. If group $i$ has $m_i$ indices, $\sum m_i=A$, the three complete bipartite layers contribute exactly $6fm_i m_j$ raw bits to pair $i<j$ for raw wire width $f$. Their total is $3f(A^2-\sum m_i^2)$. The constructor has $m_i\le(2G/P)\lceil A/G\rceil\le4A/P$ since $G\le A$. Thus at $P\ge8$ the three layers alone cross at least $3fA^2/2\ge12b$ bits before padding. Even replacing the common maximum width by the sum of actual widths leaves an $\Omega(b/\sqrt{\log b})$ raw charge at the current evaluator discount. Locally, for crossing unequal wires of widths $u\ge v$, cross the low $v$ bits and tensor each piece with equality on the $u-v$ excess bits. This preserves the crossing identity and increases each of its two cut widths by at most $u-v$. The count leaves correlated encodings open. [Cluster map](https://github.com/IsaacRudich/SubexponentialDeterministicFactoring/blob/c91cc3f4947caca8977e81a5d14244f73b5ae2b1/FactoringAux/Cluster.lean) · [Upstream constructor](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/half-top-constructor.md) · [Crossing statement](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/AppRunningTimeStatement.lean)

For $q\nmid n$, an even weight $k\ge4$ with $k-1\equiv j\bmod(q-1)$ gives the scalar $\sigma_j(n)\bmod q$ as an ordinary level-one Eisenstein eigenvalue reduced modulo $q$. The universal Hecke operator on modular symbols is expensive to list. Merel's condition $C_n$ requires the boundary $[\infty]-[0]$ in each determinant-$n$ matrix class. Hermite normal form gives $\sigma_1(n)$ classes. A single supported matrix can supply both endpoints only with columns on the two coordinate axes, in one of $\tau(n)$ classes. Thus any such explicit sum needs at least $2\sigma_1(n)-\tau(n)$ supported matrices. At $n=55$ the lower bound is 140 across 72 classes; the agent enumerated 508 in Merel's formula. The scalar level-7 check gives 2 and 5 at the two embeddings for weights 8 and 6. This counting argument leaves direct evaluation of the single eigenvalue open. [Merel, Theorem 2 and §3.3](https://perso.imj-prg.fr/loic-merel/wp-content/uploads/merel-pub/Essen.pdf) · [Cohen on Eisenstein series](https://arxiv.org/abs/1809.10908)

## Two upstream field evaluations per level suffice for triprimes

Assume $N$ has exactly three prime factors counting multiplicity. At an auxiliary prime $q\equiv11\bmod12$ coprime to $N$, put $u=(q-1)/2$, fix $g$ generating the units modulo $q$ and fix a primitive $u$th root $\omega$ in one characteristic-two field. Write $\eta(d)=\omega^{\log_g d}$, $C=\eta(N)$ and $a=(u+1)/2$. Request the upstream normalized coefficient at $j=1,3$ and multiply by $C^{aj}$ to obtain $R_j=\sum_{d\mid N}\eta(d)^j$. Since $3$ is invertible modulo $q-1$, changing the supplied generator to $g^{3^{-1}\bmod(q-1)}$ implements the second query in the same field. Both queries use the original index. [Upstream field-query convention](https://github.com/1337isnot1337/integer-factoring/blob/main/research/sparse-faithful-character.md)

For distinct primes let $x,y,z$ be their character values, $E=x+y+z$, $H=xy+xz+yz$. At $R_1\ne0$, compute
$$S=R_1+1+C,\qquad P=(R_3+1+C^3+S^3+C+C^2)/R_1.$$
Expansion of $R_j=(1+x^j)(1+y^j)(1+z^j)$ gives $S=E+H$ and $P=EH$. The prime values occur among the roots of the two cubics for the possible assignments of $E,H$. With $D=X^3+SX+C$ and $J=X^2+X$, their product is $D^2+SJD+PJ^2$. For $N=p^2r$, $x=\eta(p)$ instead satisfies $x^4+x^3+(1+C+R_1)x^2+Cx+C=0$, by expanding $(1+x+x^2)(1+C/x^2)$. The repeated-prime formula only needs the first query; an integer cube test handles $p^3$.

Test the $u$ powers $\omega^i$ and map every root to $g^{2i}\bmod q$. The resulting lists of length at most six and four contain the relevant prime squares at this level. For unknown multiplicities run both predicates. Convert each list into a monic integer polynomial modulo $q$, padding its roots with zeros to the stated degree. Combine coefficients by CRT until the modulus $M>N^{24}$. Each required integer $p^2<N^2<M^{1/12}$ is a small root of a monic polynomial of degree at most six. Deterministic univariate Coppersmith recovery with fixed slack and exact square and division tests complete the reconstruction. Returned candidates must satisfy the promised factorization pattern. Bad levels divide $N\prod_{p\mid N}(p^2-1)<N^3$: at a good level an $R_1$ zero requires $\eta(p)=1$ for some prime factor, since $3\nmid u$. By Linnik applied to distinct reduced classes $11\bmod12$ with a supplementary prime modulus, $O(b)$ eligible polynomial-size primes suffice, including the losses. Field construction by factoring over $\mathbb F_2$, scanning the subgroup and CRT all take polynomial bit cost. The missing operation is obtaining the supplied coefficients efficiently from $N$. [Coppersmith's theorem](https://www.di.ens.fr/~fouque/ens-rennes/coppersmith.pdf) · [Linnik bound](https://doi.org/10.4064/aa150-1-4)

Boneh’s Theorem 5.1 gives this CRT construction for lists of residues. The [error-tolerant version](order-and-crt-reductions.md#chinese-remainder-decoding-with-missing-or-incorrect-levels) only needs the correct lists on a specified fraction of the total logarithmic weight.

A finite example shows that these two values need not encode the whole coefficient vector locally. At $q=2543$, let $p_i$ be the least prime at least $2^{64}$ congruent to $5^{41i}\bmod q$ and take the product at each listed index triple. Encode $\omega$ using $X^{20}+X^8+X^7+X+1$ over $\mathbb F_2$ and display field elements as binary polynomial masks. Each input has 193 bits.

| Indices | $N\bmod q$ | $A_1$ | $A_3$ | $A_5$ |
| --- | ---: | ---: | ---: | ---: |
| 1, 7, 12 | 752 | 538088 | 767197 | 510065 |
| 2, 3, 15 | 752 | 538088 | 163851 | 701923 |
| 1, 8, 21 | 1883 | 767196 | 818349 | 701923 |
| 3, 12, 15 | 1883 | 767196 | 818349 | 701922 |

The [field decoder](../experiments/triprime.gp) takes a coefficient callback. Its test fixture supplies genuine sums from known divisors. It verified all factors on eight inputs, including three distinct primes, a repeated prime and a prime cube. The distinct and repeated examples using only primes congruent to 1 modulo 12 avoid any opportunity to split at a queried level. For $858461=71\cdot107\cdot113$, it used 54 levels; for $569633=71^2\cdot113$, it used 53. At $q=11$ on the first example the sextic has four candidate residues, of which only two are actual prime squares at that level. No timing of this supplied-coefficient decoder measures the missing engine.

## Reproduction

From the repository root run the full suite with the command below. The Lean checks cover the two earlier statements; the new general arguments above are paper proofs.

~~~sh
make check
~~~

To inspect individual witnesses, load the third-round experiments in GP.

~~~sh
gp -fq experiments/round-3.gp <<'GP'
print(checkLPFibers())
print(checkMixedRoots())
print(checkBoxJoins())
print(checkClassInterval())
print(checkGlobalOrders())
print(checkRankTwo())
print(checkBlindStrides())
print(checkTriprimes())
print(checkFieldDecoder())
print(checkFieldWitnesses())
GP
~~~
