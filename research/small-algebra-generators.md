# Small generators and the exact test for a supplied order

Let $K$ be a fixed number field of degree $k$, with a fixed integral basis containing 1. Fix $B>2k$ and put $Y=(\log X)^B$. There is a constant $C_K$ such that the nonzero algebraic integers with all basis coordinates of absolute value at most $C_KY^{1/k}$ generate the **entire unit group** of $\mathcal O_K/t\mathcal O_K$ at all but
$$
                       X^{2k/B+o(1)}
$$
rational primes $t\in[X,2X]$. This includes every splitting type. In fact every residue unit at a good prime is a product of distinct members of this box, with at most $(4k+o(1))\log X/\log Y$ factors. The box has $O_K(Y)$ entries. For any fixed $\epsilon>0$ its height can be chosen polylogarithmic with at most $X^\epsilon$ exceptional primes.

### A product set in a lattice box

For each of the $\gg_K Y/\log Y$ primes $\ell\in[Y/2,Y]$ splitting completely in the normal closure of $K$, choose one ideal $\mathfrak l$ above it. Its index in the integral lattice is $\ell$. Minkowski on the lattice of its embeddings gives a nonzero $\alpha_\ell\in\mathfrak l$ with every archimedean absolute value at most $C\ell^{1/k}$. Its basis coordinates satisfy the claimed bound after changing the constant. The absolute norm is $m_\ell\ell$ with $1\le m_\ell\le C^k$. For $Y/2>C^k$ each marker prime divides only its own generator norm and has valuation one there. The generators themselves need never be found by the algorithm. [Chebotarev density theorem](https://websites.math.leidenuniv.nl/algebra/Lenstra-Chebotarev.pdf)

Partition the markers into two sets of comparable size. Within either set take all products of $r$ distinct generators. Choose the largest $r$ with $C'(CY^{1/k})^r\le X^2$, where $C'$ converts the maximum archimedean norm to the maximum absolute basis coordinate. All product vectors lie in $[-X^2,X^2]^k$. Their norms distinguish their subsets. For either product set $S$,
$$
 r=(2k+o(1))\frac{\log X}{\log Y},\qquad
 |S|\ge X^{2k(1-1/B)+o(1)}.
$$
Indeed $\log\binom mr\ge r\log(m/r)$ for $m\gg_K Y/\log Y$. All products are units at every prime in $[X,2X]$, since their norm prime factors are at most $Y$. The same holds for all the nonzero entries of the original box, whose norms are $O_K(Y)$.

### An additive large sieve

Write $A(z)=\sum_{a\in S}\exp(2\pi i\,a\cdot z)$. The nonzero vectors $v/t$ in the $k$-torus for primes $t\in[X,2X]$, $v\in(\mathbb Z/t)^k$, are mutually separated in maximum norm by at least $1/(4X^2)$. The multidimensional additive large sieve yields
$$
 \sum_t\sum_{v\ne0}|A(v/t)|^2\ll_K X^{2k}|S|.
$$
For a direct proof, dualize the sampling matrix and majorize the indicator of the lattice box by a constant times $\exp(-\pi\|a\|^2/L^2)$, $L=4X^2$. Poisson summation gives a dual Gram kernel $L^k\sum_{m\in\mathbb Z^k}\exp(-\pi L^2\|z+m\|^2)$. Its absolute row sums are $O_k(L^k)$ by packing the separated lifted points in successive shells of width $1/L$. The row-sum bound is also an operator-norm bound. [Huxley, multidimensional large sieve](https://doi.org/10.1112/S0025579300002540)

If $S$ occupies at most half of the $t^k$ residue vectors, Cauchy–Schwarz applied to their multiplicities and additive Parseval give $\sum_{v\ne0}|A(v/t)|^2\ge |S|^2$. Thus at most $O_K(X^{2k}/|S|)$ primes have this property in either pool. At every other prime the images of both product sets occupy more than half the entire ring, hence more than half the unit group. For each target unit $z$, one set meets $z$ times the inverse of the other. Multiplying the two representatives gives $z$ with no repeated marker. This argument also applies to noncyclic unit groups and uses no estimate for individual multiplicative characters.

Pappalardi used the additive large sieve on smooth rational integers in proper multiplicative subgroups modulo primes. The argument here uses a fixed number-field lattice and works for the entire residue algebra. Klurman, Shparlinski and Teräväinen obtain subset-product generation with a smaller prescribed set of rational primes for almost all integer moduli. [Pappalardi, Lemma 2](https://papparnta.github.io/pappa/papers/BULLCMS_38_1995.pdf#page=2) · [Klurman–Shparlinski–Teräväinen](https://arxiv.org/abs/2609.25393)

### What the gcd computes for every supplied exponent

Now let $k$ be an odd prime, let $p,q\in[X,2X]$ be distinct primes, and put $N=pq$. For one field compute every box element to the **odd part** $D$ of the supplied exponent $M$ in $\mathcal O_K/N\mathcal O_K$. Take one gcd of $N$ and all coordinates other than the scalar coordinate of all these powers. For all pairs outside a fraction $X^{-1+2k/B+o(1)}$, this gcd equals
$$
 \prod_{t\in\{p,q\}\, :\,t\text{ inert in }K,\ \Phi_k(t)\mid M} t .
$$
The prediction holds on the same pairs for **all positive $M$ at once**, however large or dependent on the pair. A fixed finite collection of fields obeys the same bound by a union bound. One field costs $O_K((\log X)^B)$ modular powers with fixed-dimensional arithmetic; the bit cost depends polynomially on $\log M$ and $\log N$. Replacing $\log X$ by $\log N$ only enlarges the tested box by a constant factor.

Remove the finitely many ramified primes. At an inert prime the quotient of the unit group by scalar units is cyclic of odd order $\Phi_k(t)$. Hence all box powers are scalar exactly when $\Phi_k(t)\mid D$, equivalently $\Phi_k(t)\mid M$. At a reducible unramified prime of residue degrees $d_1,\ldots,d_j$, $j\ge2$, the quotient has order $\prod_i(t^{d_i}-1)/(t-1)$, which is even. Some group element has even projective order, so an odd power cannot annihilate the whole group. Full generation ensures some tested power is nonscalar.

For $M=a\Phi_k(p)$ this decides which of two regimes applies mathematically. When $\Phi_k(q)\nmid M$, the gcd is $p$ precisely in the fields inert at $p$ and is 1 otherwise. When $\Phi_k(q)\mid M$, it is the product of the inert primes in that field. The algorithm does not need the hidden divisibility bit. The cross-prime gcd bound below implies the first regime on almost all pairs simultaneously for $a\le X^{k-1-\delta}$, any fixed $\delta>0$. Indeed $\Phi_k(q)\mid a\Phi_k(p)$ would force $\gcd(\Phi_k(p),\Phi_k(q))\gg X^\delta$, an event of power-saving probability. At the exponent $k-1$ a positive fraction of pairs can already reach the second regime. Fix a prime $\ell>2^{k+1}$ equal to one modulo $k$ and unramified in the normal closure of $K$. Require $p,q$ inert and each to have order $k$ modulo $\ell$. The prime-conductor cyclotomic field intersects the closure trivially, so these conditions have positive joint density by Chebotarev. The choice $a=\Phi_k(q)/\gcd(\Phi_k(q),\Phi_k(p))\le X^{k-1}$ covers both. [Cross-prime gcd estimate](prime-index-miss-density.md#uniformity-in-the-extra-multiplier-and-the-box)

These conclusions describe the actual field batched gcd. The box consists of elements in a fixed field, and a field test uses multiple modular powers. The results assume the supplied exponent. Computing a useful such exponent from an unrestricted integer remains open.

Choosing the fields from cubic characters of the public integer gives a sharp worst-multiplier mean of two field tests in the cyclic-character model. [Public branching algorithm and cutoff](public-cubic-characters.md)

### Finite group checks

Exact prime-quotient rank tests counted the primes where the radius-one and radius-two power-basis boxes generated the whole unit group. Each row uses all 2,692 primes from 1,009 through 26,000. The last column includes the scalar units before testing generation.

| Field | Radius one | Radius two | Radius two modulo scalars |
|---|---:|---:|---:|
| Cyclic cubic, conductor 7 | 2,105 | 2,689 | 2,692 |
| $S_3$, $X^3-X-1$ | 1,704 | 2,683 | 2,683 |
| Cyclic quintic, conductor 11 | 2,692 | 2,692 | 2,692 |
| $S_5$, $X^5-X-1$ | 2,692 | 2,692 | 2,692 |

All nine remaining $S_3$ cases were reducible. In each one a local unit had nonscalar maximal odd power, including in its minimal-polynomial quotient. Thus all 10,768 field/prime cases satisfied the exact scalar rule at radius two. Two balanced inert pairs in degrees three and five gave literal gcds $p,N,N,p$ at the successive exponents $\Phi_k(p)$, the two-order lcm, twice that lcm, and the previous smaller multiple obtained by subtracting $\Phi_k(p)$ from the lcm. [Full unit groups and literal gcds](../experiments/small-algebra-generators.gp)

An independent check built eight norm markers in each of three integral bases, including $\mathbb Q(\sqrt{-5})$ of class number two. All 56 triple products per field were distinct. Direct Hermite normal forms of the residue logarithms gave full generation at 101 of 102 field/prime pairs, covering every splitting type in degrees two, three and four. Squaring every generator produced a proper subgroup in all cases. [Integral-basis marker replay](../experiments/smooth-norm-markers.gp)

### Pointwise generation by linear shifts

Let $t$ be a rational prime, $f$ any monic degree-$k$ polynomial over $\mathbb F_t$, and $z=X\bmod f$. If $B>k\sqrt t+k$ and $2B-1\le t$, the units among the shifts $z-c$ for $|c|<B$ generate the full unit group of $\mathbb F_t[X]/f$. Repeated factors of $f$ are allowed. For fixed $k$ this gives a deterministic square-root-length list at every sufficiently large prime. The earlier polylogarithmic boxes have a different guarantee, quantified by an exceptional prime count. Complete-line character sums and generating sets in finite algebras have been studied previously. [Katz](https://web.math.princeton.edu/~nmk/old/estcharsums.pdf) · [Generating sets for multiplicative groups of finite algebras](https://doi.org/10.1016/j.jsc.2017.07.008)

Extend any nonprincipal unit character $\chi$ by zero. For every $h\in\mathbb F_t$ the mixed sum satisfies
$$
 \left|\sum_{c\bmod t}\chi(z-c)e(hc/t)\right|\le k\sqrt t.
$$
Indeed on monic polynomials $P$ use the Hayes character $\chi(P\bmod f)e(-h b_1(P)/t)$, where $b_1$ is the next-to-leading coefficient. In degree $k+1$, $f(X)(X+a)+R(X)$ realizes arbitrary $b_1$ and any remainder $R$ of degree below $k$ independently. Thus the character is nonprincipal. Equation (2.9) of Gorodetsky–Sawin at degree one, with one leading coefficient and finite modulus $f$, gives the bound. [Gorodetsky–Sawin, §2.1.5](https://arxiv.org/pdf/1811.04834#page=9)

Give residue $c$ weight $w(c)=B^{-1}\#\{0\le u,v<B:u-v=c\bmod t\}$. Its mass is $B$, its maximum is one, and its normalized Fourier coefficients are nonnegative and sum to $w(0)=1$. The weighted character sum therefore has absolute value at most $k\sqrt t$. If the unit shifts generated a proper subgroup, a nonprincipal character trivial on it would give weighted sum at least $B-k$, since $f$ has at most $k$ roots. This contradiction proves the claim.

**One list for all moduli and polynomials.** For large $X$ choose $B=\lceil20k\sqrt{2X}\rceil$. Draw $c=u-v$ for independent uniform $u,v\in[0,B)$. For every $t\in[X,2X]$, monic degree-$k$ polynomial and prime-order character of order $s$, the probability of a nonunit or a unit in its kernel is at most
$$
 \frac1s+\frac{k\sqrt t+k}{B}<0.6 .
$$
This follows by averaging the powers of the character over the units, using the weighted bound on each nonprincipal power and charging at most $k/B$ for nonunits. A proper subgroup lies in a prime-index subgroup. There are $O_k(X^{2k+1})$ triples of prime, polynomial and character. Thus $O_k(\log X+\log(1/\eta))$ independent draws give a single list working simultaneously for every such algebra with probability at least $1-\eta$, $0<\eta<1$. This gives existence of short universal lists. Efficient deterministic construction of lists of this length remains open here.

For $k\ge2$ the logarithmic order of the universal length is necessary. At a single odd prime $t$, reduce a proposed list $C$ of $m$ shifts modulo $t$. If $t-m>2^m$, two residues $a\ne b$ outside the list have identical Legendre signs on $a-c$ and $b-c$ for all $c\in C$. Take a monic $f$ divisible by $(X-a)(X-b)$ and extend it to degree $k$. The ratio of the two quadratic evaluation characters is nonprincipal on the unit group and trivial on every unit in the list. It is also trivial on scalars, so the lower bound holds for projective generation. An explicit universal list with polynomial construction time in $\log X$ would in particular yield deterministic polynomial-time quadratic nonresidue finding, by applying it at $f=X$ in degree one or to a split algebra in higher degree and testing the two evaluations.

**Cubic application.** Let $n=pq$ with prime ratio at most two, and let a public monic cubic be irreducible at the covered prime $p$ and squarefree at $q$. Put $D=M/2^{v_2(M)}$ for a supplied multiple of $p^2+p+1$. At $p$ every shifted unit raised to $D$ is scalar. At reducible $q$ the projective unit group has even order and an odd power leaves some unit nonscalar. At inert $q$ its cyclic order is $q^2+q+1$, so such a unit exists exactly when that order does not divide $M$. A norm gcd handles nonunits. Taking $B=O(n^{1/4})$ using $q\le\sqrt{2n}$ now gives a pointwise deterministic split in these cases. For fixed eligible $p,q,f$ the random difference above gives a split with probability at least $0.4$ per draw for sufficiently large $n$, by using a prime-order character trivial on the scalar-power kernel. If both primes are inert and both orders divide $D$, the scalar test on units always returns the whole modulus.

The finite replay checks 15 squarefree residue algebras and three algebras with a repeated linear factor. For $(X-1)^2(X+1)$ a unit has coordinates in $\mathbb F_t^\times\times\mathbb F_t^\times\times\mathbb F_t$ given by its two evaluations and its logarithmic derivative at 1. Discrete logs and the Hermite normal form certify full index one. The replay also checks four literal cubic splits, a common-order obstruction and a small-characteristic exception. [Finite shifts and gcd replay](../experiments/finite-shift-generators.gp)
