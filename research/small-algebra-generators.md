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
