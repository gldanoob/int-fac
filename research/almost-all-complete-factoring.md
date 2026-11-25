# Complete deterministic factorization of almost all integers

Put $B=\log x$. There is an integer-only deterministic algorithm which completely factors all but $O(xe^{-c m(B)})$ integers in $(x/2,x]$, with the following bit-operation bounds. Constants may depend on a fixed exponent or strip width.

| Input from the distribution of zeta zeros | Time | $m(B)$ |
| --- | --- | --- |
| Classical Vinogradov–Korobov region, fixed $a=5/6+\epsilon\in(5/6,1)$ | $\exp(O_a(B^a))$ | $B^{a(1-a)}\log B$ |
| Fixed $\delta>0$ with $\Re\rho\le 1-\delta$ for every nontrivial zeta zero | $\exp(O_\delta(\sqrt{B\log B}))$ | $B^{1/4}(\log B)^{3/4}$ |

The exponents in $m$ reflect trial division followed by the quantitative exception bound at the smallest prime still present. The fixed-strip statement is in particular a consequence of ordinary RH. Cureton–Thorner's reported Dedekind strip and Alpöge's recent ordinary RH statement each supply it. Repeating on dyads, or discarding $N\le\sqrt x$, gives the same asymptotic bound up to $x$ with a possible change of $c$. The algorithm may report failure on the exceptional inputs or use a deterministic fallback there. Its faster running time holds for the stated proportion of integers. [Smooth Hasse lemma and analytic inputs](odd-smooth-hasse.md) · [Alpöge and the independent checks](https://math.mit.edu/~drew/grh/)

## Quantitative complementary characters

For every $k\ge1$ there are $c_1,\ldots,c_k\ge2$ with $c_i\ll (i+1)^8$ such that the $2k$ positive rational squareclasses of $c_i,c_i-1$ are independent. Given the first $i-1$, their combined prime support has size $O(i\log(2i))$ by the height bound. Choose two unused odd primes $r_i,s_i\le C(i+1)^2$. The prime number theorem guarantees sufficient choices for an absolute $C$, by induction with the constants fixed sufficiently large (the support bound is $O(i\log(Ci))$). Impose $c_i\equiv r_i\pmod{r_i^2}$ and $c_i\equiv1+s_i\pmod{s_i^2}$ and take a positive representative at most $r_i^2s_i^2$. The two fresh odd valuations separate the two new classes. Taking the largest index present in a prospective relation proves independence.

Let $P\le Z$, with $p\in(P,2P]$, $q\in(Z,2Z]$, and set $k=\lfloor c_0\log P/\log\log P\rfloor$ for sufficiently small fixed $c_0>0$. All the characters $\chi_\ell(c_i),\chi_\ell(c_i-1)$, considered as functions of the variable prime $\ell$, are Dirichlet characters with a common modulus
$$Q=8\!\prod_{r\mid \prod_i c_i(c_i-1),\ r\text{ odd prime}}r\ \le\exp(O(k\log(2k)))\le P^{1/3}.$$
On the group of reduced residues modulo $Q$, their sign vector has uniform distribution on $\{\pm1\}^{2k}$ by independence of the associated quadratic characters. Every reduced class contains $O(P/(\varphi(Q)\log P))$ primes in the first dyad and $O(Z/(\varphi(Q)\log Z))$ in the second, by Brun–Titchmarsh. The fractions of pairs of residue classes missing each of the two desired witnesses are $(7/8)^k$. In fact each index has chance $1/8$ of satisfying $\chi_p(c_i)=\chi_p(c_i-1)=s$ and $\chi_q(c_i(c_i-1))=-1$ for a prescribed $s$. The counts of prime pairs that fail for either sign are therefore
$$\ll \frac{PZ}{\log P\log Z}\exp(-c_1\log P/\log\log P).$$
This only uses upper bounds for primes in individual residue classes. All the required constants $c_i$ are included by enumeration up to $(\log(2d))^9$ on any cofactor $d$ divisible by $pq$ when $P$ is large. [Montgomery–Vaughan, the Brun–Titchmarsh bound](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf)

## A seed for an arbitrary cofactor

In the notation of the [moving Legendre construction](legendre-average-factoring.md), take a good prime $p\in(P,2P]$, and put $V=V(P)$. Independently of $q$, its exceptional set of starting residues in $\mathbb P^1(\mathbb F_p)$ has size $O(pV^{-7})$. This is the union over all conic choices $c_+,c_-\ll(\log P)^8$ that have the correct characters at $p$. The '$O(b^2)$ choices' calculation there extends to any fixed power of $\log P$, since $V$ grows faster than every such power. The first $\lceil V^6\rceil$ distinct marks have height $P^{o(1)}$ and remain distinct modulo both primes. The word length used in this exceptional set is $O(\log V)$.

At a cofactor $d$, try the at most $1+\lfloor\log_2 d\rfloor$ public seeds
$$x_j=\lfloor d/2^j\rfloor,\qquad 0\le j\le\lfloor\log_2 d\rfloor.$$
Write $d=pqA$ with $p<q$. For fixed $p,A$ choose $j=\lfloor\log_2(pA)\rfloor$. Then $x_j=\lfloor vq\rfloor$ with $1\le v=pA/2^j<2$. As the integer $q$ ranges in $(Z,2Z]$ with $Z\ge P$, this map is injective and its range has length $O(Z)$. Each residue modulo $p$ occurs $O(1+Z/p)=O(Z/p)$ times. At most $O(ZV^{-7})$ integers $q$ in this interval produce a bad seed for the given $p,A$. This estimate is uniform in $A$ and includes the case that $q$ and $p$ lie in the same dyad. The machine visits the chosen seed without knowing $p,A$.

If a suitable parameter and mark give identity modulo $p$ and a finite point modulo $q$, the same gcd-checked group law splits $d$ even when $d$ has other prime or repeated divisors. In the absence of any preceding proper gcd, all arithmetic decisions simulate the two field laws simultaneously. A proper gcd is forced before incompatible identities are returned. In a successful branch at $p$, a zero denominator or singular parameter at $q$ already separates the factors. A globally zero denominator or globally singular model cannot occur in that branch because its reduction at $p$ is valid.

## Accounting for every divisor reached by the algorithm

Write $g(u)=u^a$ in the classical case and $g(u)=C_\delta\sqrt{u\log u}$ in the fixed-strip case. For an input $N$ begin with trial division by all primes up to $\exp(g(\log N))$, repeatedly removing each prime power. This fits the stated time. At every subsequent cofactor $d$, handle primes and perfect powers by deterministic primality testing and integer roots, and on other composites run the moving Legendre search at the scale $\sqrt d$ with the listed seeds and $2\le c\le (\log(2d))^9$. A prime-power cofactor can be completed by trying exponents up to its bit length and primality testing the exact roots. Every other composite has at least two distinct prime divisors. Repeat on both sides of every proper split. There are $O(\log N)$ calls at most, and each capped search costs $\exp(O(g(\log N)))$ bit operations. [Agrawal–Kayal–Saxena, deterministic primality testing](https://annals.math.princeton.edu/2004/160-2/p12)

For $N\in(x/2,x]$ every remaining prime exceeds $R=\exp(g(B)/2)$ for large $x$. Use dyads $(P,2P]$ with $R/2\le P\le x$ and analogous dyads $(Z,2Z]$. On this range
$$\log V(P)=16(\log P)\log\log P/g(\log P)\gg m(B).$$
Indeed the right side of the definition is eventually increasing, and substituting $\log P\asymp g(B)$ at the lower endpoint gives precisely the two displayed forms of $m$. Also $\log P/\log\log P\gg m(B)$ and $m(B)/\log B\to\infty$.

1. A bad Hasse prime $p$ has $O(PV(P)^{-11})$ possibilities per dyad, so the exceptional integers it divides are bounded by $x\sum_{p\ {\rm bad}}1/p\ll xB e^{-c m(B)}$.
2. The number of integers divisible by a pair of large primes missing a required character sign is at most $x\sum_{p,q\ {\rm bad}}1/(pq)$. The uniform prime-pair count bounds this by $O(xB^2e^{-c m(B)})$ across all dyad pairs.
3. For each $A,p$ and each $q$-dyad, the reciprocal sum over $q$ giving a bad public seed with $d=pqA$ is $O(V(P)^{-7})$. The number of inputs divisible by any offending $pqA$ is therefore at most
$$x\sum_{A\le x}\frac1A\sum_{R/2<p\le x}\frac1p\sum_{Z\ {\rm dyadic}} O(V(P)^{-7})\ \ll x B^3 e^{-c m(B)}.$$
Here $P$ is the dyad containing $p$, and replacing the prime reciprocal sum by the harmonic sum suffices. Allowing all positive integers $A$ covers every divisor of the original input that a recursive split might produce. Common factors among $A,p,q$ cause no issue.

The polynomial factors in $B$ are absorbed by reducing $c$. Outside this union, every remaining cofactor containing distinct primes $p<q$ has a successful seed and both required sets of conic signs. Since $\sqrt d\ge p$, its search includes the smoothness cutoff, word depth, and mark count used at the proof scale $P$. Every proper split can therefore be completed, independently of the order in which gcds expose divisors. This proves the quantitative complete-factorization statement.

The finite replay checked 315 scaled-seed fiber bounds over different $p,A,Z$ and completely factored 385 composite integers through public bit shifts, gcd-checked point arithmetic and recursive splits. The cases include repeated prime factors and exact prime powers. Its finite Boolean primality test uses trial division on these test sizes. Run `python3 -B experiments/moving-legendre.py`. [Recursive arithmetic replay](../experiments/moving-legendre.py)
