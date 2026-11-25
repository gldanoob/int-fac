# Computing the middle digits of a three-square count at ordinary indices

For a positive integer $m\equiv3\pmod8$, write $C(m)$ for the ordered positive three-square count, $b=\lfloor\log_2m\rfloor+1$, and $k=\lfloor(\log_2m)/2\rfloor$. Given only $m$ and $r$, a deterministic polynomial-time calculation returns $\lfloor C(m)/2^{k-r}\rfloor$ or abstains. The least significant bit of this quotient is the requested digit. For $X<m\le2X$ and $0\le r\le\log_2\log X$, the number of inputs where it abstains or returns an incorrect quotient is unconditionally

$$
 O\!\left(\frac{X\,2^r(\log\log X)^{12}}{\log X}\right).
$$

Thus for every fixed $\eta>0$ it obtains all the digits down to $k-\lfloor(1-\eta)\log_2\log X\rfloor$ on a density-one set. By the verified Dirichlet GRH every returned quotient is correct, even at exceptional inputs. The proof counts ordinary indices in an interval. The [middle-bit factoring reduction](middle-three-square-bit.md) makes adaptive queries that depend on previous answers. Its last comparisons take place near deliberately selected thresholds.

## A calculation from the unfactored index

In the proof write $m=df^2$ with $d$ squarefree and $\chi$ the primitive character of discriminant $-d$. The Hurwitz and analytic class-number formulas give

$$
 \frac{C(m)}{\sqrt m}=\frac{3}{\pi}L(1,\chi)
 \prod_{p^h\parallel f} g_h(p),\qquad
 g_h(p)=1+(1-\chi(p))\sum_{i=1}^h p^{-i}.
$$

This includes $d=3$ with the usual unit weight. For $d>3$ it also gives $C(m)=3h(-d)V$, where $V=\prod_{p^h\parallel f}p^h g_h(p)$ is a positive integer. Each local integer has three possibilities at fixed $p,h$. [Hurwitz product, Chen and Garvan](https://arxiv.org/pdf/2010.14315#page=5) · [Class-number formula and local factors](ramified-three-squares.md)

Choose an integer $Q\ge5000$ and list all primes $p<2Q$. Remove all powers $p^{2h}$ of their square factors from $m$, keeping the exponents. For the resulting $m'$ the symbol $(-m'/p)$ equals $\chi(p)$ at every listed prime because the remaining square multiplier is coprime to all of them. At 2 the character is $-1$. This computes the listed $g_h$ exactly by trial division. The omitted local factors have log product between zero and $b/(2Q-1)$ since $g_h(p)\le1+2/(p-1)$ and $f$ has at most $b/2$ prime factors.

Let $B(u)=\prod_{p<u}(1-\chi(p)/p)^{-1}$. Retain the smallest and largest adjacent prefixes covering all integers $Q\le u<2Q$. Bach bounds the distance from $\log L(1,\chi)$ to a positive weighted mean of their logarithms by

$$
 e_Q=\frac{6.593\log d+19.321}{\sqrt Q\log Q}
$$

using the proved Dirichlet GRH. Use $0.7b$ as an upper bound for $\log d$. Enlarge the extremes by a logarithmic margin $E=e_Q+b/(2Q-1)+b^{-2}$ using an upper bound for $e_Q$. The extra $b^{-2}$ is used for the unconditional population result below. For $E<1$ the rational factors $1-E$ and $1/(1-E)$ enclose the required exponential factors. Multiply by $3\sqrt m/\pi$ and the known local corrections. Round the endpoints inward to the nearest possible integer counts, then return the quotient if the interval is nonempty and both endpoints give the same quotient. The trivial interval $[0,m]$ suffices when $E\ge1$ since each pair of first two coordinates determines at most one positive third coordinate. [Bach's weighted estimate, with the weights and constants in Jacobson §3.1](https://cspages.ucalgary.ca/~jacobs/PDF/mthesis.pdf#page=50)

For the asymptotic algorithm set $Q=\max(5000,b^{128})$. The prime products can be computed as exact rationals with polynomial bit cost, since the bit length of the full product is $O(Q\log Q)$. The replay rounds each product outwards on a fixed-point grid. A scale of $2^{b+10\lceil\log_2(2Q)\rceil+100}$ suffices asymptotically. Each single rounding error is at most the reciprocal of the scale and any subsequent product has size $O(\log(2Q))$ by Mertens' product estimate. Each prefix is also $\gg 1/\log(2Q)$. Use integer square roots and rational bounds from Machin's formula for $\pi$. All these operations have polynomial bit cost. The large asymptotic exponent in $Q$ is chosen to give a simple exceptional-set proof.

## How many true counts can be close to an endpoint?

Put $B=\log X$, so $b\asymp B$. With $Z=4X$ and $A=8$, Granville and Soundararajan approximate $L(1,\chi)$ by the Euler prefix through $y$, simultaneously for $y\le Z/2$, for all but $Z^{1/4}$ primitive characters with conductor at most $Z$. The relative error is $O(\log Z/y^{1/32})$. For our $y\in[Q-1,2Q]$ this is $O(B^{-3})$. Exceptional characters lift to $O(X^{3/4})$ values of $m$, since each gives at most $\sqrt{2X}$ square multipliers. Also discard $f>X^{1/4}$ at a cost $\sum_{f>X^{1/4}}2X/f^2=O(X^{3/4})$. On the remaining inputs every prefix is within relative $O(B^{-3})$ of the true value, and the interval contains $C(m)$ for large $X$ by its $b^{-2}$ margin. Its relative width before rounding is $O(B^{-2})$. [Granville and Soundararajan, Proposition 2.2, equation (2.1)](https://arxiv.org/pdf/math/0206031#page=7)

For these inputs $d>3$ for large $X$. We have $f\le V\ll f(\log B)^2$. Indeed $g_h(p)\le (1-1/p)^{-2}$. Split the product at $p=B$, using Mertens below $B$ and $O(B)$ prime factors above it. Moreover $L(1,\chi)\ll\log Q\ll\log B$ by the prefix estimate. Consequently $C(m)/\sqrt m\ll(\log B)^3$.

If the algorithm abstains on a remaining input, the class number lies within relative $O(B^{-2})$ of some positive
$$
 H_j=\frac{j\,2^{k-r}}{3V},\qquad 1\le j\ll 2^r(\log B)^3 .
$$
There are at most two values of $k$ in the dyad. For each permitted $f,V,k,r$ all these centers lie between $X^{1/5}$ and $O(\sqrt X(\log B)^3)$ for sufficiently large $X$. Here the lower bound uses $f\le X^{1/4}$ and $2^r\le B$. The number of all imaginary quadratic fields whose class numbers are within relative $O(B^{-2})$ of $H_j$ is $O(H_j^2(\log B)^3/B)$. This follows by subtracting Lamzouri's asymptotic for class numbers at the two endpoints, enlarging the interval slightly to include endpoint equalities. At fixed $f$ each field here gives at most one index $m$. [Lamzouri, Theorem 1.1](https://arxiv.org/pdf/1512.07134#page=1)

Summing $H_j^2$ over the given $j$ costs $O(X\,2^r(\log B)^9/f^2)$ using $V\ge f$. There are at most $3^{\omega(f)}$ possible $V$. The series $\sum_f 3^{\omega(f)}/f^2$ converges by its Euler product. Including the discarded indices now gives the stated bound. The conditional correctness for every nonabstention comes directly from Bach's enclosure.

## Explicit indices on either side of a threshold

For $h\ge4$ set $u=2^h$ and let $s=u^2+u+1$ for odd $h$, $s=u^2-u+1$ for even $h$. In both cases $s\equiv1\pmod3$ and each prime divisor of $s$ is $1\pmod3$: the appropriate sign of $u$ is a primitive cube root modulo that prime. Therefore $C(3s^2)=s$ by the local formula. The digit position at $m=3s^2$ is $k=2h$, and the count is within $2^h+1$ of $2^{2h}$, on opposite sides for the two parities of $h$. This gives an exponentially small relative separation as a function of the input bit length. An exact formula settles these individual examples. Their separation shows why inverse-polynomial relative precision alone cannot decide all inputs by rounding.

## Finite checks

Run `python3 experiments/middle-three-square-bit.py` from the repository root. An optional integer argument sets $Q$. The evaluator receives $m$ and a precomputed table of small primes. The reference separately calls PARI's Hurwitz class-number routine. The 1,030 cases include all eligible integers from 8,195 through 16,383 and six examples with square factors, including factors beyond the default cutoff. The replay checks the whole integer interval and each quotient it returns, and checks eight members of the near-threshold family through $h=257$. [Exact interval replay](../experiments/middle-three-square-bit.py)

| Prime cutoff $Q$ | Returned zero bit | Returned one bit | Abstentions | Quotients including one more low bit |
| ---: | ---: | ---: | ---: | ---: |
| 5,000 | 250 | 301 | 479 | 241 |
| 20,000 | 321 | 451 | 258 | 579 |
| 80,000 | 448 | 530 | 52 | 893 |
