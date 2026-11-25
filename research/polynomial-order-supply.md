# How many balanced products can fixed polynomials supply with full cyclotomic orders?

Let $t\ge2$ be fixed, and let $N$ be the product of $t$ distinct primes in $(X,2X]$. Choose $t-1$ distinct prime indices $r$. At each index fix a finite list of nonzero integer polynomials $P$ of degree at most $d_r=\varphi(r)=r-1$. Call a factor $p$ **covered** when for every chosen index some entry satisfies
$$
                       0\ne P(N)\equiv0\pmod{\Phi_r(p)}.
$$
The entries can differ between factors and indices.

1. A deterministic algorithm using only $N$ and the fixed lists recovers every covered factor in polynomial bit time. One covered factor splits $N$. Coverage of all factors gives the complete factorization.
2. For any such fixed lists, at most $X^{1+o(1)}$ distinct products in the indicated interval have even one covered factor.
3. There are fixed lists attaining at least $c_t X/(\log X)^{C_t}$ distinct products in every sufficiently large interval, with **all** factors covered. In this construction every two factors differ by at least a fixed positive multiple of $X$.

Thus $1$ is the sharp exponent of $X$ for this degree-bounded supply model. For two factors this gives $X^{1+o(1)}$ as the optimal count among $\asymp X^2/(\log X)^2$ possible pairs. The counts concern full cyclotomic divisibility at fixed exponents. The earlier size-dependent list obstruction treats the relative gcd of partial orders in a different quantifier range. [Prior supply bounds](cyclotomic-supply.md)

## Recovering every covered factor

Put $L=\log N$ and $D=\lfloor N^{1/t}/2\rfloor$. The prime interval implies $D\le p\le 2N^{1/t}$. Try all selections of one entry $P_r$ per index, omitting zeros and moduli below two. For the right selection use the monic row $T$ at modulus $N$ and each monic $\Phi_r(T)$ at modulus $M_r=|P_r(N)|$. Their hidden divisors are $p$ and $\Phi_r(p)$ for the selected $r$. They are pairwise coprime. Indeed $\Phi_r(0)=1$, and a common prime of $\Phi_r(p),\Phi_s(p)$ for different prime indices would force $p\equiv1$ at that prime, since the order divides both $r$ and $s$. Substitution at $1$ would then force the prime to divide both $r$ and $s$.

Take lower bounds $D$ and $(D-1)^{d_r}$ for these divisors. For large inputs the lattice radius in the simultaneous univariate theorem has logarithm at least
$$
 \frac{(\log D)^2}{L}
  +\sum_r\frac{d_r(\log(D-1))^2}{\log M_r}-O(1)
  \ \ge\ L/t-O(1).
$$
Here $\log M_r\le d_rL+O(1)$ and $\log D=L/t+O(1)$. The constants depend only on the fixed lists and $t$. Skip selections with a lower bound exceeding its modulus. A bounded number of translated windows covers the balanced interval for every viable selection, by the same logarithmic bound. For instance the guaranteed radius can be rounded down by a constant factor using rational lower bounds for the logarithms, then bounded above by the interval length. Test all candidates by primality and division. Small inputs can be checked directly. The algorithm uses $N$ in every row computation, so a successful split preserves the ability to recover other covered factors from the original data. This applies the existing multiple-row theorem and its univariate integer lattice. [Radius, bit cost and prior lattice work](hidden-divisor-lattices.md#a-lattice-for-overlapping-public-moduli)

## Upper bound for every fixed list

Fix $p$ and write $N=pv$. A nonzero constant entry covers only bounded $p$. Write any other selected polynomial as $P=c\prod_i f_i^{e_i}$ with distinct primitive irreducibles, $S=\prod_i f_i$, $e=\max e_i\le d_r$. Put
$$
       h=\frac{\Phi_r(p)}{\gcd(c,\Phi_r(p))},\qquad
       h'=\prod_{\ell^u\parallel h}\ell^{\lceil u/e\rceil}.
$$
Coverage implies $h\mid S(pv)^e$, hence $h'\mid S(pv)$. Also $h'\ge h^{1/e}\gg X^{d_r/e}\gg X$. The number of roots of the fixed squarefree polynomial $S$ modulo $h'$ is $X^{o(1)}$, since there are at most constantly many roots modulo any prime power and $h'\le O(X^{d_r})$. Multiplication by $p$ permutes the residue classes. [Prime-power root count](cyclotomic-supply.md#a-limit-for-every-fixed-list-of-polynomial-exponents)

The $t-1$ moduli $h'$ divide pairwise coprime cyclotomic values. Their product is $\gg X^{t-1}$ and CRT leaves only $X^{o(1)}$ classes for $v$. Since $v\le(2X)^{t-1}$, this permits $X^{o(1)}$ numerical values per $p$. Summing over $p$ and the fixed number of selections proves the upper bound. Repeated factors and nonprimitive polynomials are included.

## A construction attaining the exponent

Take $h$ to be a fixed admissible-tuple length sufficient for $t$ primes in Maynard's Theorem 3.4. Set $A=8h$ and $a_i=A+i$ for $1\le i\le h$. The forms $a_i n+1$ are admissible since $n=0$ avoids all obstructions modulo each prime. Apply the theorem on $X/A<n\le5X/(4A)$. Its interval length is a fixed positive proportion of the starting point, and all coefficients are fixed. There are $\gg_t X/(\log X)^h$ integers $n$ giving at least $t$ primes. These values lie in $(X,2X]$ for large $X$, and differ pairwise by at least $X/A$. [Maynard, Theorem 3.4](https://compositio.nl/Content/prize2018_maynard.pdf#page=5)

For each $t$-element index set $I$ and $i\in I$, define the integer polynomial
$$
         H_{i,I}(Z)=Z\prod_{j\in I\setminus\{i\}}(a_j Z+a_i-a_j).
$$
For $N=\prod_{j\in I}(a_j n+1)$ and $p=a_i n+1$, we have $H_{i,I}(p)=a_i^{t-1}N$. At index $r$, form the monic integer polynomial
$$
    Q_{r,i,I}(V)=\operatorname{Res}_Z(\Phi_r(Z),\,V-H_{i,I}(Z)).
$$
It has degree $d_r$ by the product over primitive roots. Moreover $\Phi_r(Z)$ divides $Q_{r,i,I}(H_{i,I}(Z))$ in $\mathbb Z[Z]$ by monicity and vanishing at a primitive root. Include $P(U)=Q_{r,i,I}(a_i^{t-1}U)$ in the public list. The substitution proves coverage for every one of the $t$ primes at every index. These polynomials are fixed in advance and nonzero at all sufficiently large positive $N$. A given $N$ can arise from at most $th$ parameters $n$, since any chosen prime factor and its slope determine $n$. This proves the count of distinct inputs.

On this illustrative subfamily one can also factor by solving each fixed equation $\prod_{j\in I}(a_j n+1)=N$ for an integer $n$. The lattice algorithm works from the divisibility conditions themselves, including products outside these affine forms. The constant tuple length in the asymptotic construction comes from Maynard's theorem. The arithmetic replay below uses smaller lists.

## Exact replay

The GP experiment checks each resultant identity by polynomial division. For slopes $6,8,10$ it derives the lists at indices $2,3$ and sends only those lists, indices and $N=3\,095\,239\,393$ to the lattice decoder. The decoder recovers $1\,117$, $1\,489$ and $1\,861$ in 367 translated lattice calls. For the slopes $4,5$ at index $3$ the entries are $16U^2+16U+31$ and $25U^2+25U+13$. The product $174\,833=359\cdot487$ falls outside the affine relation $4(q-1)=5(p-1)$. The second polynomial supplies $359^2+359+1$ and the decoder recovers $359$ in 52 calls. The replay also compares the prime valuation rule used in the upper bound with literal divisibility for polynomials having content and repeated factors. [Exact GP replay](../experiments/polynomial-order-supply.gp)
