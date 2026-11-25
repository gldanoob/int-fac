# The number of prime pairs with a common cyclotomic divisor above a power threshold

Fix $k\ge3$ and $0<\theta<1/2$. The number of prime pairs $X<p<q\le2X$ with
$$
          \gcd(\Phi_k(p),\Phi_k(q))\ge X^\theta
$$
is $X^{2-\theta+o(1)}$. The same exponent holds if $p\le5X/4$ and $q>7X/4$. One may further require the common divisor to have a prime factor in $[X^\theta,2X^\theta]$. This gives a supply estimate in a smaller-overlap regime than the [near-maximal gcd bound](cyclotomic-overlap-count.md).

**Upper bound.** Write $F=\Phi_k$ and $d=\varphi(k)$. Fix an integer $p$ in the interval. There are $X^{o(1)}$ divisors of $F(p)=O_k(X^d)$ by the divisor bound. For each such divisor $h\ge Y=X^\theta$, the congruence $F(q)=0\bmod h$ admits at most $C_k^{\omega(h)}=X^{o(1)}$ residue classes. Indeed, the number of roots of a fixed squarefree polynomial modulo each prime power is bounded solely in terms of the polynomial. Hensel lifting gives this at primes away from the discriminant, and a Bézout identity between $F$ and $F'$ bounds it at the finitely many remaining primes. The Chinese remainder theorem gives the stated power of $C_k$. Thus at most $X^{o(1)}(1+X/Y)$ integers $q$ occur per $p$. This proves the upper estimate even over integer pairs. [Detailed prime-power root argument](cyclotomic-supply.md#a-limit-for-every-fixed-list-of-polynomial-exponents)

**Lower bound.** Use primes $\ell\in[Y,2Y]$ congruent to $1\bmod k$. There are $\gg_k Y/\log Y$ of them by the prime number theorem in fixed arithmetic progressions. Each has a reduced root class of $F$ corresponding to an element of exact order $k$. Write $I=(X,5X/4]$ and $J=(7X/4,2X]$. In either interval the expected main term for one reduced class modulo $\ell$ is $\gg X/(Y\log X)$.

For any fixed $A>3$, Bombieri–Vinogradov bounds by $O_A(X/(\log X)^A)$ the sum over moduli up to $2Y$ of the largest absolute prime-count error over reduced classes in each of $I,J$. Apply the theorem at the four endpoints and partial summation in its prime-counting version. The hypothesis $2Y\le\sqrt X/(\log X)^{C(A)}$ holds eventually for every fixed $\theta<1/2$. Discard the moduli at which one error exceeds half the lower bound for the main term. There are $O_A(Y/(\log X)^{A-1})$ discarded moduli. At each remaining eligible prime $\ell$, one chosen root class therefore furnishes $\gg(X/(Y\log X))^2$ pairs with one prime in each interval. [Bombieri, *On the large sieve*](https://doi.org/10.1112/S0025579300005313) · [Baier–Zhao, equation (1.1)](https://www.impan.pl/shop/en/publication/transaction/download/product/82297#page=1)

Any pair can recur for only $O_{k,\theta}(1)$ primes $\ell\ge Y$, since their product divides $F(p)\le(2X+1)^d$. This gives at least
$$
           \gg_{k,\theta}\frac{X^2}{Y(\log X)^2\log Y}
$$
distinct pairs, completing the exponent calculation. The large-sieve argument counts the inputs having a suitable divisor. The divisor itself is hidden, and in this range the earlier near-maximal-overlap algorithm does not give a polynomial time bound from this condition alone. [Algorithm and required size](2026-11-25-handoff/cyclotomic-supply/audit.md)

**Arithmetic replay.** At $X=8\,000$, $Y=20=X^{1/3}$ and $k=3$, direct gcds give 21,751 pairs at the threshold. Of these, 2,884 share a prime in $[20,40]$ congruent to $1\bmod3$. Counting each such prime separately gives 2,887 incidences. The replay independently recovers the threshold count by Möbius inversion over divisors and the incidence count by enumerating root classes modulo each prime. It repeats both comparisons for $k=4,5,6,8,10,12$, including a finite interval containing no eligible prime at $k=8$. [Exact GP replay](../experiments/moderate-cyclotomic-overlap.gp)
