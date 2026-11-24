# Represented squares and their height

## A split that an odd-order walk misses

Let $F=(a,b,c)$ have discriminant $-N$, with $N$ odd and $\gcd(a,N)=1$. A displayed $F(u,v)=k^2$ with $k>0$ and $\gcd(2k,N)=1$ gives a root of $a$ modulo $N$,

$$
r=(2au+bv)/(2k)\pmod N,\qquad (2au+bv)^2+Nv^2=4ak^2.
$$

Two such roots differing up to sign give a proper factor by $\gcd(r-s,N)$. The construction only needs modular arithmetic. For the related halving construction Bosma–Stevenhagen require a primitive representation and a leading root coprime to the relevant discriminant. Their general Sylow algorithm uses the prime factorization of the discriminant. Dirichlet GRH helps find a nonresidue at a *known* prime in that algorithm. [Bosma–Stevenhagen, Lemma 2.4 and §§3, 6](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.170.pdf) · [Lagarias on the Sylow subgroup](https://doi.org/10.1090/S0002-9947-1980-0574794-0)

At $N=17947$ the norm-7 form has odd order 11. Its first square $F=(49,43,101)$ represents $7^2$ at $(1,0)$ and $47^2$ at $(4,3)$. The two modular roots up to sign are 7 and 6295. Their difference gives 131, and the complementary factor is 137. This uses a second representation outside the seed's squaring orbit.

With the first square of each split prime form of norm at most 19 and search height 16, the two-witness search splits 110 of the repository’s 120 semiprimes. Combining with the previous orbit search splits 119. The remaining $N=13843$ has **no split prime at all** through 19. Its first split prime is 23. The form $(61,59,71)$ then represents $23^2$ at $(-2,3)$ and $31^2$ at $(-1,4)$. The roots up to sign are 2108 and 3124, giving $\gcd(1016,13843)=127$. Allowing that prime on the remaining input closes the finite set. [Represented-square experiment](../experiments/represented-squares.gp) · [Original family and collision search](../experiments/square-walk.gp)

## What small witnesses would imply

Let $N$ be nonsquare. Take an odd split prime $p\nmid N$ and $N>4p^4$. The squared prime form has a representative $(p^2,b,c)$ with $|b|\le p^2$. Indeed, lift the chosen middle coefficient to a root of $b^2\equiv-N\bmod 4p^2$ and normalize modulo $2p^2$ by translation. Composition of the prime ideal with itself gives this class, and $c=(N+b^2)/(4p^2)>p^2$ ensures it is already reduced. There is a displayed witness $(1,0)$ for $p^2$. [Schoof, quadratic form arithmetic in §2](https://reneschoof.github.io/mcpaper.pdf)

Suppose another witness with $|u|,v\le H$, $v>0$, produces a root different up to sign from $p$. Put $s=2p^2u+bv$. Then $(2pk)^2-Nv^2=s^2$ and $|s|\le3p^2H$. Hence

$$
0\le\frac{2pk}{v}-\sqrt N\le \frac{9p^4 H^2}{2v^2\sqrt N}.
$$

If $9p^4H^2<\sqrt N$, Legendre’s criterion makes the reduced fraction $A/B=2pk/v$ a convergent of $\sqrt N$. With $t=\gcd(2pk,v)$, we have $t\mid s$ from $t^2\mid s^2$. Thus $A^2-NB^2=(s/t)^2$. The multiplier $t$ is a unit modulo $N$, so the mixed modular signs survive division. Taking the gcd of $A\pm|s/t|$ with $N$ recovers a proper factor. Enumerating the convergents with $B\le H$ takes $O(1+\log H)$ iterations, since denominators grow at least as fast as Fibonacci numbers. The square-root continued fraction uses exact integer arithmetic of polynomial bit length in $\log N+\log H$. This single list simultaneously covers successful bounded witnesses for **all** prime seeds satisfying the inequality. It is the single-square case of continued-fraction factoring. [Legendre’s criterion, Theorem 8.1.5](https://webspace.science.uu.nl/~beuke106/getaltheorie/getalscript.pdf#page=88) · [Morrison–Brillhart](https://doi.org/10.2307/2005475)

## Infinite obstruction to the bounded first-square search

For odd $m$, take $N=m^2+2$. If $(9p^4+2)H^2<2m$, a witness with $1\le v\le H$ and $|u|\le H$ would satisfy

$$
0 < (2pk)^2-(mv)^2=s^2+2v^2\le(9p^4+2)H^2<2m.
$$

Consecutive integer squares above $(mv)^2$ are separated from it by at least $2mv+1$. This is a contradiction. With $v=0$ every unit witness gives just $\pm p$. Thus for $p,H=N^{o(1)}$ the first squares of all such prime forms miss on sufficiently large members of this family. As $-N\equiv5\bmod8$, the prime 2 is inert. For a finite squarefree example take $m=10000000551$. Then $N=100000011020000303603=1381662089\cdot72376604827$. Several primes through 19 split, including 3 and 7, and every seed through 19 satisfies the inequality at height 16.

There are infinitely many **squarefree** composite examples with least prime factor $>N^\eta$ for some fixed $\eta>0$. They survive every subpower trial-division cutoff. The following argument combines a lower-bound sieve with a large-square-divisor estimate.

1. Choose an arbitrarily large prime $\ell\equiv1\bmod8$, put $X=\ell^8$, and choose $r$ with $r^2\equiv-2\bmod\ell$. Take odd $m\in[X,2X]$ with $m\equiv r\bmod\ell$. The progression has $Y\asymp X^{7/8}$ terms. Every $N=m^2+2$ on it is composite.
2. Sieve out primes $q<z=X^\epsilon$ with $\epsilon>0$ a sufficiently small fixed number below $1/8$. Each odd $q\ne\ell$ has at most two forbidden residues in the progression parameter, and 2 has none. For squarefree $d$ supported on these primes the counts are $Y\rho(d)/d+O(\rho(d))$ with $\rho(d)\le2^{\omega(d)}$ by CRT. The upper sieve-dimension bound holds with dimension 2 by Mertens’ product estimate. At level $Y^{1/2}$ the total remainder is $O(Y^{1/2+o(1)})$, and the ratio of log level to $\log z$ can be made sufficiently large. The lower beta sieve leaves $\gg Y/(\log X)^2$ terms, uniformly in $\ell$. [Lower-bound sieve, Theorem 2.1](https://kurlberg.github.io/eprints/2dscar.pdf)
3. The selected root has a unique lift modulo $\ell^2$, excluding $O(Y/\ell+1)$ terms. For $z\le q\le X^{2/3}$, $q\ne\ell$, an odd prime has at most two roots modulo $q^2$ by simple-root lifting. Summing over $q$ excludes $O(Y/z+X^{2/3})$ terms. For larger $q$, write $m^2+2=kq^2$ so $k=O(X^{2/3})$. Each $k$ gives only $O(1)$ pairs in this dyadic interval. Indeed $\alpha=m+q\sqrt{k}=m+\sqrt{m^2+2}$ is between $2X$ and $5X$. For any two distinct solutions ordered by $\alpha$, their ratio $R=\alpha_2/\alpha_1>1$ satisfies $R-1/R=|m_2q_1-m_1q_2|\sqrt{k}\ge1$ by taking conjugates and using norm $-2$. A zero determinant would force identical pairs by their common norm. Thus consecutive $\alpha$ differ by a factor at least $(1+\sqrt5)/2$. This bounds the entire large-square tail by $O(X^{2/3})$. [Classical squarefree-value problem and large-square estimates, Friedlander–Iwaniec](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/F7023D0C01F0F50F6BDDCB6586475B63/S0013091508000989a.pdf/squarefree_values_of_quadratic_polynomials.pdf)

The excluded terms are $o(Y/(\log X)^2)$. Every survivor is squarefree, composite, and coprime to all primes below $X^\epsilon$. Since $N\asymp X^2$, any fixed $0<\eta<\epsilon/2$ works for sufficiently large $X$. This conclusion permits more than two prime factors.

The obstruction uses the **first square** of a small split prime form in its reduced coordinates at $D=-N$. Later powers, twists of the discriminant, and combinations of different continued-fraction residues have different search spaces. The result rules out making this particular bounded witness sweep an all-input algorithm just by raising its subpower cutoffs.
