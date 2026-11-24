# Prime-form powers and a second square witness

For every negative order discriminant $-d$ and every odd split prime $p\nmid d$, a specific even power of its prime form has a reduced leading coefficient at least $\sqrt{3d}/(4p^2)$ and a short, explicitly known representation of a square. One can obtain a prime $p=O(\log^2 d)$ by enumerating small split primes using Dirichlet GRH, as in the [genus argument](quadratic-order-reduction.md#small-split-primes-for-every-negative-order-discriminant). This constructs one witness with a large coefficient, outside the hypotheses of the [small-coefficient density bound](twisted-square-witnesses.md). The second witness must give a different root up to sign. [Schoof, §2](https://reneschoof.github.io/mcpaper.pdf) · [Lenstra–Pomerance, §§2.7–2.8](https://cr.yp.to/bib/1992/lenstra.pdf)

## Choosing the power

The $j$th power of a split prime ideal has form representative $(A,B,(B^2+d)/(4A))$ with $A=p^j$, by lifting and centering the middle coefficient. The leading coefficient $a$ after reduction is the form’s least nonzero value. At $(1,0)$ the value is $A$. At $(u,v)$ with $v\ne0$, completing the square gives a value at least $dv^2/(4A)$. Hence
$$
\min(A,d/(4A))\le a\le A.
$$
This also describes the first minima along the prime-power lattice chain in the upstream factoring project. [Pinned upstream Lemma B2](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/deterministic-smooth-relations-scope.md)

For a repeated-squaring orbit and $p<T\le(d/4)^{1/3}$, the first crossing of $a\ge T$ occurs exactly when $A=p^{2^i}$ first reaches $T$. The preceding $A$ was below $T$, so the new one is below $T^2$ and both arguments of the minimum are at least $T$. For a fixed seed, the exponent $1/3$ is sharp even with unlimited squarings. Put $s=3^{2^h}$ and $d=4s^3-1$. At step $h$ the reduced norm-three power is $(s,1,s^2)$ for a suitable choice of the prime form. Its square $(s^2,1,s)$ reduces to its inverse $(s,-1,s^2)$. The orbit alternates between the two from then on, and all earlier leading coefficients are smaller.

For the stronger construction, take the **first even exponent** $2m$ with $A=p^{2m}>\sqrt{d/3}$. Then $A\le p^2\sqrt{d/3}$, so $a\ge\sqrt{3d}/(4p^2)$. Every reduced leading coefficient satisfies $a\le\sqrt{d/3}<A$. Transporting the primitive vector $(1,0)$ through the reduction matrix gives a primitive vector $(u,v)$ on the reduced form $F=(a,b,c)$ with $F(u,v)=A=k^2$, $k=p^m$. Since $a<A$, a primitive vector with $v=0$ cannot give $A$. Completing the square now gives
$$
|v|\le2\sqrt{aA/d}\le2p/\sqrt3,\qquad
|u|\le\sqrt{A/a}+|v|/2\le(2p^2+p)/\sqrt3<2p^2.
$$
The lift, reduction matrix and witness use polynomial bit cost for polylogarithmic $p$. If $d=N$ is odd and $\gcd(a,N)=1$, the representation yields the root $(2au+bv)/(2k)$ of $a$ modulo $N$.

The [PARI check](../experiments/seed-powers.gp) verifies the crossing and the transported nonhorizontal witness on 7,863 discriminant/seed pairs. At prime bound 19 and height 16, trying the first one, two and three squarings cumulatively splits 110, 118 and 119 of the 120 semiprimes. The remaining input has no split seed through 19. For $N=14039$, the second squaring at $p=3$ gives $(52,-51,80)$. Its values at $(1,1)$ and $(11,3)$ are $9^2$ and $73^2$, and the two roots yield $\gcd(777-474,N)=101$.

## Which secants give a factor

Let $N\equiv3\bmod4$ be odd and let $D=-N$. In coordinates adapted to the known square, the form is $k^2U^2+bUV+cV^2$ with $4k^2c-b^2=N$ and $\gcd(2k,N)=1$. A rational line $L=kU+(j/n)V$ through the known conic point, with $n>0$ and $\gcd(j,n)=1$, gives
$$
\lambda=2kj-bn,\quad U=cn^2-j^2,\quad V=n\lambda,\quad
L=k(j^2+cn^2)-bjn .
$$
Put $S=2k^2U+bV$ and $Y=2kL$. Then $Y-S=\lambda^2$ and $Y+S=Nn^2$. The integer identity for the conic and both sign identities are kernel-checked. [Lean proof](../formal/Secant.lean) · [Cremona–Rusin on conic parametrization](https://johncremona.github.io/papers/conics.pdf)

The common content of $(U,V,L)$ is exactly $g=\gcd(\lambda,N)$. Indeed its gcd with $n$ is one since $U\equiv-j^2\bmod n$. Thus the content divides $\lambda$ via $V$ and divides $N$ via $Y+S$. Conversely $g$ divides $V$, $Y$ and $S$, and $2k$ is invertible modulo $g$, so $g$ divides all three coordinates.

After division by $g$, the normalized ratio $(S/g)/(Y/g)$ is defined modulo $N$ precisely when $\gcd(g,N/g)=1$. To see this, the normalized difference is $g(\lambda/g)^2$ and the normalized sum is $(N/g)n^2$. At primes dividing $g$, $n$ is a unit. At primes dividing $N/g$ but not $g$, $\lambda$ is a unit. At a prime dividing both, both sum and difference vanish. In the unit case the ratio is $+1\bmod g$ and $-1\bmod N/g$, so it yields mixed signs exactly for $1<g<N$. In the original form coordinates the relative sign is the same: for witness vectors $w_0,w_1$ with represented squares $k^2,(L/g)^2$, the polar form evaluated on them is $S/g$. Multiplying the two root numerators and using the discriminant identity gives the ratio of their roots as $(S/g)/(Y/g)\bmod N$ whenever $Y/g$ is a unit. Thus a search over rational slopes can take the gcd of the *linear* integer $\lambda$ before constructing either the conic point or its representation. For $N=17947$, $k=7,b=43,c=101$, the slope $19/3$ gives $(548,411,6439)=137(4,3,47)$ and $\gcd(\lambda,N)=137$.

## A guaranteed box and its cost

For the lifted prime-power representative, $\gcd(b,2k)=1$ and $|b|\le k^2$. If $\ell$ is the least prime factor of composite $N$, put $s=\lfloor\sqrt{\ell}\rfloor$. Two of the $(s+1)^2$ pairs in $[0,s]^2$ agree under $(j,n)\mapsto2kj-bn\bmod\ell$. Their difference gives $|j|\le s$, $1\le n\le s$ after a possible change of sign. A collision with $n=0$ would also have $j=0$. Dividing out a common factor preserves the congruence since both coordinates have size below $\ell$. [Brauer–Reynolds on the Aubry–Thue theorem](https://doi.org/10.4153/CJM-1951-042-6)

Throughout the larger box $K=\lfloor N^{1/4}\rfloor$, $2k>K$ rules out $\lambda=0$, since it would force $2k\mid n$. Also $|\lambda|\le(2k+k^2)K<N$ for large $N$ and polylogarithmic $p$. Thus any collision modulo $\ell$ gives a proper gcd, including on inputs with repeated primes. Product and multipoint evaluation applied to the lists $2kj,\ |j|\le K$ and $bn,\ 1\le n\le K$ find a split in $\widetilde O(K\log N)$ bit operations. If a row product has gcd $N$, one scan of that row suffices because no individual difference is zero modulo $N$. Doubling the box recovers the factor-sensitive scale $\sqrt{\ell}\operatorname{polylog}N$. Hittmeir’s Algorithm 3.2 already supplies this batch procedure, and its Pollard–Strassen application achieves the same scale with simpler setup. This gives a proved cost for finding a second sign through slopes. An improvement here would require structure forcing collisions at much smaller cost. [Hittmeir, Algorithm 3.2 and Corollary 3.4](https://doi.org/10.1090/mcom/3623)
