# Sampling factored ideals with almost uniform quadratic class

Let $N>1$ be odd, $D=-4N$, and $\mathcal O=\mathbb Z[\omega]$ with $\omega^2=-N$. Let $Y$ be a power of two in $[N^4,2N^4)$. There is a sampler whose accepted output is an exactly uniform primitive integral invertible $\mathcal O$-ideal of norm at most $Y$ and prime to $2N$, together with its prime-ideal factorization. Here primitive means that the ideal is contained in no $p\mathcal O$ for a rational prime $p$. One may additionally require the norm to be squarefree. In either version the class law is within $O(N^{-1/2})$ in total variation of uniform on $\operatorname{Pic}(\mathcal O)$, with an absolute implied constant. Under Dirichlet GRH, the expected bit cost is polynomial in $\log N$. A polynomial time cap allows an arbitrarily small inverse-power coupling error. The sampler uses the order as given, including when $N$ has repeated prime factors.

## Exact factored ideal proposals

For each rational prime $p\nmid 2N$ with $(-N/p)=1$, orient the two prime ideals by the smaller and greater roots of $x^2=-N$ in $[0,p)$. At an inert prime the only prime ideal is $p\mathcal O$. At a split prime the product of the two conjugate primes is $p\mathcal O$. Thus a primitive ideal prime to $2N$ is specified by an ordered pair $(a,e)$ of positive integers with $ae$ its norm, $(a,e)=1$, and all prime factors of $ae$ split and prime to $2N$. The prime powers of $a$ use the first orientation, those of $e$ the second. Norms prime to $2N$ are prime to the conductor, and their factorization in the order follows by extension and contraction from the maximal order. [Cox, §7, especially Proposition 7.19](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf)

Write $J=\log_2Y$. Pick $j$ uniformly from $0,\ldots,J$. Independently draw a uniform factored $a\in[1,2^{j+1}]$ and a uniform factored $e\in[1,Y/2^j]$ using Kalai's sampler. Retain $2^j\le a<2^{j+1}$, $ae\le Y$, $(ae,2N)=(a,e)=1$, and the splitting conditions. For squarefree norms also reject any repeated prime in the known factorization. Every eligible ordered pair has probability $1/(2Y(J+1))$, since its dyadic slot is unique and each rectangle has size $2Y$. This avoids a rejection correction by an unbounded number of roots of a given norm. Previous factored quadratic ideal samplers include Lebowitz-Lockard and Pomerance's construction for the maximal order. The separate class estimate below is uniform in the discriminant and applies in the given order. [Kalai's factored-integer algorithm](https://www.microsoft.com/en-us/research/publication/generating-random-factored-numbers-easily/) · [Lebowitz-Lockard and Pomerance, §7](https://math.dartmouth.edu/~carlp/kalai3.pdf) · [Related dyadic pair proposal](keybreak-factored-denominator-proposal.md)

For each retained prime use a random verified finite-field square-root algorithm and orient its result canonically. Hensel-lift the required root to its known prime power. CRT gives a root $u\bmod n$ for $n=ae$ and the actual ideal $(n,\omega-u)$ of index $n$, along with all its prime-ideal factors. For $n=1$ return the unit ideal. The local roots are simple since $p\nmid 2N$, and the congruence checks and all gcd tests use polynomial bit work. If a reduced form for the output class is wanted, start with $[n,2u,(u^2+N)/n]$ and use Gauss reduction. Its coefficients are primitive because $n$ and $2u$ are coprime. The conductor, the factorization of $N$, and a class group presentation are unnecessary for these operations. [Cox, Theorem 7.7](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf) · [Sutherland, class representation and reduction](https://math.mit.edu/~drew/sutherland-phd.pdf)

## A class count uniform in the order

Put $M=\operatorname{rad}(2N)$, $\rho=\prod_{p\mid M}(1-1/p)$, and $w=|\mathcal O^\times|$. For a class $\mathcal C$, fix an integral invertible ideal $\mathfrak a$ of inverse class. Every integral invertible ideal in $\mathcal C$ is uniquely $(\alpha)\mathfrak a^{-1}$ for $0\ne\alpha\in\mathfrak a$, up to multiplication of $\alpha$ by one of the $w$ units. Its norm is $Q(\alpha)=|\alpha|^2/\operatorname{Nm}\mathfrak a$. This is integral since $(\alpha)\subseteq\mathfrak a$ and the index of $(\alpha)$ in $\mathcal O$ is $|\alpha|^2$. Thus the plane lattice $\mathfrak a/\sqrt{\operatorname{Nm}\mathfrak a}$ has covolume $\sqrt{|D|}/2$ and shortest nonzero length at least one.

For $p\mid M$, invertibility makes $\mathfrak a$ locally principal at $p$. In a local basis obtained by multiplying the basis $1,\omega$ by a local generator, $Q$ is the norm form $x^2+Ny^2$ times a $p$-adic unit. The multiplier is a unit because the valuation of the determinant of multiplication by the generator is the valuation of $\operatorname{Nm}\mathfrak a$. Modulo an odd $p\mid N$, this norm form is $x^2$. Modulo two it is $(x+y)^2$. Consequently $p\mid Q$ cuts out one linear sublattice of index $p$, regardless of $\mathfrak a$. By CRT, $d\mid Q$ cuts out a sublattice of index $d$ for every $d\mid M$, and its shortest nonzero length remains at least one.

For a plane lattice of shortest nonzero length $\lambda$ and covolume $\Delta$, the disk of radius $R$ has $\pi R^2/\Delta+O(1+R/\lambda)$ lattice points. Take a shortest vector as the first basis vector and reduce the horizontal projection of the second to at most $\lambda/2$ in absolute value. The vertical spacing $h$ of rows is then at least $\sqrt3\,\lambda/2$. Each row contributes its chord length divided by $\lambda$, with $O(1)$ error. Summing the chords differs from the disk area divided by $h$ by $O(R)$ by the upper and lower sums of the decreasing chord length on each half-disk. This proves the uniform error with no upper bound on the second basis vector.

Remove the origin and use Möbius inversion over $d\mid M$. For $U\ge1$, the count of all invertible ideals in class $\mathcal C$ of norm at most $U$ and prime to $M$ is therefore
\[
 F_{\mathcal C}(U)=\frac{2\pi\rho U}{w\sqrt{|D|}}+O\bigl(\tau(M)\sqrt U\bigr).
\]
In particular the local factors lost at primes dividing the conductor or the discriminant are common across all classes. The choice of $\mathfrak a$ and the factors of $M$ enter only this estimate.

## Removing conjugate overlaps and repeated norms

In a formal product indexed by ideals prime to $M$, write $P,Q$ for the two split prime ideals over $p$ and let multiplication record ideal multiplication. The local series for all ideals at this prime is $(1-P)^{-1}(1-Q)^{-1}$. The correction to keep primitive ideals is $1-PQ$, since the canceled terms are exactly those divisible by both conjugate primes. For squarefree norms the correction is
\[
 (1+P+Q)(1-P)(1-Q)=1-P^2-PQ-Q^2+P^2Q+PQ^2.
\]
At an inert prime both filters have correction $1-(p\mathcal O)$, of nonconstant term norm $p^2$. The correction coefficients $\lambda(\mathfrak l)$ multiply across primes. Hence the filtered class count is exactly
\[
 \sum_{\operatorname{Nm}\mathfrak l\le Y}\lambda(\mathfrak l)\,
 F_{\mathcal C[\mathfrak l]^{-1}}(Y/\operatorname{Nm}\mathfrak l).
\]
For each fixed $\epsilon>0$ the series $\sum_{\mathfrak l}|\lambda(\mathfrak l)|/(\operatorname{Nm}\mathfrak l)^{1/2+\epsilon}$ converges with an absolute bound depending only on $\epsilon$. Its local factors are bounded by $1+3p^{-1-2\epsilon}+2p^{-3/2-3\epsilon}$. Applying the estimate for $F$ and extending its main term past $Y$ gives, uniformly in the class,
\[
 \frac{2\pi\rho Y}{w\sqrt{|D|}}\,L_*+O_{\epsilon}\bigl(\tau(M)Y^{1/2+\epsilon}\bigr).
\]
Here $L_* = \prod_{p\nmid M}(1-p^{-2})$ for primitive ideals and, for squarefree norms,
\[
 L_* = \prod_{p\nmid M,\ p\text{ split}}(1-3p^{-2}+2p^{-3})
       \prod_{p\nmid M,\ p\text{ inert}}(1-p^{-2}).
\]
Both are bounded below by a positive absolute constant. This argument allows split prime powers in the primitive version without allowing any overlap of conjugates.

If $M$ has $s$ distinct prime factors then $\rho\ge1/(s+1)$, by comparing the ordered primes with $2,3,\ldots,s+1$. Take $\epsilon=1/16$ and use $\tau(M)\le2\sqrt M$. The relative error in the common per-class main term is $O(N^{-3/4}\log N)=O(N^{-1/2})$. Normalizing the class counts changes the same bound by at most an absolute factor. The distribution bound holds unconditionally for the exact accepted law.

## Runtime and the principal genus

Summing the per-class estimate over the $h(D)$ classes gives
\[
 (1+O(N^{-1/2}))\,Y\rho L_*L(1,\chi_D)
\]
eligible ideals, by the ring class number formula $h(D)=w\sqrt{|D|}L(1,\chi_D)/(2\pi)$. If $D=f^2D_0$ with $D_0$ fundamental, the imprimitive value equals $L(1,\chi_{D_0})\prod_{p\mid f}(1-\chi_{D_0}(p)/p)$. The finite product has the same elementary inverse-logarithmic lower bound as $\rho$. Littlewood's bound under Dirichlet GRH gives $L(1,\chi_{D_0})\gg1/\log\log(3|D_0|)$ for large conductor, with an absolute positive lower bound on bounded conductors. Thus the exact outer acceptance probability is bounded below by an inverse polynomial in $\log N$. Only this runtime estimate uses GRH. [Cox, Theorem 7.24](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf) · [Lamzouri, Li and Soundararajan, Theorem 1.5 and equation (1.3)](https://www.math.ksu.edu/about/personal/xiannan/papers/QuaResL1ver2Sound.pdf)

Kalai's factorization sampler has polynomial expected bit cost with deterministic primality tests. For any prescribed constant $A>0$, choose a polynomial work cap with timeout $O(N^{-A})$. The outer and inner acceptance counts have geometric tails with inverse-polylogarithmic success. The elementary nonincreasing integer chain has a uniformly positive probability of halving at each nonterminal step, giving the required inverse-power tail on its length. The other uniform-integer and prime-nonresidue rejections also have geometric tails. A union bound over the polynomial work budget couples the capped sampler to the exact law with error $O(N^{-A})$, including when time and output are dependent. [Explicit coupling for factored dyadic proposals](keybreak-factored-denominator-proposal.md)

Squaring the ideal doubles its known exponents and maps its class to the principal genus $\operatorname{Pic}(\mathcal O)^2$. The square map has equal-size fibers over its image, so pushforward preserves the uniform target and can only decrease the total variation error. The squared ideal is still primitive and prime to $2N$, and has norm at most $Y^2$. Its norm is a square. A principal generator or a factor-base smoothness guarantee would require additional input.

An exact PARI/GP check compared the dyadic-pair ideals with primitive norm-form vectors in each reduced class for eight odd inputs and three norm bounds. All 129 class counts matched for both filters, including orders with conductor divisible by odd primes. The checks included 1,956 primitive ideals, of which 1,810 had squarefree norm.
