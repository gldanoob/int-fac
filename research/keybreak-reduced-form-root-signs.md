# CRT signs of roots obtained from reduced ideal squares

Let \(N>1\) be odd, \(\omega=\sqrt{-N}\), and \(\mathcal O=\mathbb Z[\omega]\), the order of discriminant \(-4N\). Fix a canonical properly reduced form in each ideal class. For a fixed square class with reduced leading coefficient \(A\) coprime to \(N\), a uniform class among its square roots gives a uniform modular root of \(A\) up to global sign. An independent fair global sign makes the root uniform over all CRT choices. The relative-sign statement holds for nonmaximal orders and square factors of \(N\). In the fundamental case, the two square-root classes giving each relative sign differ by the ramified class above \(2\). [Schoof, Theorems 2.3 and 2.3′](https://reneschoof.github.io/mcpaper.pdf#page=5)

## The root attached to a square

Use the proper invertible ideal class group \(G=\operatorname{Pic}(\mathcal O)\). Let \(I\) have norm \(t\) prime to \(2N\) and primitive square
\[
I^2=\langle t^2,B+\omega\rangle_{\mathbb Z}.
\]
Its norm form is \([t^2,2B,(B^2+N)/t^2]\). Apply a determinant-one change of basis whose first column is \((x,y)\), and let \(\gamma=t^2x+(B+\omega)y\) and \(\eta\) be the two resulting basis vectors. If the resulting reduced form is \([A,2b,c]\), then
\[
\operatorname{Nm}(\gamma)=A t^2,\qquad
\overline\gamma\,\eta/t^2=b+\omega.
\]
The imaginary coefficient in the second equality is the basis determinant. Consequently \(J=(A,b+\omega)=(\overline\gamma/t^2)I^2\), so \(I^2=(\gamma/A)J\). The map
\[
\rho\colon \mathcal O\longrightarrow\mathcal O/(\omega)\simeq\mathbb Z/N,\qquad
\rho(a+b\omega)=a\bmod N
\]
commutes with conjugation acting trivially on the target. It extends after inverting rational integers prime to \(N\). The normalized root \(z(I)=\rho(\gamma/t)\) satisfies \(z(I)^2=A\bmod N\). For a reduced form \(A\le\sqrt{4N/3}<N\), a nonunit \(A\) already gives a proper gcd.

The same normalization applies when the sampled leading coefficient is even. Write \(t=gq\) and \(I^2=gI_0\), with \(I_0=(q^2,b_0+\omega)\), as in the integer squaring formula. If \(\gamma_0=q^2 x+(b_0+\omega)y\) is the first reduced basis vector of \(I_0\), then \(I_0=(\gamma_0/A)J\). Thus the vector used in the class comparison for \(I^2\) is \(\gamma=g\gamma_0\); its normalized residue \(\rho(\gamma/t)=\rho(\gamma_0/q)\) is exactly the value computed by the sampler. Only \(q\) is inverted in this formula. [Integral squaring formula](keybreak-quadratic-class-integration.md#the-private-draw-and-the-computed-root)

Every class of \(G\) admits a primitive representative of norm prime to \(2N\). In its primitive norm form, for every prime \(p\mid2N\) choose a pair on which the form is nonzero modulo \(p\). For odd \(p\), the pairs \((1,0),(0,1),(1,1)\) suffice. For \(p=2\), one of the two diagonal coefficients is odd. Use CRT to lift these pairs to a primitive pair \((x,y)\). To ensure primitivity, choose any nonzero \(y\) in its required progression, then use the free residue of \(x\) at each prime divisor of \(y\) outside \(2N\) to avoid zero. The value \(t\) is the leading coefficient after a proper basis change. The corresponding ideal \((t,B_1+\omega)\) has norm \(t\). Each prime dividing \(t\) is unramified and split, since \(B_1^2=-N\bmod t\) and \(\gcd(t,2N)=1\). The ideal selects one branch above each such prime, so its square is primitive. This establishes existence at the class level. [Schoof, invertible ideals and primitive forms](https://reneschoof.github.io/mcpaper.pdf#page=5)

## The sign homomorphism

Put \(U_2=\{u\in(\mathbb Z/N)^\times:u^2=1\}\). CRT identifies \(U_2\) with one independent sign on each prime-power divisor of \(N\). If \([T]\in G[2]\), choose an integral representative \(T\) prime to \(N\), write \(T^2=(\beta)\), and define
\[
\sigma([T])=\bigl[\rho(\beta)/\operatorname{Nm}(T)\bigr]\in U_2/\{\pm1\}.
\]
The norm equality \(\operatorname{Nm}(\beta)=\operatorname{Nm}(T)^2\) gives a sign after reduction. The order has only units \(\pm1\), since its unit equation is \(a^2+Nb^2=1\). To change representatives \(T'=\lambda T\), localize by inverting the integers prime to \(N\). Both ideals become the whole localized ring, so \(\lambda\) is a unit there. The new sign differs by a global sign and by \(\rho(\lambda^2/\operatorname{Nm}(\lambda))=1\). Norm multiplicativity for invertible ideals shows that \(\sigma\) is a homomorphism.

For \([I']=[I][T]\), write \(I'=\lambda IT\) with both representatives prime to \(N\) and take the same fixed reduced ideal \(J\). Then
\[
\gamma'=\pm\lambda^2\beta\gamma,\qquad
t'=\operatorname{Nm}(\lambda)\operatorname{Nm}(T)t,\qquad
\bigl[z(I')/z(I)\bigr]=\sigma([T]).
\]
The last equation describes the torsor action of square-root classes on the relative signs. In particular, taking \(T=\mathcal O\) proves that the relative sign is independent of the representative within each square-root class.

For surjectivity, let \(d e=N\) with \(\gcd(d,e)=1\). The two-generator ideal \(J_d=(d,\omega)\) satisfies
\[
J_d^2=(d^2,d\omega,-de)=d\mathcal O,
\]
so it is invertible even in the nonmaximal order. An equivalent integral ideal is
\[
T_d=\frac{d+\omega}{d} J_d=(d+\omega,\omega-e)=(d+e,\omega-e).
\]
It has norm \(d+e\), as the quotient sends \(\omega\) to \(e\bmod(d+e)\), and \(\gcd(d+e,N)=1\). Its square is generated by \(d-e+2\omega\). Therefore its sign is represented by \((d-e)/(d+e)\), which is \(-1\bmod d\) and \(+1\bmod e\). These unitary divisors provide all relative sign patterns, including at odd prime powers. They serve here as existence witnesses and depend on the factorization of \(N\).

## Fundamental discriminant and the global sign

For odd squarefree \(N\equiv1\bmod4\), \(\mathcal O\) is maximal. Every class of order dividing two has a conjugation-invariant fractional representative. Indeed, if \(\overline I=\lambda I\), then \(\operatorname{Nm}(\lambda)=1\). Take \(\lambda=\tau/\overline\tau\), using \(\tau=1+\lambda\) for \(\lambda\ne-1\) and \(\tau=\omega\) otherwise. The ideal \(\tau I\) is invariant. Its exponents at split conjugate primes agree, inert prime ideals are rational principal ideals, and even powers of ramified ideals are rational principal ideals. Thus the ramified primes generate \(G[2]\).

There is exactly one relation between the ramified generators modulo their squares. If a squarefree product of those ideals of norm \(d\mid2N\) is \((\alpha)\), then \(\alpha\in\mathcal O\) and \(\alpha^2=\pm d\). Writing \(\alpha=x+y\omega\), the rationality of \(\alpha^2\) forces \(xy=0\), so \(d=1\) or \(d=N\). The relation at \(N\) is \((\omega)=\prod_{p\mid N}\mathfrak p_p\). For \(k\) odd primes dividing \(N\) there are \(k+1\) ramified generators, hence \(|G[2]|=2^k\). The dyadic class \([\mathfrak p_2]\) is nontrivial and has \(\sigma([\mathfrak p_2])=1\) since \(\mathfrak p_2^2=(2)\). Surjectivity and the target size \(2^{k-1}\) now give \(\ker\sigma=\langle[\mathfrak p_2]\rangle\). [Schoof, ambiguous forms](https://reneschoof.github.io/mcpaper.pdf#page=31)

Negating both columns of a reduction matrix leaves the reduced form fixed. A permitted deterministic convention chooses the representative of \(z\) in \([1,N/2]\), so uniform square-root classes alone cannot imply full sign uniformity. For instance at \(N=21\), the principal square class has \(A=1\) with CRT roots \(\{1,8,13,20\}\). The convention outputs \(1\) and \(8\). Norms \(37,11,19,209\) give representatives of the four square-root classes. One can take \(I_{37}=(4+\omega)\), \(I_{11}=((1-\omega)/2)\mathfrak p_2\), \(I_{19}=((6-\omega)/3)\mathfrak p_3\), and \(I_{209}=I_{11}I_{19}\). Generators of their squares are \(-5+8\omega\), \(-10-\omega\), \(5-4\omega\), and \(-134+35\omega\), respectively. Their displayed normalized residues are \(1,1,8,8\).

## Distribution needed by a sampler

For a uniform square-root class in a fixed square fiber, surjectivity makes its pushforward uniform modulo global sign. An independent fair sign after reduction makes the absolute root uniform. In particular, two independent roots from that conditional law have a mixed relative sign with probability \(1-2^{1-k}\). This yields a proper gcd by comparing the roots. Exact class uniformity gives the same conditional statement after tests depending only on the canonical square class.

If the whole class law is within total variation \(\varepsilon\) of uniform, the joint law of the square class and relative sign is within \(\varepsilon\) of its uniform-class counterpart by pushforward. For this comparison, attach an independent uniform dummy sign to classes yielding a nonunit \(A\). The reference joint law is then the uniform square-class marginal times the uniform relative-sign law. Comparing with the actual square-class marginal times that sign law bounds the average conditional sign distance by \(2\varepsilon\). A rare fiber can still have every sample on one relative sign. Redistributing the original mass of one fiber among classes mapping to that sign costs at most the original mass of the fiber in total variation. A per-fiber guarantee needs conditional uniformity, a suitable pointwise class bound, or control of the probability of the acceptance event. The cost of sampling factored norms subject to those guarantees remains open here.
