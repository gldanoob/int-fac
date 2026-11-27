# Relative ideal norms preserve the quadratic class-width floor

Let $N>1$ be odd and squarefree, $B=\mathbb Q(\pi)$ with $\pi^2=-2N$, and $L/B$ a finite extension of degree $d$. Thus $\mathcal O_B=\mathbb Z[\pi]$ has discriminant $-8N$. Write $C=\operatorname{Pic}(\mathcal O_B)$ and $S=\operatorname{Nm}_{L/B}\operatorname{Pic}(\mathcal O_L)$. The image of a uniform higher class is uniform on $S$, and
$$
[C:S]=[H_B\cap L:B]\le d,
$$
where $H_B$ is the Hilbert class field of $B$. This describes the distribution if a uniform higher class is supplied. It does not require computing either class group. [Quadratic width count and minimum norm](keybreak-reduced-class-width-floor.md) · [Targeted quadratic root sampler](keybreak-targeted-quadratic-class.md)

## The exact norm image

Use the Artin isomorphism $C\simeq\operatorname{Gal}(H_B/B)$. The extension $H_BL/L$ is abelian and unramified, since base change preserves unramified local extensions and $B$ has no real places. For a prime $\mathfrak P$ of $L$ above $\mathfrak p$ of $B$, Frobenius at $\mathfrak P$ in $H_BL/L$ restricts to Frobenius at $\mathfrak p$ in $H_B/B$ raised to the residue degree $f(\mathfrak P/\mathfrak p)$. This follows from the defining residue-field power, and that exponent is exactly the one in $\operatorname{Nm}_{L/B}\mathfrak P=\mathfrak p^{f(\mathfrak P/\mathfrak p)}$. Multiplicativity therefore identifies the Artin symbol of the ideal norm with the restriction of the upstairs Artin symbol. The upstairs Artin map is onto by qualitative Chebotarev and factors through the ordinary class group because the extension is unramified everywhere. [Artin maps and Chebotarev](https://math.mit.edu/classes/18.785/2019fa/LectureNotes21.pdf)

The restriction of $\operatorname{Gal}(H_BL/L)$ to $H_B$ is injective, and its fixed field there is $H_B\cap L$. The image is consequently $\operatorname{Gal}(H_B/(H_B\cap L))$ by Galois correspondence. This does not assume $L/B$ is Galois. The index is the displayed degree, and divides $d$.

## Minima and the norm of a root identity

A homomorphism sends the uniform law on a finite group to the uniform law on its image. Thus squaring a norm class, or norming a squared class, gives the uniform law on $S^2$. Squaring also induces a surjection $C/S\to C^2/S^2$, so $[C^2:S^2]\le[C:S]\le d$. A fixed translated class has the analogous uniform law on a translate of $S^2$, inside the corresponding full genus.

For a class $c\in C$, let $m_B(c)$ be the least norm of an integral ideal in that class, including imprimitive representatives. Any choice of an integral representative of norm at most $X$ implies $m_B(c)\le X$. Therefore for any fixed translate $P$ of the output law,
$$
\Pr_{c\ {\rm uniform\ on}\ PS^2}(m_B(c)\le X)
\le d\,\Pr_{c\ {\rm uniform\ on}\ PC^2}(m_B(c)\le X).
$$
The same bound applies to a translate of $S$ versus the full class group. The representative may be chosen after seeing the upstairs output. For adaptive selection of $L$ or the translate, the comparison requires a fresh uniform draw conditional on that choice.

The existing upper count for discriminant $-8N$ bounds the right-hand probability under Dirichlet GRH, on the rough branch, by $(X/\sqrt N)\exp(o(H))$, with $H=(\log N)^{1/3}(\log\log N)^{2/3}$. Thus for $d=N^{o(1)}$ a fixed power saving below $\sqrt N$ is still polynomially rare, even after keeping the least norm among the integral representatives of each output class. If $d=\exp(o(H))$, the leading subexponential rejection exponent is unchanged as well. This estimate concerns norms taken down to $B$. It does not bound schemes using a genuinely different higher-field invariant or giving up the assumed uniform higher class law. [Quadratic upper count, including fixed multiplier discriminants](keybreak-reduced-class-width-floor.md#counting-the-rare-classes)

For the extraction identity suppose $I,J$ are integral ideals of $L$ prime to $N$ and
$$
I^2=(\alpha)J.
$$
Put $K=\operatorname{Nm}_{L/B}I$, $J_B=\operatorname{Nm}_{L/B}J$, and $\beta=\operatorname{Nm}_{L/B}\alpha$. Multiplicativity and the norm of a principal ideal give $K^2=(\beta)J_B$. With $t=\operatorname{Nm}_{B/\mathbb Q}K$ and $A=\operatorname{Nm}_{B/\mathbb Q}J_B$, this gives
$$
t^2=(\beta\bar\beta)A.
$$
Here all the ideals are coprime to $N$. The element $\beta$ and its inverse belong to the localization of $\mathcal O_B$ at rational integers coprime to $N$: their valuations vanish at every prime of $B$ above $N$. Hence the evaluation $\rho(\pi)=0\bmod N$ extends to them and gives units. It commutes with conjugation in this localization, so
$$
z=t/\rho(\beta)\pmod N
\quad\text{satisfies}\quad z^2\equiv A\pmod N.
$$
If a fixed ideal $P$ multiplies $I^2$ in the upstairs identity, then $p\,t^2=(\beta\bar\beta)A$ with $p=\operatorname{Nm}_{L/\mathbb Q}P$, and the root $p\,t/\rho(\beta)$ squares to $pA$. The same unit hypotheses apply. These formulas use an exact higher ideal identity, rather than only equality of field norms or selected modular branch values.

Changing the downstairs representative $J_B$ to $\gamma J_B$ replaces the generator by $\beta/\gamma$ and multiplies the root by $\rho(\gamma)$, whenever both representatives are prime to $N$. This accounts for reduction or rational content cancellation. Changing the norm seed $K$ by $\lambda K$ with $J_B$ fixed replaces $\beta$ by $\lambda^2\beta$ and multiplies the root by $\operatorname{Nm}(\lambda)/\rho(\lambda)^2=1$. A choice of generator may still change the global sign. Thus the transported root follows the ordinary quadratic mechanism. No polynomial-time claim for finding an upstairs identity or its generator is needed for the distribution bound. [Representative normalization and exact quadratic signs](keybreak-targeted-quadratic-class.md#exact-sign-fibers-and-the-genus-label)

## What happens to the relative signs

Conditional on a fixed downstairs square class in $S^2$, the uniform norm seed ranges uniformly over a coset of $S[2]$. The ordinary quadratic sign homomorphism $\sigma:C[2]\to U_2/\{\pm1\}$ shows that its relative signs are uniform on a coset of $\sigma(S[2])$, provided the public representative is fixed by the downstairs square class. Fixing an upstairs square class instead restricts the sign increments to $\sigma(\operatorname{Nm}_{L/B}\operatorname{Pic}(\mathcal O_L)[2])$. Neither condition by itself asserts that this image is the full sign group.

There is a clean exception when $d$ is odd. Extension of ideals followed by norm is the $d$th power map on $C$. It is the identity on $C[2]$. Thus the norm of the upstairs two-torsion already surjects onto $C[2]$ and both descriptions preserve all relative signs of the quadratic mechanism. In even degree one cannot infer this just from the ideal identity. For example a scalar unit modulo $N$ with square one maps under the relative norm to its $d$th power, which is one when $d$ is even. The class-width bound does not use preservation of any signs.
