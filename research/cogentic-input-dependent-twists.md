# Prescribing twists of a fixed input-dependent elliptic curve

For fixed distinct roots, an exact rational substitution cannot turn the full twist condition into one unshifted quadratic character or a product of independent quadratic norms. The obstruction is the genus of the curve obtained by adjoining the proposed square root. A uniformly random origin instead gives short consecutive lists that realize every local difference-sign profile with high probability, uniformly in the input root heights. The random origin has polynomial bit length. Choosing an origin deterministically at that cost remains open here. [Fixed marking and twist signs](cogentic-fixed-marking-twists.md)

## A genus obstruction to rational norm substitutions

Fix distinct rational \(e_1,e_2,e_3\) and \(f(X)=\prod_i(X-e_i)\). On the moving marking \(c\), the twist of \(E:y^2=f(x)\) has class \(f(c)\). Suppose one tries to realize that class by an unshifted parameter, or by a prescribed rational squareclass function \(G(t)\), using a nonconstant \(c(t)\in\mathbb Q(t)\) and an identity
\[
                    f(c(t))=D_0 G(t) R(t)^2
\]
with \(D_0\in\mathbb Q^\times\). On the source \(C_G:\ s^2=G(t)\), the pair \((c(t),D_0 sR(t))\) gives a rational map to the target twist \(E_{D_0}:\ y^2=D_0 f(x)\). Over \(\overline{\mathbb Q}\) this is a map to \(E\) after scaling the ordinate by \(1/\sqrt{D_0}\). The rational map extends to the smooth projective source because the target is proper. It is nonconstant since the abscissa is nonconstant.

If \(G\) is square, use either rational component of the source after base change. If its double cover has two branch points, the connected source has genus zero. In either case Riemann–Hurwitz forbids the map. This includes \(G=t\), and a product or quotient of at most two linear factors after removal of squares. If \(G\) has four branch points, including any odd pole at infinity, the source has genus one. After choosing geometric origins the morphism is an isogeny up to translation, so the source elliptic curve must be isogenous to \(E\). The degree-four character in the reciprocal conic construction is consistent with this restriction. [Morphisms of elliptic curves](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)

For the pairwise parametrization, prescribe global squareclasses \(d_1,d_2\) for \(c-e_1,c-e_2\). The conic \(d_1u^2-d_2v^2=e_2-e_1\) is rational once a point is supplied. Its map \(c=e_1+d_1u^2\) has degree four and branches only over \(e_1,e_2,\infty\). Prescribing \(c-e_3=d_3w^2\) is therefore a double cover of that conic with four simple branch points over the distinct value \(e_3\). The poles are even and supply no additional branches. Its genus is one even when the first conic has an explicit point. [Reciprocal conic parametrization](cogentic-fixed-marking-twists.md#consecutive-conic-parameters)

There is also a several-parameter obstruction. Suppose \(G\) is a product of powers of independent parameters \(t_i\). The dominant substitution \(t_i=u_i^2\) makes \(G\) a square on a rational variety. The identity would then give a rational map from that variety to \(E\). Over \(\overline{\mathbb Q}\), restricting to the generic rational line in each coordinate direction shows that the map is independent of that coordinate, by the genus-zero case over the algebraic closure of the other coordinates' function field. It follows that the map is constant. The same argument applies when \(G\) is a product of independent binary quadratic norm forms in disjoint variable pairs. Over \(\overline{\mathbb Q}\) each norm is a product of two independent linear coordinates, and squaring the new coordinates makes the product a square on a rational variety. The norm fields and \(D_0\) may depend on the supplied roots. This argument concerns rational identities on independent parameter spaces. It allows coupled norm equations to have nonrational covers, and leaves open constructions that select rational points rather than parametrize all of them.

## Why a fixed global twist may fail even with local separation

Take \(f(c)=c(c-1)(c-2)\), \(p=43\), and \(q=47\). The pair-bit convention gives \(L(-1)=3,L(2)=1,L(1)=0\). At \(c=3\), \(f(c)=6\) is a square at both primes. The three Kummer columns for the fixed marking are \((1,1),(1,3),(0,3)\), so their stacked rank is three. Yet the global squareclass \(1\) has no admissible rational lift. Translating by one gives \(y^2=x^3-x\), and a point with \(y\ne0\) gives a rational right triangle of area one with legs \(\lvert(x^2-1)/y\rvert,\lvert2x/y\rvert\).

For the elementary descent, a rational triangle of area one would give an integer right triangle of square area after clearing denominators and removing common content. In a primitive such triangle write the legs as \(2ab,a^2-b^2\), with \(a,b\) coprime and of opposite parity. The four positive integers \(a,b,a+b,a-b\) are pairwise coprime and have square product, so all four are squares. Write \(a=r^2,b=s^2,a+b=w^2,a-b=v^2\). The integer legs \((w+v)/2,(w-v)/2\) have hypotenuse \(r\) and square area \((s/2)^2\), a smaller instance. This rules out the original triangle. The example separates the choice of a global squareclass representative from the local conditions. Choosing a different global representative can work, as \(f(3)=6\) shows. [Fixed-marking Kummer columns](cogentic-fixed-marking-twists.md#one-marking-for-all-remaining-difference-colors)

## A second moment for complete random origins

Let \(p,q>3\) be distinct prime divisors of \(N\). Assume the rational roots are distinct modulo each prime and their denominators are units. Choose the origin \(A_0\) uniformly modulo \(N\) and take \(c=A_0+t\) for \(1\le t\le H\le\min(p,q)\). These candidates can be reduced modulo \(N\). A prescribed joint profile gives three nonzero signs at each prime, one for each difference \(c-e_i\).

Expand its indicator as the product of the six factors \((1+\epsilon\chi_\ell(c-e_i))/2\). The expansion is exact off the roots. At most six progression indices meet a root at either prime, so using the expansion there changes the count by \(O(1)\). Each of the 63 nonconstant terms is a product of one or two factors of the form \(\chi_\ell(F_I(A_0+t))\), with \(F_I(X)=\prod_{i\in I}(X-e_i)\) for a nonempty subset \(I\). For one such term let \(S\) be its sum over \(t\). Its diagonal second moment is at most \(H\). On different indices the active prime contributes the complete correlation
\[
 \frac1\ell\sum_{a\in\mathbb F_\ell}
            \chi_\ell\!\left(F_I(a+t)F_I(a+s)\right)\qquad(t\ne s).
\]
The polynomial is nonsquare. Otherwise its two translated root sets would be equal, and a nonzero translation would preserve a nonempty set of size at most three in a prime field of size greater than three. Any such translation has a single orbit on the whole field. Weil bounds the correlation by \(O(\ell^{-1/2})\), uniformly in the roots. The two prime coordinates of the origin are independent by CRT, so even when both factors are active the full correlation is bounded by \(O(p^{-1/2}+q^{-1/2})\). Thus
\[
 \mathbb E |S|^2\ll H+H^2(p^{-1/2}+q^{-1/2}).
\]
Cauchy–Schwarz over the finitely many terms and Markov's inequality show that, for any fixed \(\eta>0\), the probability that any of the 64 profile counts differs from \(H/64\) by more than \(\eta H\) is
\[
                   O_\eta(H^{-1}+p^{-1/2}+q^{-1/2}).
\]
The \(O(1)\) excluded indices are absorbed for sufficiently large \(H\), with a threshold depending only on \(\eta\). The same proof applies to the nonconstant twist character on a reciprocal conic parameter, whose polynomial has at most four distinct roots and is squarefree after removing square factors. Use \(p,q>4\) there. [Weil's complete character sums](https://pmc.ncbi.nlm.nih.gov/articles/PMC1079093/) · [The conic character](cogentic-fixed-marking-twists.md#what-the-twist-can-change)

For a robust \(b\), each of the four prescribed pairs of twist signs has separating profiles in the fixed marking. Taking \(\eta<1/64\) gives all four choices in the same short random list with the stated probability. For arbitrary distinct roots the local sign-profile bound applies independently of any additional separation requirement. The computation uses a random integer of \(O(\log N)\) bits and polynomial work in the root bit lengths and \(H\). It uses the hidden primes only in the analysis. A proper gcd from an excluded root or a downstream split can be verified publicly. The complete-origin distribution is essential to the calculation. It supplies no bound for a prescribed origin or a deterministic short list of origins, and it does not create smooth local group orders if neither twist has one.
