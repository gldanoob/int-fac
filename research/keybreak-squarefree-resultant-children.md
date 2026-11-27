# Children of a quadratic mark with squarefree resultant

Let \(F(X)\) be the primitive irreducible field polynomial of degree \(d\) and leading coefficient \(A\), and let \(h(X)=aX^2+bX+c\) be a quadratic top mark. If the verified nonzero resultant \(R=\operatorname{Res}(F,h)\) is squarefree, each good prime dividing it gives exactly one degree-one child of multiplicity one. In particular a squarefree top product predicate settles the type of the algebraic children once its distribution is available. [Quadratic cost assumptions](keybreak-quadratic-top-budget.md) · [Linear child and extraction conventions in KeyBreak, Appendix H.2](https://crypto.sjtu.edu.cn/factoring.pdf#page=128)

## The local calculation

Suppose \(q\nmid A\). Over \(\mathbb Z_q\), make \(F\) monic by scaling by \(A^{-1}\). On the free module \(\mathbb Z_q[X]/(A^{-1}F)\) multiplication by \(h\) has determinant \(A^{-2}R\). Reducing this map modulo \(q\) gives nullity
\[
 k=\deg\gcd(\overline F,\overline h).
\]
Indeed, writing the monic reduction as \(gF_1\) and \(\overline h=gh_1\) with \((F_1,h_1)=1\), the kernel is precisely the multiples of \(F_1\) modulo \(gF_1\), of dimension \(\deg g\). Smith reduction over \(\mathbb Z_q\) now gives \(k\le v_q(R)\). A squarefree factor \(q\mid R\) forces \(k=1\), so polynomial gcd over \(\mathbb F_q\) recovers a unique monic factor \(X-s\). This holds even if \(q\) divides the leading coefficient of \(h\). Requiring \(q\nmid A\) keeps the root finite.

At a good prime, which also avoids the raw content and discriminant of \(F\), the algebra is unramified. Its prime over \(X-s\) has residue degree one; every other component is a unit for \(h\). The valuation at that prime is one because the norm has valuation one. Alternatively this follows directly from the sum of residue degrees times valuations. The top atom can therefore send \((q,s)\) to the original linear child recursion in the same field. Good primes below the terminal cutoff and exceptional primes use the existing terminal conventions. One tests goodness by divisibility of the known field integers for each discovered prime. With \(F(r/Q)=k_0N/Q^d\), a child \(q\nmid Qk_0N\) automatically avoids the excluded anchor slope, since \(F(s)=0\bmod q\). Root recovery and the goodness tests cost polynomial time in the recorded bit lengths.

## The row identity

Write \(m=r/Q\bmod N\) on a branch where all divided quantities are units. If \(h(r,Q)=ar^2+brQ+cQ^2=pn\), evaluation gives
\[
 p\equiv Q^2 h(m)/n\pmod N .
\]
The rational record therefore needs the sign, the known cofactor primes and the existing denominator label \(Q\). The algebraic atom is \(h(\alpha)\). With \(\beta=A\alpha\) its integral cleared numerator is \(a\beta^2+Ab\beta+A^2c\). Its signed field norm is \(R/A^2\). For a row mixing quadratic top atoms and linear internal atoms, the leading-coefficient exponent is the sum of occurrence multiplicities weighted by the respective degrees. Modulo two, only the linear occurrences enter this parity column. Norm-square, ideal and character columns can then be treated as in the field-labelled extraction argument. Powers of \(A\) are units on the continuing branch. Each cleared atom has polynomial bit length at the stated field heights. These identities concern individual verified records and do not estimate the number of records supplied by the proposed predicate. [Field-labelled square certificate](keybreak-polynomial-top-field-pool.md#field-labelled-rows-and-exact-extraction)

The finite matrix implication has a Lean proof over the integers. For any number of independent kernel vectors modulo a prime, that power of the prime divides the determinant. In particular a prime dividing exactly once gives a one-dimensional kernel. One may use the integral Sylvester matrix of the resultant here; over the residue field where the leading coefficient of the first polynomial is a unit, its nullity is the same gcd degree, including when the quadratic degree drops. [Determinant and modular nullity](../formal/cogentic/Cogentic/RandomizedPrimeDetNullity.lean)
