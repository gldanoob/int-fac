# Private prime ideals on almost all near-cube cubic and quartic grids

Fix a balance ratio \(R>1\) and constants \(c,C>0\). Among the products \(N=pq\in[X,2X)\) of distinct primes with \(p\le q\le Rp\), the exceptional proportion in the following statement is at most \(\exp(-(1/(9c)+o(1))V)\), where \(L=\log X\), \(W=L^{1/3}(\log L)^{2/3}\) and \(V=L^{2/3}(\log L)^{1/3}\).

Set \(M=\lfloor N^{1/3}\rfloor\). For every integer \(m\) with \(|m-M|\le e^{CW}\), consider **all** monic integer polynomials \(f\) of degree three or four with coefficient height at most \(m e^{CW}\) and \(f(m)=N\). They are irreducible, their derivatives at \(m\) are units modulo \(N\), and their fields have no quadratic subfield. Every primitive direction \(|a|,b\le A=\lfloor e^{cW}\rfloor\), \(b>0\), has unit reduction \(a-bm\bmod N\). Its field element has an odd valuation at a prime ideal private to that direction within the grid. This includes the [monic carry and its quartic companion](cogentic-monic-pair.md) whenever they are chosen at the stated height, and permits adaptive choices anywhere in the box. The [centered quadratic theorem](cogentic-centered-quadratic-density.md) uses one varying residual. Here the middle carry digit supplies that variation at nonzero slopes, and the constant digit handles the zero direction.

## Freezing the carry digits

Write the possibly signed remainder as \(N-m^3=c_0+mc_1+m^2c_2\) with \(0\le c_0,c_1<m\) by Euclidean division. The near-cube condition gives \(|c_2|=O(e^{CW})\), and \(m\asymp X^{1/3}\). Take the two base polynomials
\[
 F=T^3+c_2T^2+c_1T+c_0,\qquad G=F+(T-m)T^3.
\]
An eligible polynomial of degree three or four equals the corresponding base plus \((T-m)P\), with \(P\in\mathbb Z[T]\) of degree at most one or two, respectively, since the difference is integral and vanishes at \(m\). Comparing the constant, linear and, if present, quadratic coefficients in order gives \(|P_j|=O(e^{CW})\) for every coefficient. For example the constant difference is \(-mP_0\) and the next difference is \(P_0-mP_1\). This description does not require Eisenstein parity. We count the entire digit and perturbation boxes, including points beyond the original input interval.

At a primitive mark with \(a\ne0\), freeze \(m,c_2,c_0,P,a,b\) and vary \(c_1\). The marked homogeneous value is affine with slope \(ab^2\) in degree three and \(ab^3\) in degree four. At \((0,1)\) freeze \(c_1\) instead and vary \(c_0\), with slope one in both cases. Each form is injective on its varying digit, can vanish once, and has absolute value at most \(T_*=m\exp(O_{c,C}(W))\).

Let \(y=2A^2\). The number of positive integers through \(T_*\) with all prime valuations above \(y\) even is at most
\[
 T_*^{1-\lambda}\zeta(2-2\lambda)\prod_{p\le y}(1-p^{-1+\lambda})^{-1}.
\]
This is the Euler product bound from the [centered quadratic count](cogentic-centered-quadratic-density.md#a-count-of-possible-norms). Choose \(\lambda=((2/3)\log L-2\log\log L)/\log y\), which lies in \((0,1/4]\) for large \(X\). The logarithm of the finite Euler product is \(O(y^\lambda\log\log(3y))=o(V)\) and \(\lambda\log m=(1/(9c)+o(1))V\). Thus at most \(m\exp(-(1/(9c)+o(1))V)\) varying digits give zero or an absolute value with all valuations above \(y\) even. This uses injectivity even when the digit interval is clipped. After summing over the other digit, \(O(X^{1/3})\) bases, and \(\exp(O_{c,C}(W))\) choices of high digits, perturbations and marks, the exception count is at most \(X\exp(-(1/(9c)+o(1))V)\).

The same calculation permits an offset cap \(J=\exp(\eta V)\) and a height cap \(m\exp(\theta V)\) for fixed \(\eta,\theta\ge0\) with \(\eta+4\theta<1/(9c)\). The high digit contributes \(\exp((\eta+o(1))V)\), the three quartic perturbation coefficients contribute \(\exp((3\theta+o(1))V)\), and the bound on \(T_*/m\) contributes \(\exp((\theta+o(1))V)\). This leaves a positive exponential saving on the \(V\) scale. All the auxiliary polynomial-margin counts below still apply because these additional parameters have size \(X^{o(1)}\).

## Irreducibility, quadratic subfields and gcds

For the following counts freeze \(m,c_2,c_1,P\), so only the constant coefficient varies with \(c_0\). There are \(X^{2/3+o(1)}\) frozen tuples. The cubic quadratic coefficient has size \(X^{o(1)}\), while its lower coefficients have size at most \(mX^{o(1)}\). An integer root therefore has absolute value at most \(\sqrt m X^{o(1)}\), by comparing the leading term against the other three terms. Each root forces at most one \(c_0\). This bounds reducible cubics by \(X^{5/6+o(1)}\).

Write the quartic as \(T^4+a_3T^3+a_2T^2+a_1T+a_0\), where \(|a_3+m|\le X^{o(1)}\) and the other coefficients are bounded by \(mX^{o(1)}\). Any nonzero integer root \(t\) satisfies \(|t(t+a_3)|\le mX^{o(1)}\) after dividing its polynomial identity by \(t^2\). Since at least one factor in this product has absolute value at least \(|a_3|/2\), the root lies within \(X^{o(1)}\) of zero or \(-a_3\). Those possibilities, including zero, cost \(X^{o(1)}\) choices of \(c_0\) per frozen tuple.

A quartic with a rational quadratic factorization, or an irreducible quartic whose field contains a quadratic subfield, has an integer root of the cubic resolvent
\[
 R(z)=z^3-a_2z^2+(a_3a_1-4a_0)z+4a_2a_0-a_3^2a_0-a_1^2.
\]
Indeed the resolvent roots are the three sums of products associated with partitions of the four roots into pairs. A quadratic factorization supplies a Galois-invariant partition. A quadratic subfield supplies the partition by restriction of the four embeddings to its two embeddings. The corresponding sum is a rational algebraic integer.

Put \(b_0=4a_2-a_3^2\), \(z_0=b_0/4\), and \(R_0(z)=z^3-a_2z^2+a_3a_1z-a_1^2\). If \(z\in\mathbb Z\) is a resolvent root, then \(a_0(4z-b_0)=R_0(z)\). We have \(z_0\sim-m^2/4\) and \(R_0(z_0)\sim-m^6/64\), because the lower terms are \(o(m^6)\). Thus \(v=4z-b_0\) is nonzero. The integer polynomial in \(4z\) given by \(64R_0(z)\) shows that \(v\mid 64R_0(z_0)\). That fixed nonzero integer has size \(X^{O(1)}\), so it has only \(X^{o(1)}\) signed divisors. Each gives at most one root \(z\) and one value of \(a_0\). This argument allows odd \(a_3\) and bounds all the remaining reducibility and quadratic-subfield exceptions by \(X^{2/3+o(1)}\). Cubic fields have no quadratic subfield by the degree formula.

On the balanced semiprimes the mark value has absolute value at most \(A(1+m)=o(\sqrt X)\) and is nonzero, hence is a unit. For a frozen tuple the derivative is independent of \(c_0\), asymptotic to \(3m^2\) or \(m^3\) in degree three or four, respectively. It has at most \(O_R(1)\) prime divisors comparable to \(\sqrt X\). For each one there is at most one \(c_0\) with \(p\mid N\), since \(N\) varies by unit steps over a length \(m<p\). This adds \(X^{2/3+o(1)}\) direct derivative-gcd exceptions. The balanced semiprime population is \(\gg_R X/L^2\), by choosing both primes in a fixed sufficiently narrow interval above \(\sqrt X\) and applying the prime number theorem. Dividing the counts by this lower bound gives the stated exception proportion.

## Mixed ordinary relations

An odd norm valuation at a rational prime \(p>2A^2\) gives an odd valuation at some prime ideal over \(p\). That ideal cannot divide a second primitive direction in the same field, since it would then contain their nonzero determinant of absolute value at most \(2A^2\). The rational contents discussed here come from normalizing bounded integer marks, so all their prime factors are at most \(A\). Signs have no finite valuations. Thus an ordinary product which is a square in a listed field has even aggregate exponent at each primitive direction, even when repeated directions, rational mark contents, negative exponents and independent field signs are used. Its remaining rational scalar must be a rational square, since a rational nonsquare becoming square would give a quadratic subfield. This also excludes \(-1\).

In a mixed library at one common \(m\), suppose every mark label has even total incidence across the fields, and the independent signs have even total parity as in the [signed mixed decision](cogentic-monic-mixed-complete.md#normalization-and-signs). Each field square root is, up to sign, its rational scalar square root times its primitive mark half-product. The product of these expressions reduces modulo \(N\) to the canonical half-product of the original labels up to a global sign. To see this also for nonprimitive labels, separate each label into its rational content and primitive direction, and halve the total exponents. The two rational coefficients have the same square because the product of the field signs is one. Hence these libraries have no productive ordinary mixed relation under the specified normalization. Independent unit corrections and other field heights or arguments remain outside this result.

The [exact replay](../experiments/cogentic-near-cube-density.py) checks 1,440 cubic and quartic carry instances, including the norm slopes and derivative identities, and reconstructs 36 integer resolvent roots from the fixed divisor condition.
