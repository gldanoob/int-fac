# Deterministic coefficient selection for Farey marks

Under the [fixed-multiple Farey-mark moment proof](cogentic-homogeneous-marks.md) and the [explicit conditional score](cogentic-conditional-score.md), there is a deterministic complete factoring algorithm on each \(N\ge2\) with bit cost
\[
 L_N[2/3,(8/3)^{1/3}]
 =\exp\!\left(((8/3)^{1/3}+o(1))(\log N)^{2/3}(\log\log N)^{1/3}\right).
\]
The coefficient is \(1.38672\ldots\). This is a manuscript-level refinement of the two-field order extractor. Cogentic's pinned deterministic theorem gives \(\exp(3(\log N)^{3/4})\). The present coefficient uses the verified Dirichlet Riemann hypothesis in the individual smooth-window estimates and in the final generator-prime sign count. [Cogentic, Theorem 1.1 and Lemmas 7.3–7.5](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf) · [Verified analytic inputs](https://math.mit.edu/~drew/grh/)

Put \(L=\log N,\ z=\log L,\ D=(L/z)^{1/3},\ H=Dz,\ V=DH\). Use degree \(d\sim xD\), mark height \(\log A\sim cH\), prime cutoff \(\log B\sim bH\) and coefficient Gaussian width \(\log W\sim sH\). Write \(S=xc+1/x\). Fix positive rational parameters with
\[
       xc>1/x,\qquad c>2b,\qquad b(c-b)>S/3,\qquad s>2c+2b.       \tag{1}
\]
Each field uses \(f_u=f^{(0)}+P_0\ell(X-m)G_u(X,1)\) with \(G_u(X,Y)=\sum_{j=0}^{n}u_jX^jY^{n-j}\), \(n=d-2\). Its \(n+1\) coefficients have independent centered discrete Gaussian laws of width \(W\). The rational marks are primitive \(v=(a,b_v)\) with \(a/b_v\in(0,.8]\) and distinct slopes, \(b_v\) prime near \(A\). The common integer root is \(m=\lceil N^{1/d}\rceil\). All the fixed-multiple construction's root brackets, positive-saddle ratios, one- and two-mark smoothness asymptotics and lattice estimates apply under (1). The first inequality supplies the required square-root margin for its individual modulus \(m\exp(O(H))\). The remaining grid change is proved below.

## The fixed cofactor sieve at \(c>2b\)

Write \(D_0=k_0k'_0\) for the fixed product of the two cofactors at \(m\). A retained numerator has \(\gcd(a-mb_v,D_0)=1\). Each underlying numerator interval of length \(\asymp Aw\) retains a constant fraction, uniformly in its allowed denominator. Indeed the proof of the original Brun estimate at modulus one applies, since \(\omega(D_0)=L^{O(1)}\) and \(\prod_{p\mid D_0}(1-1/p)\gg1\). These follow from \(\log c_d=(1/x+o(1))V,\ k_i<2c_d\), and \(p>d\) for \(p\mid D_0\), just as in the [fixed-parameter sieve](cogentic-deterministic-two-thirds.md#the-grid-its-sieve-and-its-real-roots). As usual the preliminary gcd checks of \(a-mb_v\) with \(N\) can return a proper divisor immediately.

Use the [two-row cell bound for Farey marks](cogentic-variable-multiple-lattice.md#the-cell-estimate-with-two-prescribed-rows). In that calculation \(Q\le B^2\) is the product of prescribed row primes, \(M\) the entry scale, and the summand is bounded by \(L^{O(1)}M(1+Q\,1_{a\equiv rb_v\bmod Q})\). The fixed-multiple family's \(Q\) is coprime to \(D_0\), as its eligible prime band excludes primes dividing \(D_0\) and \(\ell\nmid D_0\). The same bracket applies because the factors for at most three omitted primes are still polynomial in \(L\).

For any singular-series divisor \(h\), its primes are at most \(\sqrt B\). With the first mark fixed, \(h\mid\Delta=|ab_{v'}-a'b_v|\) prescribes one second numerator class modulo \(h\), coprime as a modulus to \(Q\). For an absolute upper bound drop the sieve on \(a'\) and use the constant surviving fraction in the denominator. The second-mark bracket mass is \(O(1/h+Q/(Aw))\). Likewise the intersection of the full \(Q\)-class and \(p^2\mid\Delta\) for \(p\mid Q\ell\) costs \(O(1/p+Q/(Aw))\) in bracket mass. The fixed family's extra condition \(p\nmid(a-mb_v)\) in \(\gamma\) only removes terms from these positive bounds. Thus the contribution of \(h>T=e^{100z^2}\), the restoration of unclean pairs, and the polynomial-weight errors from deleting large eligible prime divisors of \(\Delta\) are exactly bounded by the corresponding estimates (2)–(3) in the two-row proof. The \(\ell\)-suppression errors there also use only absolute upper bounds on at most \(d\) slopes. Dropping the sieve costs a constant and keeps the bound \(L^{O(1)}M(\ell^{-1}/h+Q/(Aw))\), even if the combined modulus includes \(Q\ell\).

For \(h\le T\), the fixed-family singular series requires \(\gcd(a-mb_v,h)=1\). Sum only over \(r_h\bmod h\) with \(\gcd(r_h-m,h)=1\). For a numerator restricted to this slope and any required compatible \(Q'\)-slope, \(Q'\mid Q\), the weighted residue count has main density
\[
             \frac{\kappa_h}{hQ'},\qquad
             \kappa_h=\prod_{p\mid(h,D_0)}(1-1/p)^{-1}\ll1.
\]
Indeed the fixed \(h\)-class already avoids all the displayed primes of \(D_0\). The modulus for the remaining sieve is \(hQ'\le TB^2\). In the short subdivisions used for the weighted Brun estimate the length divided by this modulus exceeds \(\exp((c-2b+o(1))H)\). Inclusion–exclusion through \(2\lceil z^2\rceil\) prime factors, at \(Z_{\rm Br}=\exp(100z^2)\), then gives a relative error \(O(e^{-4z^2})\) for interval counts. In the weighted version the error is relative to the specified sup norm, by subdivision of the interval into \(L^{O(1)}e^{4z^2}\) parts. These are the original finite Brun estimates with their required modulus bound verified. The product \(\kappa_h\) is independent of the denominator, grid interval and auxiliary \(Q'\)-slope.

In the centered numerator \(J(h,r_h)\), the atomic reference mean on the full \(Q\)-class and the constant term therefore acquire the same factor \(\kappa_h/h\). The source's local identity cancels the main terms. Inclusion–exclusion for the at most two row hits outside the full support has the same polynomial-gain error \(L^{O(1)}B^{-.49}/h\), since those primes are coprime to \(D_0h\). The resulting bound, including the Brun error, is
\[
 |J(h,r_h)|\ \ll\ L^{O(1)} M h^{-1}
          (B^{-.49}+hQ/(Aw)+e^{-4z^2}).
\]
Its square, summed over \(h\le T\) and admissible \(r_h\) with the positive coefficients \(\eta(h)\), is below \(e^{-7z^2}M^2\), since \(\sum_h\eta(h)\le(\log B)^{O(1)}\). In the uncentered total-mass variance the nonidentity terms cost \(O(\sum_{p>d}p^{-2})+o(1)\), using the same upper bound \(O(1/h+1/(Aw))\) and \(\eta(p)=O(1/p)\). The diagonal term still costs \(\exp((-2c+2b+2S/(3b)+o(1))H)M^2\). Conditions (1) make all required errors small. This proves the fixed-multiple moment estimates and the score expectation \(o(1)\) with \(c>2b\).

## Projecting the remaining coefficients

Fix the coefficients of one field in **decreasing degree**. After all indices greater than \(j\) have been fixed, a residual free vector \(u=(u_0,\ldots,u_j)\) contributes
\[
       b_v^{\,n-j} E_v(u),\qquad
       E_v(u)=\sum_{l=0}^{j} u_l a^l b_v^{j-l}
\]
to \(G(v)\). Add the entire known high-degree contribution to the constant part of the marked polynomial. Thus squarefree smoothness at this mark is a computable bounded unary function \(F_v(E_v(u))\). Factoring the known common factor \(b_v^{n-j}\) out of the *argument* restores a primitive evaluation vector at every stage. A row or derivative condition remains an affine congruence on the free vector after subtracting the fixed coefficients. At most two distinct marks occur in any one-field score term, and the combined row modulus \(Q_0\) is \(B^{O(1)}\). For terms involving marks, at most two prescribed root primes occur, so \(Q_0\le B^2\). Terms involving root multiplicity or shared roots alone require no marked evaluations and use at most two such primes.

For two distinct marks and \(j\ge1\), let \(E=(E_v,E_{v'})\), \(\Delta=|ab_{v'}-a'b_v|\), and \(q'=Q_0\Delta\). The [projective kernel lemma](cogentic-projective-kernel.md) gives \([\mathbb Z^2:E(\mathbb Z^{j+1})]=\Delta\). A compatible row system cuts out a coset \(u_*+\Lambda\), with \(Q_0\mathbb Z^{j+1}\subseteq\Lambda\). Hence \(q'\mathbb Z^2\subseteq E(\Lambda)\). Enumerate the at most \(q'^2=\exp(O(H))\) output residue pairs modulo \(q'\), testing compatibility of \(E(u)\) with that pair and all prescribed rows. These are integer linear congruences, solved by Hermite or Smith normal form with a slack variable for each modulus. Their sizes in bits are polynomial in \(L\). If no pair is compatible the term is zero. Otherwise compute \(I=[\mathbb Z^{j+1}:\Lambda]\) by the same integer linear algebra, and \(I_E=[\mathbb Z^2:E(\Lambda)]\) as \(q'^2\) divided by the number of compatible residue pairs. This permits arbitrary dependencies between row congruences, including after nearly every coefficient has been fixed. [Polynomial bit algorithms for integer normal forms](https://doi.org/10.1137/0208040)

For the unconditional free discrete Gaussian, the joint probability of the row system and a particular attainable value \(y=E(u)\) is, up to uniform relative error \(O(e^{-\Omega(L^6)})\),
\[
 \frac{I_E}{I\,W^2\sqrt{\det(EE^\mathsf T)}}\,
         \exp\!\left(-\pi y^\mathsf T(EE^\mathsf T)^{-1}y/W^2\right).       \tag{2}
\]
Indeed the congruence system has probability \(I^{-1}(1+O(e^{-\Omega(L^6)}))\) by Poisson summation. On every permitted fiber the homogeneous kernel contains the \(Q_0\)-multiples of the shifts of \((b_vX-aY)(b_{v'}X-a'Y)\), with basis operator norm before scaling at most \((2A)^2\). Here \(W/(Q_0(2A)^2)\gg L^3\) by (1). The conditional covariance and covolume formula of the projective lemma yields (2). For \(j=1\) the kernel has rank zero and the fiber numerator is exactly its displayed Gaussian times the normalizing constant. For \(j=0\), enumerate the single coefficient through its truncated range of size \(W\,\mathrm{poly}(L)\). One-mark terms use the analogous one-dimensional projection, directly summed over its unary array. Coincident marks combine their unary functions first. With no marks the row-coset probability alone suffices.

## Evaluating the two-variable sum in one array length

Set \(\xi=y_1/(Wb_v^j)\) and \(\eta=y_2/(Wb_{v'}^j)\), and let \(T\) be the \(2\times2\) Gram matrix of \((1,t,\ldots,t^j)\) at \(t=a/b_v,\ t'=a'/b_{v'}\). Its top eigenvalue is bounded absolutely for \(0<t,t'\le.8\). The minor from the first two coefficient positions is \(t'-t\), of magnitude at least \(A^{-2}\). Hence \(\|T^{-1}\|\le C A^4\) at every conditioning stage with \(j\ge1\). The exponential in (2) is
\[
                         g(\xi,\eta)=e^{-\pi(\xi,\eta)T^{-1}(\xi,\eta)^\mathsf T}.
\]
Keep \(|\xi|,|\eta|\le L^3\). The removed discrete probability, even without any row conditions, is \(O(e^{-cL^6})\). For example, if every free coefficient has magnitude at most \(L^3W/6\), then \(|E_v(u)|/(Wb_v^j)\le L^3/(6(1-.8))<L^3\). A union bound over \(O(d)\) one-dimensional tails suffices.

Choose rational \(\rho\asymp A^{-2}\) sufficiently small that \(\pi\rho^2\|T^{-1}\|\le1\). For any real \(\eta\), on the complex disk of radius \(\rho\) around any real first coordinate,
\[
                     |g(\xi,\eta)|\le \exp(\pi\rho^2\|T^{-1}\|)\le e .
\]
Partition the retained \(\xi\) interval into panels of half-width at most \(\rho/2\). On the panel centered at \(u\), its Taylor polynomial in \((\xi-u)/\rho\) through degree \(\lceil L^4\rceil\) has uniform absolute error at most \(2e\,2^{-\lceil L^4\rceil}\). For each compatible residue pair, panel, and polynomial degree, separately sum the first unary array times \(((\xi-u)/\rho)^l\) and the second unary array times the corresponding Taylor coefficient \(c_l(\eta)\). Multiply these two sums. The sum of all products gives (2) integrated against the two bounded unary tests to the stated precision. There are at most
\[
          \exp(O(H))\quad\text{panels, residue pairs and degrees together},
\]
and either unary array has length at most \(M_j=O(L^3 W A^j)\). Thus this step costs \(M_j\exp(O(H))\) bit operations. Even charging \(M_j^2\) individual approximation errors still loses just \(\exp(O(V))\) against \(2^{-L^4}\).

All unary values are obtained by exact polynomial evaluation and division by the eligible factor-base primes, in \(\mathrm{poly}(B,L)\) bit operations per entry. The density normalization and Taylor coefficients can be computed with dyadic interval arithmetic. On the scaled variable the exponential is \(e^{h_0+h_1t+h_2t^2}\). Its Taylor recurrence is \(l c_l=h_1c_{l-1}+2h_2c_{l-2}\), initialized by \(e^{h_0}\) and \(c_{-1}=0\). The real \(h_0\le0\), and \(\log(2+|h_1|+|h_2|)=O(H+\log L)\) on the retained panels. Guard precision \(L^{O(1)}\) bits absorbs even a factor \((2+|h_1|+2|h_2|)^{\lceil L^4\rceil}\), including all finite sums and normalizations. Underflowed values of \(e^{h_0}\) may be rounded to the working absolute precision. Integer weights \(a^l b_v^{j-l}\) have \(O(V)\) bits. This yields absolute error \(e^{-\Omega(L^3)}\) per bounded score term at the asserted bit cost.

## Selecting the fields and optimizing

Use the source-derived nonnegative score \(P\) whose expectation is \(o(1)\) and whose value below one guarantees rank. Its [separated expansion and deterministic coefficient approximations](cogentic-conditional-score.md) apply to the Farey marks by using their actual \(\mu_i(v)\), variances, and residue \(q_0=P_0\ell b_v|a-mb_v|\). The full or marked smooth indicators are the unary arrays just treated. Factoring \(|a-mb_v|\) for the scalar \(q_0/\phi(q_0)\) costs at most \(\exp((1/(2x)+o(1))V)\) across all marks by trial division. This is smaller than \(\exp(xcV)\) under (1). All remaining scalar integrals have \(\log(Y/S_{\rm width})=O(H)\) and the numerical scheme for the conditional score costs \(\exp(O(H))\). There are \(\exp(O(H))\) separated terms, with total absolute coefficient size \(\exp(O(L))\). The tiny deterministic norm-direction error \(O(d e^{-30z^2})\) from the denominator interval is already below the rank margin of the Farey-mark proof.

Condition the product Gaussian on every coefficient belonging to \([-L_0^2W,L_0^2W]\). The coordinates remain independent. The total removed probability \(O(de^{-cL^4})\) and bounded unary tests permit using full-Gaussian projections for each partial conditional expectation with absolute errors \(O(de^{-cL^4})\) per term, uniformly in fixed in-box coordinates. Minimize over each next coefficient by enumerating \(O(L_0^2W)\) integer choices and evaluating the remaining mean by (2) and the one-mark formulas. Fix every coefficient in the first field, then every coefficient in the second, keeping the order described above within each field. For the other, still-independent field use its unconditional factor or its already fixed value in each separated term. Each step changes the true conditional expectation by at most \(e^{-\Omega(L^2)}\) upward. Thus the resulting pair has \(P<1\) for sufficiently large \(N\). The verified homogeneous extractor returns its order exponent. The prime-base sweep, direct gcd splitting, recursive primality tests, and finite fallback are exactly those of the [single-exponent splitting proof](cogentic-dense-exponents.md). All the calls together cost
\[
             A^{d-2}W\exp(O(H))=\exp((xc+o(1))V).
\]
Even the extra scan over all possible values of each next coefficient is absorbed because \(W=\exp(O(H))\). The remaining variable polynomial degree never exceeds \(d-2\).

Let \(v=xc\). Then \(x>1/v\) and \(b(c-b)\le c^2/4\) give \(v^2>4(vx^2+x)/3>8/(3v)\). Conversely for any fixed \(v>(8/3)^{1/3}\) close to this limit, take \(x>1/v\) sufficiently close to \(1/v\), \(c\) close to \(v/x\), and \(b<c/2\) sufficiently close to \(c/2\). All strict inequalities in (1) hold with arbitrarily small rational adjustments. Interleave fixed rational schedules with a positive simulation share for each and verify each output, as in the [two-thirds construction](cogentic-deterministic-two-thirds.md). Its integer guards and polylogarithmic simulation overhead preserve the limiting coefficient.

The [finite replay](../experiments/cogentic-projective-selection.py) checks 1,170 evaluations with fixed leading coefficients and 135 projected row-congruence cases, including residual linear forms. The 81 panel calculations agree with direct two-dimensional Gaussian sums to maximum absolute difference \(5.33\cdot10^{-14}\). Four strictly feasible rational schedules decrease to \(34669/25000\) in the final fixture.
