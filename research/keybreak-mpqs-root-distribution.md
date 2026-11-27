# Residue distribution for planted MPQS roots

Randomizing the known split factors of the MPQS coefficient gives a local distribution theorem for one fixed input under Dirichlet GRH. Put \(n=\log N\), \(D=(n/\log n)^{1/3}\), and \(H=D\log n\). For any fixed positive \(B,K\), one can sample a factored squarefree \(A\asymp\sqrt N\) so that, except with probability \(O(e^{-KDH})\) over \(A\), the uniform CRT roots of \(N\) have the expected conditional residues simultaneously modulo every \(q\le e^{BDH}\), to absolute error \(O(e^{-KDH})\) per residue. The estimate also holds with an interval restriction on the integer lift. This covers fixed products of private \(Y_0=e^{O(DH)}\)-scale primes and more products of terminal \(e^{O(H)}\)-scale primes. The remaining smoothness question concerns the full integer quotient.

## A bias in an arbitrary fixed coefficient

Let \(q\) be a large odd prime. Take an even number \(k\) of distinct primes \(p_j\) in \((q,q(1+1/(100k)))\), and write \(A=\prod_j p_j\). Prescribe \(N\equiv(qA/p_j)^2\pmod {p_j}\) and \(N\equiv A^2\pmod q\). Choose a solution within \(O(Aq)\) of \(A^2\). The same construction allows \(N\) odd with \(v_3(N)=1\) by adding congruences modulo 2 and 9, since the other moduli are coprime to 6. For the lift window of length \(A\) centered near \(\sqrt N\), the uniform roots have the representation
\[
h=A+\sum_j\varepsilon_j(q-p_j)A/p_j,
\qquad \varepsilon_j\in\{-1,1\}\ \text{independent}.
\]
Indeed \(|h-A|\le A/100\), \(\sqrt N=A+O(q)\), and the residues are exactly the independently chosen local signs. Modulo \(q\) this is \(A(1-\sum_j\varepsilon_j)\). Thus the quotient \(u=(h^2-N)/A\) obeys
\[
\Pr(q\mid u)\ge 2^{-k}\binom{k}{k/2}\asymp k^{-1/2}.
\]
This is exponentially larger than \(2/q\) for the scales here. For example, \(k\asymp(\log q/\log\log q)^{1/2}\) gives \(\log q\asymp DH\), and \(k\asymp(\log q/\log\log q)^2\) gives \(\log q\asymp H\). Under RH the prime number theorem supplies more than \(k\) primes in the stated window for either choice. This construction rules out a uniform estimate based only on the split condition and the number of signs.

The aggregate CRT equidistribution theorem of Kowalski and Soundararajan concerns the discrepancy of the archimedean fractions \(h/A\), averaged over the planting modulus \(A\). Its Assumption 1.1 requires positive weighted prime support, and its restriction to a specified number of prime factors in Theorem 1.6 also needs the stated harmonic density and range for that number. Duke, Friedlander, and Iwaniec vary the prime modulus for a fixed polynomial. The short-interval root theorem for modular square roots of primes varies the prime radicand and averages over prime moduli. The incidence here instead fixes the radicand, samples an explicit product law for \(A\), and asks for residues of the integer lift at an external modulus. [Kowalski–Soundararajan, Theorems 1.2 and 1.6](https://people.math.ethz.ch/~kowalski/crt-sets.pdf) · [Duke–Friedlander–Iwaniec](https://annals.math.princeton.edu/1995/141-2/p08) · [Modular square roots of primes, Theorem 1.1](https://link.springer.com/article/10.1007/s00209-024-03436-5)

## Sampling the coefficient and mixing its CRT multipliers

Assume \(N\) is a fixed positive odd nonsquare. A split prime here is odd, coprime to \(N\), and satisfies \((N/p)=1\). Fix \(m=\lceil M DH\rceil\) distinct split primes \(p_j\in(2n^{12},3n^{12}]\), where the constant \(M\) will depend on \(B,K\), and put \(U=\prod_jp_j\). Thus \(\log U=O(DH\log n)=o(n)\). Put
\[
L=\left\lfloor\frac{\log(\sqrt N/U)}{12\log n}\right\rfloor,
\qquad X=(\sqrt N/U)^{1/L}.
\]
Then \(L\sim n/(24\log n)\) and \(X=(1+o(1))n^{12}\). Choose \(L\) split primes from \([X,X(1+1/(100L))]\) uniformly without replacement. With \(V\) their product, set \(A=UV\). The two sampling regions are disjoint, and \(\sqrt N\le A\le e^{1/100}\sqrt N\) up to harmless integer endpoints. An implementation may round \(X\) using the comparison \(U^2X^{2L}\le N\). Enumerating the prime candidate intervals, testing the split condition, and sampling the resulting lists all cost polynomially many operations in \(n\).

The uniform GRH input for a character \(\chi\bmod m_0\) is the prime sum bound \(\sum_{p\le x}\chi(p)\log p=\mathbf1_{\chi=1}x+O(\sqrt x\log^2(2m_0x))\). The modulus may exceed \(x\). One way to obtain this form is to take the forward difference of the integrated explicit formula at increment \(\sqrt x\). The GRH zero terms up to height \(\sqrt x\) contribute \(O(\sqrt x\sum_{|\gamma|\le\sqrt x}1/|\rho|)\), and the higher terms contribute \(O(x\sum_{|\gamma|>\sqrt x}|\gamma|^{-2})\). The uniform Dirichlet zero count gives the displayed logarithmic allowance. For the nonprincipal origin term, the functional equation reduces the conductor-dependent constant to \(O(\log(2m_0)+|L'/L(1,\overline\chi)|)\) for the primitive character. Comparing the partial fractions at 1 and 2 bounds the logarithmic derivative at 1 by \(O(\log(2m_0))\) under GRH, since the differences sum with weight \(O((1+\gamma^2)^{-1})\). The integrated remainder and the unsmoothing endpoint then contribute at most the same allowance. Removing prime powers and the primes excluded by induction from a smaller conductor also fits the error. [Lee, §2 and the integrated explicit formula in §4](https://arxiv.org/pdf/2301.13457)

For nonprincipal \(\chi\bmod U\), the quadratic splitting filter averages the sums for \(\chi\) and \(\chi\chi_N\), where \(\chi_N\) is the quadratic character attached to the squarefree part of \(N\). Both are nonprincipal because their possible nontrivial conductors lie in coprime factors of \(4NU\). Deleting primes dividing \(2N\) contributes only polynomial logarithmic error. Partial summation on the short sampling interval gives, for one uniformly chosen split prime \(\ell\),
\[
|\mathbb E\chi(\ell)|\ll \frac{\sqrt X\log^2(2NUX)}{X/L}=n^{-3+o(1)}.
\]
The principal estimate gives \(\asymp X/(L\log X)\) split primes in that interval and ample primes for \(U\). With replacement, the residue of the product \(V\) modulo \(U\) therefore differs from uniform on \((\mathbb Z/U\mathbb Z)^\times\) in total variation by at most
\[
\tfrac12\sqrt{\phi(U)}\,(n^{-3+o(1)})^L=\exp(-\Omega(n)).
\]
This follows by finite Fourier expansion and Cauchy–Schwarz. The probability of a repeated prime among the independent samples is \(o(1)\). The actual without-replacement law is the independent law conditioned on no repetition. Below, nonnegative expectations are bounded before conditioning and then divided by this acceptance probability, avoiding an additive collision error.

## Completing an external congruence

For fixed accepted \(A\), let \(h\) be uniform on the CRT roots lifted into a window \(J\) of \(A\) consecutive integers. Write \(e_q(x)=e^{2\pi ix/q}\). With a local square root \(b_p\) fixed at each prime factor of \(A\), the root measure modulo \(A\) has transform
\[
\widehat\mu_A(k)=\prod_{p\mid A}\cos(2\pi k b_p(A/p)^{-1}/p).
\]
The inverses in the argument are modulo \(p\). Let \(I\subseteq J\) be any integer subinterval. Expand the function \(\mathbf1_I(h)e_q(ah)\) in frequencies \(k\bmod A\). If \(d\) is the centered representative of \(qk-aA\bmod qA\), its coefficient has modulus \(O(\min(1,q/|d|))\) for \(d\ne0\), by the geometric sum. If \(d=0\), the coefficient is exactly \(|I|/A\). The estimate for \(d\ne0\) is independent of \(I\), its starting point, and \(a\).

For \(p\mid U\) with \(p\nmid q\), the phase of the \(p\)-factor is proportional to \(q^{-1}d V^{-1}\bmod p\), since \(qk\equiv d\pmod p\). Under uniform \(V\bmod U\), the retained phases are independent, and their mean absolute cosines are at most \(\gamma=0.7\) whenever \(p\nmid d\). This constant follows from the Riemann sum over the nonzero residues, with limit \(2/\pi\). If \(p\mid d\), use 1. Drop all other prime factors from the absolute product. With \(U'=U/(U,q)\), \(m_q=\omega(U')\), and \(\epsilon=\exp(-\Omega(n))\), the mean of this upper bound at each fixed nonzero \(d\) is at most
\[
\gamma^{m_q}\sum_{e\mid(U',d)}(\gamma^{-1}-1)^{\omega(e)}+O(\epsilon).
\]
Here \(d\) can be summed over all nonzero integers of magnitude at most \(qA_{\max}/2\), where \(A_{\max}=2\sqrt N\). This removes the congruence restriction \(d\equiv-aA\pmod q\) before averaging over \(V\). The resulting bound is an envelope independent of \(a\) and \(I\), even though the original frequency \(k\) can depend on \(V\). Using \(\min(1,q/|d|)\le q/|d|\), the sum over multiples of \(e\) contributes \(O((q/e)\log(2qA_{\max}))\). Consequently the expected envelope is
\[
O\left(q\log(2qA_{\max})\left[\gamma^{m_q}\prod_{p\mid U'}\left(1+\frac{\gamma^{-1}-1}{p}\right)+\epsilon\right]\right).
\]
The product is \(1+o(1)\). For \(q\le Q=e^{BDH}\), the number of discarded primes of \(U\) is at most \(\log Q/\log(2n^{12})=o(m)\). After the no-collision conditioning, Markov's inequality and a union over \(q\le Q\) show that every envelope is at most \(\tau=e^{-KDH}\), except with probability \(O(e^{-KDH})\), by taking \(M|\log\gamma|>2B+2K+1\). The factor \(Q^2\) in this union comes from summing \(q\) over the moduli. Sampling only requires the split-prime lists. More generally, the same argument permits \(\log Q+\log(1/\tau)=o(n/\log n)\) by taking \(m\) a sufficiently large multiple of \(\log Q+\log(1/\tau)+\log n\).

## Incidences and character moments

Write \(g=(q,A)\) and \(\mu_g\) for the uniform root law of \(N\) modulo \(g\). An exact frequency \(d=0\) exists precisely for \(a\) divisible by \(q/g\), and its CRT expectation is the transform of \(\mu_g\) at that frequency. Inverting the external additive transform gives, on the same good event for \(A\),
\[
\Pr(h\in I,\ h\equiv b\pmod q)
=\frac{|I|}{A}\frac{g}{q}\mu_g(b\bmod g)+O(\tau).
\]
This includes \(q=1\), which gives the unconditional interval mass. For \(q\) coprime to \(A\) the main term is uniform modulo \(q\).

For \(d\) coprime to \(N\), take \(q=d\gcd(d,A)\). Since \(A\) is squarefree, \(d\mid u\) is equivalent to \(h^2\equiv N\pmod q\), in addition to the planted root condition. Write \(\rho_N(s)\) for the number of roots modulo \(s\). Hensel lifting at the odd planted primes gives \(\rho_N(q)=\rho_N(d)\), so whenever \(q\le Q\),
\[
\Pr(h\in I,\ d\mid u)
=\frac{|I|}{A}\frac{\rho_N(d)}{d\rho_N(\gcd(d,A))}+O(\rho_N(d)\tau).
\]
For a single external split prime \(p\) this gives \(2/p\) when \(I=J\). At a planted prime the main term is \(1/p\). The main term vanishes at external inert primes. Taking \(K\) larger than the upper scale for the modulus and the interval losses makes the error relative on the intended incidences. The range \(q\le Q\) admits a fixed number of factors at the private scale and order \(D\) factors of bounded terminal scale when they are coprime to \(A\).

For an arbitrary bounded test of \(u\bmod d\), sum the residue formula at modulus \(q=d\gcd(d,A)\). Its absolute error is \(O(q\tau)\) times the sup norm of the test. The reference law is a product across the primes of \(d\). At a planted odd prime \(p\), write the lift of a fixed local root as \(b+pt\). The difference between two resulting quotient residues is \((t-t')(2b+p(t+t'))/(A/p)\), with a unit second factor. Thus \(u\) is uniform modulo \(p^j\) in this reference law. At an external prime \(p\nmid 2AN\), the Legendre moment has mean \(-\left(\frac{A^{-1}}p\right)/p\). Indeed the equation \(z^2=x^2-N\pmod p\) has \(p-1\) pairs, parametrized by the nonzero first factor of \((x-z)(x+z)=N\). Thus products of these local moments, and centered moments with controlled moduli and weights, follow from the same simultaneous residue estimate.

## From local distributions to smoothness

Take the lift window centered near \(\sqrt N\). Then \(h+\sqrt N\asymp\sqrt N\) and \(A\asymp\sqrt N\), so \(|u|\asymp |h-\sqrt N|\). The interval estimate gives \(\Pr(|u|\le Z)\ll Z/\sqrt N+\tau\) for \(Z\le \sqrt N\). In particular, forcing \(|u|\le e^{O(DH)}\) by independent sign samples is exponentially rare on the \(DH\) scale in this construction. The ordinary quotient scale remains \(N^{1/2+o(1)}\).

The local law also gives a smoothness upper bound at the terminal cutoff. Fix \(b>0\), take \(y=e^{bH}\) and \(T=e^{BDH}\), and use the simultaneous estimate through \(Q=T^2\), with \(\tau=e^{-3BDH}\). Restrict to quotients coprime to \(N\). In the centered window, any nonunit quotient instead gives a proper gcd with \(N\), since \(0<|u|<N\) eventually. If \(|u|\ge T/y\) is \(y\)-smooth, multiply its prime factors one at a time until the product first reaches \(T/y\). This supplies a smooth divisor \(d\in[T/y,T]\), so its query modulus \(d\gcd(d,A)\) lies in range.

For \((d,N)=1\), every odd prime power has at most two roots and powers of 2 have at most four. Thus \(\rho_N(d)\le4\cdot 2^{\omega(d)}\). The summed incidence error is \(O(T^2\tau)\), even using just \(\rho_N(d)\le d\). The main term of the union bound is controlled by Rankin's inequality with \(\sigma=(\log D)/(2\log y)\):
\[
\begin{aligned}
\sum_{\substack{T/y\le d\le T\\P^+(d)\le y}}\frac{2^{\omega(d)}}{d}
&\le (T/y)^{-\sigma}\prod_{p\le y}\left(1+2\sum_{j\ge1}p^{-j(1-\sigma)}\right)\\
&\le \exp\left(-\sigma\log(T/y)+O(\sqrt D\log\log y)\right)\\
&=\exp\left(-\left(\frac{B}{6b}+o(1)\right)H\right).
\end{aligned}
\]
The product bound uses \(p^\sigma\le y^\sigma=\sqrt D\) and the prime harmonic sum. The constant \(1/6\) uses \(\log D/\log n\to1/3\). Smaller quotients have probability \(O(T/\sqrt N+\tau)\) by the interval bound. The probability that the sampled coefficient fails the simultaneous estimate fits the same error allowance. This proves arbitrarily large fixed exponential saving on the \(H\) scale by increasing \(B\) in the sampler. In one growing-parameter sampler, take \(B=\sqrt D\). Then \(\log Q+\log(1/\tau)=5D^{3/2}H=o(n/\log n)\) and the upper bound becomes \(\exp(-\Omega(\sqrt D H))\).

The private cutoff \(e^{bDH}\) is a different regime. The ordinary Dickman comparison there gives an \(H\)-scale loss for unrestricted integers of size \(N^{1/2+o(1)}\), while the Rankin argument above at that larger cutoff has only \(\log T/\log y=B/b\) in its loss parameter. A lower bound for fully smooth values at the private cutoff still requires a global smoothness input for the CRT-root sample. A cheaper single-input schedule would also need a way to use those values, reduce the quotient height, or exploit useful partial relations.
