# Public MPQS rows on a single input

The multiple-polynomial quadratic sieve gives public square rows with a known smooth leading factor. Dirichlet GRH supplies enough small split primes to choose that leading factor and sample \(\Theta(\log N/\log\log N)\) independent root bits in polynomial bit work. Smoothness has the right leading exponential scale if the unfactored value is screened at the private top cutoff. Neither the split-prime count nor a fixed-leading-factor average proves smooth supply for the individual input after choosing the leading factor.

## Construction and trial cost

Write \(L=\log N\), \(D=(L/\log L)^{1/3}\), and \(H=D\log L\). Fix \(X=\exp((v+o(1))H)\) with \(v>0\). On a continuing odd nonsquare input the quadratic character of \(N\) is nonprincipal, with conductor at most \(4N\). For fixed \(K>4\), the usual Dirichlet GRH prime-count bound \(O(\sqrt x\log^2(4Nx))\) for Chebyshev sums at \(x=L^K\) gives \(\asymp L^K/\log L\) primes in \([L^K/2,L^K]\) that do not divide \(N\) and for which \(N\) is a square. Primes found to divide \(N\) give a proper split. Scanning the interval, finding roots by exhaustive search if desired, multiplying selected primes, and preparing CRT coefficients all cost polynomially many bit operations in \(L\).

Greedily multiply distinct split primes until the next would exceed \(\sqrt N/X\). The resulting odd squarefree \(A\) satisfies
\[
\frac{\sqrt N}{XL^K}<A\le \frac{\sqrt N}{X},
\qquad k=\omega(A)=(1+o(1))\frac{L}{2K\log L}.
\]
All its primes are below an ordinary terminal factor base of size \(\exp((b+o(1))H)\) for fixed \(b>0\). Choose \(k\) independent signs on the two roots at these primes and reconstruct \(B\bmod A\). Take the representative \(B\) nearest \(\sqrt N\), so \(|B-\sqrt N|\le A/2\), and let \(x=At+B\) for an integer \(|t|\le X\). Then
\[
u=\frac{x^2-N}{A}\in\mathbb Z,\qquad
|u|\ll \sqrt N(X+1),\qquad x^2\equiv A u\bmod N .
\]
The factor list of \(A\) is available from construction. If \(|u|\) is screened and fully factored at the source's private top cutoff, its primes can enter the existing descent only when the relevant good-parent and completion conditions hold. The signed rational identity itself is exact. A nonunit \(x\) or \(u\) is handled by a gcd, and the public modular square root is \(x\bmod N\).

For a top cutoff \(\log Y=(y+o(1))DH\), a value of the usual height \(\log |u|=L/2+O(H)\) has smoothness argument \((1/(2y)+o(1))D\). The Dickman log loss is \((1/(6y)+o(1))H\), the one-coordinate counterpart of the private two-coordinate anchor. At the much smaller terminal cutoff \(\log B=(b+o(1))H\), the loss instead is \((1/(3b)+o(1))DH\). These are density scales, apart from the averaged estimate below. Acquisition, recognition, descent and usable row rank must all be charged on an individual input for a factoring budget.

## Exact CRT law and a pointwise counterexample

For \(p\mid A\), let \(A_p=A/p\), choose one local root \(s_p\), and let \(c_p=s_p A_p^{-1}\bmod p\). The law of \(B/A\bmod1\) has exact Fourier coefficient
\[
 \widehat\mu(h)=\prod_{p\mid A}\cos(2\pi h c_p/p).
\]
Parseval gives \(A^{-1}\sum_{h\bmod A}|\widehat\mu(h)|^2=2^{-k}\). This average over frequencies does not bound the short-interval frequencies for the individual input.

In fact for any prescribed \(A\) built from primes of the stated size, impose the unit CRT conditions \(N\equiv A_p^2\bmod p\) for all \(p\mid A\). Then one may take \(c_p=1\), and all CRT roots \(B/A\) lie in an arc of radius \(\sum_{p\mid A}1/p=o(1)\) around zero modulo one. In particular \(\widehat\mu(1)=1-o(1)\). For any growing integer \(X\), choose \(N\) in the resulting class modulo \(A\) with \(\sqrt N/A\) within \(1/16\) of \(X+1/2\). The interval for \(N\) has length \(\asymp A^2X\), so it contains members of the class. Then every possible \(x=At+B\) is at distance at least \(A/4\) from \(\sqrt N\). The same conclusion holds for \(-\sqrt N\), because the root set is closed under sign. This prevents abnormally short \(u\) for this particular \(A\). The construction disproves a pointwise equidistribution argument based only on the split primes and the number of independent signs. It neither analyzes alternative choices of \(A\) for these inputs nor asserts a counterexample on the rough-input branch.

There is a universal but much weaker short-interval bound. For an interval of length \(T<A\), choose a subproduct \(A_0>T\) by multiplying prime factors until just past \(T\). Writing \(k_0=\omega(A_0)\), each root modulo \(A_0\) gives at most one integer representative in the interval, so its probability is at most \(2^{k_0-k}\). At \(T=A\exp(-cH)\), this gives at most \(\exp(-\Omega(H/\log L))\) for fixed \(c>0\), whereas uniform placement would give \(\exp(-cH)\). For the bound use \(A_0\le T L^K\) when \(T\ge1\), and \((k-k_0)K\log L\ge\log(A/A_0)\).

## Smooth values averaged over the input

Fix \(A\) and a dyad \(N\in[M,2M]\), where \(A\asymp \sqrt M\exp(-O(H))\), \(AX\ll\sqrt M\), and \(A\) has the above prime factors. Draw \(N\) uniformly among unit quadratic residues modulo \(A\) in this dyad, then draw a uniform CRT root. Here the scales are defined with \(L=\log M\). The number of equally weighted pairs \((N,B\bmod A)\) is \((1+O(A/M))M\varphi(A)/A\), since each of the \(\varphi(A)\) unit roots gives one congruence for \(N\). In this range \(\varphi(A)/A=1-o(1)\).

Fix an integer \(t\) and use centering as above. For each proposed \(x\), put \(x_0=x-At\); necessarily \(|x_0-\sqrt N|\le A/2\). The latter condition places \(u=(x^2-N)/A\) in an interval of length \(2x_0=O(\sqrt M)\). There are \(O(\sqrt M)\) choices of \(x\). Apply the source's short-interval smooth upper bound to each interval, padding its length to \(\Theta(\sqrt M)\) and taking the global value scale \(U_0\asymp\sqrt M(X+1)\). The loss from dilation is \(\exp(o(H))\) at the top cutoff: the bound has a factor of order \((C U_0Y/\sqrt M)^{1-\beta(U_0,Y)}\), where \(1-\beta=O(\log D/\log Y)\). Sign and intervals near zero are covered by the same prefix and dilation bounds. Each \((x,u)\) determines \(N\) and the CRT root uniquely. Therefore, uniformly for fixed \(|t|\le X\), the averaged probability of \(0<|u|\) being \(Y\)-smooth is at most
\[
\exp(-(1/(6y)+o(1))H).
\]
The same upper bound holds for \(t\) drawn independently of the input and root, and a union bound for success at any \(|t|\le X\) pays the \(X\)-scale factor. At the terminal cutoff the same argument gives the loss \((1/(3b)+o(1))DH\). [KeyBreak, Lemma B.7, (B.29), and (G.35)](https://crypto.sjtu.edu.cn/factoring.pdf#page=115)

At \(t=0\) the leading density bounds match from below for this averaged law. Take unit integers \(x\) in a fixed positive-length subinterval of \((\sqrt M,\sqrt{2M})\) staying a fixed multiple of \(\sqrt M\) from the ends. Choose \(0<u<c\sqrt M\) smooth, with \(c>0\) a sufficiently small absolute constant. Then \(N=x^2-Au\) lies in the dyad and \(x\) is its centered root since \(x-\sqrt N=Au/(x+\sqrt N)<A/2\). Counting unit \(x\) costs a factor \(1-o(1)\) by inclusion-exclusion, and the ordinary smooth prefix lower bound gives the stated leading density after division by \(M\varphi(A)/A\). The calculation averages over all the conditioned \(N\). It cannot be applied after selecting \(A\) as a function of the input, nor does it certify that the top factors are good descent labels.

## Limit on a shorter-height route

This separate bound allows \(A\) to depend arbitrarily on the input. For fixed \(K\), consider all \(N\in[M,2M]\), all \((\log M)^K\)-smooth \(A\le C\sqrt M\), and all integers \(x\) with \(N=x^2-Au\) and \(0<|u|\le M^\eta\), \(0\le\eta<1/(2K)\). Necessarily \(x=O(\sqrt M)\). Rankin bounds the number of candidate \(A\) by \(M^{(1-1/K)/2+o(1)}\): one can take the Rankin exponent \(1-1/K\), for which the logarithm of the Euler product for the primes through \((\log M)^K\) is \(O(\log M/\log\log M)\) by the prime counting bound and partial summation. Counting the triples \((x,A,u)\) therefore gives at most \(M^{1-1/(2K)+\eta+o(1)}\) possible inputs. For a subpower value bound on \(|u|\) the same estimate has \(\eta=0\) in the exponent. Thus dense-input coverage cannot rely on reducing the MPQS quotient to size \(\exp(O(DH))\) with polylogarithmically smooth \(A\), even granting free adaptive choice of \(A,x\).

The top-screened route does give a polynomial-cost source of proposals with the right *averaged* one-coordinate exponent. A positive single-input result needs a smoothness and good-parent estimate uniform over a viable leading-factor sampler, and a lower bound for the usable public row incidence after descent. Neither the exact CRT sign count nor the averaged Dickman estimate supplies these guarantees.
