# Direct sampling of reduced classes with factored leading coefficients

For odd \(N>1\), the proposal below samples the primitive proper form classes of discriminant \(\Delta=-4N\) whose canonical reduced representative has leading coefficient coprime to \(N\). Conditional on returning a form, its class is exactly uniform on that set and its leading coefficient is already factored. Under Dirichlet GRH, on the rough-input branch the omitted classes have fraction \(e^{-\omega(H)}\), and the proposal takes polynomial expected work in \(\log N\). [Reduced forms and the form-class group, Lenstra–Pomerance §2](https://cr.yp.to/bib/1992/lenstra.pdf#page=5) · [Rough-input prepass](keybreak-private-shape-work.md#ensuring-the-count-suffices-on-every-input)

## The equal-weight proposal

Write a form as \([A,2b,C]\). We use the convention \(-A<2b\le A\le C\), with \(2b\ge0\) if \(A=C\). There is one such primitive positive definite reduced form per proper class. The discriminant gives \(AC-b^2=N\), so the reduction inequalities imply \(3A^2\le4N\). Put \(U=\lfloor 2\sqrt{N/3}\rfloor\), let \(T=2^J\) be the least power of two at least \(U\), and use the following attempt. [Lenstra–Pomerance, reduced representatives in §2](https://cr.yp.to/bib/1992/lenstra.pdf#page=5)

1. Choose \(j\) uniformly in \(\{0,\ldots,J\}\). Draw independent uniform factored integers \(d\in[1,2^{j+1}]\) and \(e\in[1,T/2^j]\). Reject unless \(d\) is squarefree, \(2^j\le d<2^{j+1}\), and \(A=de\le U\). Each surviving ordered pair has mass \(1/(2T(J+1))\). Every squarefree divisor \(d\) of a given \(A\le U\) occurs once with its own \(j\), so \(A\) has mass \(2^{\omega(A)}/(2T(J+1))\). [Factored integer generation and dyadic divisor weighting](keybreak-factored-denominator-proposal.md)
2. Compute \(g=(A,N)\). If \(g>1\), reject or return the verified divisor \(g\). Since \(A\le U<N\), such a divisor is proper. Otherwise let \(R(A)=\#\{b\bmod A:b^2\equiv-N\pmod A\}\), including \(R(1)=1\). Compute the local root counts using the factorization of \(A\). At each odd prime power the unit root count is either zero or two, and when present the roots are obtained by Hensel lifting. At a power of 2 the odd-unit root count is at most four. The roots at 2 can be found by retaining the valid lifts at each step, with at most four retained residues. Hence \(R(A)\le2^{\omega(A)+1}\), including even \(A\).
3. Reject with the complement of probability \(R(A)/2^{\omega(A)+1}\). On success choose a uniform root modulo \(A\) by independent choices among the local roots and CRT, and use its representative \(-A/2<b\le A/2\). Compute \(C=(N+b^2)/A\) and keep the form exactly when it satisfies the canonical tie and reduction conditions and \(\gcd(A,2b,C)=1\). The primitive check also covers the possible common factor 2 when \(A\) is even.

Every root passing the final tests has the same unconditional mass
\[
\frac{2^{\omega(A)}}{2T(J+1)}\cdot\frac{R(A)}{2^{\omega(A)+1}}\cdot\frac1{R(A)}
=\frac1{4T(J+1)}.
\]
Conversely, each canonical reduced primitive form with \((A,N)=1\) determines exactly one accepted pair \((A,b\bmod A)\). Its weight holds regardless of whether gcd failures are rejected or treated as factor exits. Even coefficients are part of this law. [Kalai, uniform factored integer sampler](https://www.microsoft.com/en-us/research/publication/generating-random-factored-numbers-easily/)

## The missing fraction

Extend \(R\) multiplicatively to all \(A\). For each odd \(p\mid N\), put \(w=v_p(N)\). At modulus \(p^k\) with \(k\le w\), the root count is \(p^{\lfloor k/2\rfloor}\). For \(k>w\) it is zero if \(w\) is odd, and at most \(2p^{w/2}\) if \(w\) is even, by dividing out the forced power of \(p\) and using the unit root bound. Thus \(R(p)=1\) and
\[
S_p:=\sum_{k\ge1}\frac{R(p^k)}{p^k}
\le 2\sum_{k\ge1}p^{-\lceil k/2\rceil}=\frac4{p-1}.
\]
For \((m,N)=1\), the root bound \(R(m)\le2\cdot2^{\omega(m)}\) applies. Counting squarefree divisors gives \(\sum_{m\le X}2^{\omega(m)}\le X(1+\log X)\) for \(X\ge1\). Write \(A=am\), where \(a\) is supported on the prime divisors of \(N\) and \((m,N)=1\). Summing over \(m\) first and then over \(a\) gives, for a specified \(p\mid N\),
\[
\sum_{\substack{A\le U\\p\mid A}}R(A)
\le 2U(1+\log U)S_p\prod_{q\mid N,\ q\ne p}(1+S_q).
\]
This bounds even the forms dropped before enforcing primitivity and the boundary convention. For all \(N\), the product is at most a power of \(\log(2N)\). Indeed its logarithm is \(O(\sum_{q\mid N}1/q)\), and splitting at \(\log(2N)\), then using the harmonic sum below that cutoff and \(\omega(N)\le\log_2 N\) above it, gives \(O(1+\log\log(2N))\). The union over \(p\mid N\) therefore bounds the excluded count by \(U(\log(2N))^{O(1)}/p_{\min}\), where \(p_{\min}\) is the least prime divisor of \(N\).

Write \(\Delta=f^2\Delta_0\) with fundamental \(\Delta_0\). The ring class number formula, followed by Littlewood's lower bound under Dirichlet GRH, gives
\[
h(\Delta)=\frac{w(\Delta)\sqrt{|\Delta|}}{2\pi}
 L(1,\chi_{\Delta_0})\prod_{q\mid f}\left(1-\frac{\chi_{\Delta_0}(q)}q\right)
\gg \frac{\sqrt{N}}{(\log(2N))^{O(1)}}.
\]
Here \(w(\Delta)\ge2\) counts units in the order. The conductor product is at least \(\prod_{q\mid f}(1-1/q)\), which is bounded below by an inverse power of \(\log(2N)\) by the same prime split. The class number argument applies to nonfundamental discriminants, so it includes repeated prime factors in \(N\). Therefore on the rough branch \(\log p_{\min}/H\to\infty\), the omitted fraction is at most \((\log(2N))^{O(1)}/p_{\min}=e^{-\omega(H)}\). A weaker separation \(p_{\min}\ge e^{bH}\) gives the corresponding \(e^{-(b-o(1))H}\) estimate. The total variation distance between the uniform full class law and its restriction to the coprime canonical representatives equals the omitted fraction. [Ring class number relation](https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/jlms.12744) · [Lamzouri–Li–Soundararajan, GRH bounds at \(s=1\)](https://arxiv.org/abs/1309.3595)

## Restarts, gcd exits, and caps

Each ideal attempt has the same per-form mass, and the form-return probability is inverse-polylogarithmic on the rough branch by the class number lower bound. Repeat independent attempts sequentially. For an attempt cap \(J_0\), the probability of returning any specified form is its one-attempt mass times \(\sum_{j=0}^{J_0-1}r^j\), where \(r\) is the probability of continuing after an attempt. When gcd exits end the procedure, \(r\) excludes those outcomes. Thus conditioning on a returned form preserves the exact law for any deterministic cap or for unbounded sequential sampling. The class count is needed for the analysis of work and distance, not for an acceptance test.

The one-attempt gcd exit probability is \(O(\sum_{p\mid N}1/p)\). Indeed for each such \(p\), \(2^{\omega(pm)}\le2\cdot2^{\omega(m)}\), so the weight of \(A\) divisible by \(p\) is at most \(U(1+\log U)/(pT(J+1))=O(1/p)\). On the rough branch a polynomial number of attempts therefore has only \(e^{-\omega(H)}\) probability of this exit. When it happens, it supplies a verified factor immediately.

For a bounded implementation, couple the factored integer draws and modular root routines to their exact versions, using polynomial work caps with total discrepancy \(O(N^{-K})\) for any fixed \(K\). A polynomial cap on the number of attempts is enough to make the probability of reaching it equally small. The exact probability of returning a form is at least its inverse-polylogarithmic one-attempt probability, even with immediate factor exits. Conditioning the coupling on form return therefore costs only another polylogarithmic factor. This treats the capped routines through a coupling, so the proof also allows their runtimes to depend on the sampled integer. [Coupling for capped exact draws](keybreak-factored-denominator-proposal.md)
