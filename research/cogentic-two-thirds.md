# A two-thirds exponent for deterministic integer factoring

Modifying the parameter schedule in Cogentic's deterministic paper gives one algorithm for the **complete factorization of every integer** \(N\ge2\) with bit cost
\[
   \exp\!\left(O\!\left((\log N)^{2/3}(\log\log(3N))^4\right)\right).
\]
The constants are effective and absolute. This is a deduction from the paper's preconditioned polynomial construction, smooth-relation estimates and order extractor. The original Theorem 1.1 gives \(O(\exp(3(\log N)^{3/4}))\) for a proper divisor. Our [fixed-power audit](cogentic-parameter-retuning.md) uses the same lemmas with smaller changes and yields exponent \(18/25\). [Pinned Cogentic paper, §§7–11](https://raw.githubusercontent.com/google-research/google-research/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf) · [Published theorem and release status](https://raw.githubusercontent.com/google-research/google-research/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/README.md)

## Public integer parameters

For the proof put \(L=\log N,\ X=L^{1/3},\ t=\log L\), using the large-input range. Compute \(L_0\) as in §8.2, an integer within a bounded distance of \(L\). Take \(x=\lfloor L_0^{1/3}\rfloor\) and \(v=\max(2,\lceil\log_2(2L_0)\rceil)\). For a positive rational \(a/b\) define \(v_{a/b}=\lfloor(v^a)^{1/b}\rfloor\) by integer root extraction. The following choices use only integer arithmetic:
\[
\begin{aligned}
 d=z_0&=\max(1,\lfloor x/v_{3/4}\rfloor),&
 m&=\lceil N^{1/d}\rceil,\\
 \log_2 B &=x v_{3/2},&
 \log_2 K_1&=xv_{3/8},&
 -\log_2 w&=xv_{1/3},\\
 \log_2 A&=xv^4,&
 \log_2 U&=x^2v^4.
\end{aligned}
\]
Use the source's definitions of \(S_0=UA,S_1=U\), the integer-centered parameter rectangle, the factor base, and \(\Delta_{\rm close}=AK_1^{-1/2}\). Wherever the order algorithm uses the integer exponents that define \(B,K_1\), it now uses the displayed \(\log_2 B,\log_2 K_1\). In particular the integer index guard uses \(\log_2 B\) in its generator-count test and denominator. Replace its upper bound \(2^{e(N;13,20)}\) on the output bit length by \(2^{x^2}\). The same small-input and guard-failure trial-division exits handle bounded inputs.

The following asymptotic sizes will also specify the analytical constants independently of rounding:
\[
\begin{array}{c|c@{\qquad}c|c}
d&\asymp Xt^{-3/4}&\log m&\asymp X^2t^{3/4}\\
\log B&\asymp Xt^{3/2}&\log K_1&\asymp Xt^{3/8}\\
\log(1/w)&\asymp Xt^{1/3}&\log A&\asymp Xt^4\\
\log U&\asymp X^2t^4&d\log A&\asymp X^2t^{13/4}.
\end{array}
\]
In particular \(d\log A=o(\log U)\), \(\log m=o(\log U)\) and \(\log A=o(\log m)\). The coefficient sandwich of §8.2 gives \(\log X_{\rm sc}\sim\log U,\ \log c_d\sim\log U\), \(4P_0B<c_d\), and \(2X_{\rm sc}<2^{L_0}\). Its smoothness parameter and saddle distortion satisfy
\[
 u=\frac{\log X_{\rm sc}}{\log B}\asymp Xt^{5/2},\qquad
 u_Y\asymp u,\qquad \lambda_Y=(1-\alpha_Y)\log B\asymp t
\]
over the ranges of Lemma 9.2. All subsequent estimates use natural logarithms.

## Parameter transfer, pages 37–46

**Base polynomials and root brackets.** Lemma 8.1 applies directly. The root error estimate in Lemma 8.2(3) uses \(dA^{d-1}=o(\bar u_0)\) and the coefficient sandwich, which continue to give supremum error \(\le K_1^{-1}\). The evaluations at the brackets have the required alternating signs since \(\log K_1\gg d\). Off the roots the loss from the product of distances to the prescribed roots is \(O(\log(1/w)+d\log d)=O(Xt^{1/3})\), and \(\log(1/w)=o(\log K_1)\). The derivative and Gaussian ratios on page 41 retain all the stated fixed powers of \(K_1\). In particular \(\log(\mu_i(a)/X_{\rm sc})=O(Xt^{1/3})=o(\log B)\), sufficient for the single- and double-prime saddle differences on page 46. The local \(\omega(|f_i(a)|)\le 2.1u\) bound continues to hold because each admissible prime exceeds \(B^{1/2}\).

**Brun counting.** In the proof of Lemma 8.2(2) take \(r_0=2\lfloor t\rfloor\) and \(z_{\rm Br}=\exp(t^2)\). In all the Brun, variance and peeling errors write \(J=t\log t\) in place of the original \(L^{.06}\log L\). Because \(\log c_d\ll L^{.76}\) and \(d>L^{.30}\), the same reciprocal-prime sum is bounded by \(1.1\) and the coprime density is bounded below by \(1/4\). The tail beyond the even Bonferroni truncation is at most \(\exp(-(4+o(1))J)\). Primes larger than \(z_{\rm Br}\) cost \(O(z_{\rm Br}^{-1/2})\). Each modulus is at most \(B^4 z_{\rm Br}^{2r_0}\) and there are at most \((2r_0+1)\omega(k_0k'_0)^{2r_0}=\exp(O(t^2))\) terms. Their combined logarithmic cost \(O(Xt^{3/2}+t^3)\) is \(o(\log(Aw))\), even on the subintervals of length \(\gg Aw\exp(-O(J))L^{-O(1)}\). This proves the published Brun estimate with \(\epsilon_{\rm Br}=\exp(-.10J)\), including its weighted arithmetic-progression form. Every fixed power of \(L\) is \(o(\exp(cJ))\) for every constant \(c>0\).

**Mellin and prime-sum parameters.** Lemmas 8.3, 8.4, and 9.1 have general scale hypotheses. In §9.2 set \(Q_{\max}=m^3\), \(T_*=2K_1^{3.5}\), retain \(D_{\rm SK,1}=\exp(c_{\rm LP}\log B/(800t))\) and \(\nu_1=400t/\log B\), and choose \(\nu_0=X^{-1}t^{-1/4}\). In particular
\[
 \log Q_{\max}\asymp X^2t^{3/4},\quad
 \log D_{\rm SK,1}\asymp Xt^{1/2},\quad
 \log T_*\asymp Xt^{3/8},\quad
 \nu_0\log B\asymp t^{5/4}.
\]
This gives \(\log(D_{\rm SK,1}(R_{\rm win}^2+2L^{10}+4))\le c_{\rm LP}/\nu_1\) as in Lemma 9.2. At \(\nu_0\), the Perron error term containing \(\exp(\lambda_Y/2)B^{-\nu_0/4}\) decays faster than any fixed negative power of \(L\), including after polynomial factors in that lemma. At \(\nu_1\) the proof retains the original power saving, since \(\nu_1\log B=400t\) and \(\lambda_Y=(1/3+o(1))t\). The squarefree saddle calculation is unchanged with \(u_Y\asymp Xt^{5/2}\) and \(\log B\asymp Xt^{3/2}\). Its expansion error is \(O(u_Y^{-2})\). The argument permitting removal of \(O(L)\) primes uses \(L B^{-.49}=o(1)\).

## Character sums and conditional moments, pages 46–53

Set \(D_{\rm damp}=Xt^{7/16}\). The low-frequency estimate in Lemma 9.2(3) gives an exponent \(\gg u_Y/\lambda_Y^2\asymp Xt^{1/2}\), including for the exceptional real character. The high-frequency part gives \(\gg u_Y\). Hence the error \(\exp(-cD_{\rm damp})\) absorbs fixed powers of \(R_{\rm win}\) and \(K_1\). It also absorbs factors of the form \(\exp(O(Xt^{1/4}))\), which occur in the conditional Rankin bounds below.

For Proposition 9.3(1), the logarithm of the Montgomery bound at the medium conductor scale \(B^{64}\) is \(O(\nu_0\log(B^{128}T_*)+\log L)=O(t^{5/4})\). At conductor scale \(Q_{\max}\) it is \(O(Xt^{1/2})\). Consequently the generating-prime count is \((1/2-o(1))B/\log B\). The two-block decomposition in Proposition 9.3(2) applies because \(\log(Q_{\max}^2B^2)=o(\log Y)\). Its nonexceptional Euler-product loss \(\exp(-.04u)\) dominates
\[
 B^2\,\exp\big(O((1-\alpha_Y)\log Q_{\max}+\log K_1)\big).
\]
Indeed \((1-\alpha_Y)\log Q_{\max}=O(Xt^{1/4})\) and \(u\asymp Xt^{5/2}\gg\log B\). This proves the clean progression estimate with relative error \(O(\exp(-cD_{\rm damp}))\). The exceptional character and principal character use the preceding low-frequency estimate. The unconditional zero-free and zero-density theorems in Cogentic's Proposition 7.1 suffice at these scales.

For Lemmas 9.4–9.5 the conditional moduli are at most \(m^{2+o(1)}\), by their formulas involving two factors \(|m-a|,|m-a'|\) and fixed powers of \(P_0,B,A\), so they lie below \(Q_{\max}\). The logarithms of \(\mu_i^{\rm ex}(a)B/(UA)\) and its two-point counterpart on page 51 are at most \((1+o(1))\log m\). Their Rankin distortion is \(O((\log m)t/\log B)=O(Xt^{1/4})\). Thus the 1-point and 2-point upper estimates of Lemma 9.5 use \(\exp(O(Xt^{1/4}))\) in place of \(\exp(O(L^{.34}L_2))\). For clean residue classes the new progression error dominates both the Rankin losses and any required fixed power of \(K_1^{-1}\). The exclusions of individual residue classes of probability \(O(B^{-.49})\) persist since \(Xt^{1/4}=o(\log B)\), and the number of prime divisors of \(a-a'\) above \(B^{1/2}\) is \(O(\log A/\log B)=O(t^{5/2})\).

For Proposition 10.1(1) the diagonal cost in the logarithm is
\[
 -\log(Aw)+O(\log B+u\log u+Xt^{1/4})\le -\tfrac12\log A.
\]
Here \(u\log u=O(Xt^{7/2})=o(\log A)\). For nearby distinct pairs \(\Delta_{\rm close}/(Aw)=K_1^{-1/2}/w\ll K_1^{-.49}\). For distant pairs, each error on pages 52–53 retains the original exponent when measured as a power of \(B\) or \(D_{\rm SK,1}\). In the medium-conductor case the sum-of-divisors bound has logarithm \(O(\sqrt{\log(B^{64})})\), which, together with \(O(t^{5/4}+Xt^{1/4})\), is \(o(\log D_{\rm SK,1})\). In the high-conductor case the logarithm is \(O(\sqrt{\log Q_{\max}})=O(Xt^{3/8})\), and the conductor count and Rankin distortion cost \(O(Xt^{1/2}+Xt^{1/4})=o(\log B)\). In either case \(Aw\) exceeds every fixed power of \(B\). These estimates account also for medium-prime rows subsequently dropped in the proof of Proposition 10.1(2). The estimate \(\mathrm{Var}(\widehat C)\ll1/z_0+K_1^{-.48}\ll L^{-.30}\) follows since \(z_0=d>L^{.30}\). Its centered distinct-pair estimate retains \(E_{\rm rel}=\exp(-.15J)\) from the squared Brun error and the stronger discarded-pair estimates.

## Spectral lower bound and complete factoring, pages 53–57

The Markov, Cauchy–Schwarz and peeling estimates on pages 53–54 use the numerical powers of \(E_{\rm rel}\), powers of \(B^{-1}\), and polynomial factors in \(L,d,u\). They retain their stated bounds with \(J=t\log t\) because \(J/\log L\to\infty\) and \(J=o(\log B)\). The vector norm in the positive-definite comparison is now
\[
 \|w_i\|^2\asymp u(\log B)^2\asymp X^3t^{11/2}.
\]
Consequently \(d/\max_i\|w_i\|^2\gg L^{-.81}\) and \(d/(\log X_{\rm sc})^2\gg L^{-1.20}\), giving \(\|v'\|^2\ge L^{-1.25}\) in the original two cases. The average-root matrix on page 55 has diagonal magnitude \(\asymp\log(1/w)\asymp Xt^{1/3}\) and off-diagonal Frobenius norm \(O(d\log L)=O(Xt^{1/4})\). In particular its least singular value is \(\gg\log(1/w)\). The subsequent quadratic form estimate therefore gives
\[
 \sum_a\pi_0(a)g_y(a)^2\gg d^{-1}(y_0^2+\|y_{\rm arch}\|^2).
\]
Indeed the mean square of the \(2d+1\) cell averages has this bound by the same differencing argument, using \((\log(1/w))^2/d\gg d\) to absorb the reference cell's squared coefficient norm \(O(d)\). Applying the coefficient \((128u)^{-1}\) gives a lower bound \(\gg1/(du)\gg L^{-.69}\) on the mean model for its unit vector. The \(O(u^{-1})\) perturbation of the two factor-base blocks in Lemma 9.2 is absorbed by their own positive diagonal term, as on page 55. The retained eigenvalue is at least \(L^{-3}\). This completes the parameter transfer in Proposition 10.1(2) and ensures the certified search finds a successful pair for each good generating prime.

With the modified \(B\), §11.1 gives \(\log K_{\rm idx}=O(\log B+(L/\log B)\log(6L))=O(X^2t^{-1/2})\). Thus \(\log_2\widetilde M\le 2^{x^2}\) for all sufficiently large inputs, including the contribution from the at most \(B\) exponents produced by Lemma 7.5. Trial division through \(K_{\rm idx}\), constructing this multiple, and calling Theorem 1.2(a) on it all have logarithmic cost \(O(X^2)\). In particular they are below the cost of perturbation enumeration. There are at most \(16 B L_0^8U^4A^2\) calls, each with logarithmic bit cost \(O(\log A+\log B+\log L)=O(Xt^4)\). Repeated-prime inputs satisfy the same subgroup-index argument. All trial-division fallbacks caused by a failing guard lie below an effective absolute threshold by the preceding estimates. This proves the uniform proper-divisor bound. AKS tests for primes and verified recursive splitting take at most \(2\log_2 N\) nodes for a complete factorization. [Cogentic's order extraction and final reduction, Lemma 7.5 and §11](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf)

The checks compare determining powers of \(X,t\) as exact rational pairs and also check the original finite subgroup-index examples. They verify the inequalities used in the parameter transfer. The analytic and spectral results invoked here are paper proofs. [Integer and rational replay](../experiments/cogentic-parameter-retuning.py)
