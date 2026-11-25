# Selecting the number of prime factors in Cogentic's smooth windows

This gives an independent proof of the smooth-window estimate needed for **deterministic complete factoring in \(L_N[2/3,O(1)]\) bit operations**. It keeps a single real part in Mellin inversion and selects the allowed degrees in an auxiliary polynomial. It uses the verified ordinary and Dirichlet Riemann hypotheses. The [parameter and Gram calculations](cogentic-deterministic-two-thirds.md) are shared with the [proof by contour displacement](cogentic-dirichlet-smooth-windows.md). [Pinned Cogentic paper, Lemmas 8.4 and 9.2](https://raw.githubusercontent.com/google-research/google-research/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=43) · [Verified analytic hypotheses](https://math.mit.edu/~drew/grh/)

Write \(L=\log N,t_0=\log L,D=(L/t_0)^{1/3}, H=Dt_0,V=DH\). Use the [fixed public schedule](cogentic-deterministic-two-thirds.md#fixed-parameters). In particular \(\log B=(1000+o(1))H,\ \log Y=(100001+o(1))V\), \(\log q\le(2+o(1))V\), and \(\log R\asymp H\) for the required Gaussian windows of center \(Y\), width \(S\) and relative reciprocal width \(R=Y/S\). Let \(\mathcal P\) consist of primes in \((\sqrt B,B]\) after the required \(O(L)\) deletions and removal of primes dividing \(q\). Put \(u=\log Y/\log B\). With positive saddle \(\alpha\) for this set, \(u\asymp D\), \(\lambda=(1-\alpha)\log B=\log u+\log\log u+O(1)\), and \(\varphi''(\alpha)\asymp u(\log B)^2\). These are Cogentic's ordinary positive-saddle estimates. The target of the argument is relative error \(O(e^{-50t_0^2})\), uniformly in the prescribed inputs.

## A polynomial in the factor count

For a character \(\chi\bmod q\) and \(s=\alpha+it\), put
\[
 P_\chi(z;s)=\prod_{p\in\mathcal P}(1+z\chi(p)p^{-s})
               =\sum_{j\ge0} e_{j,\chi}(s)z^j .
\]
Let \(j_0=\lfloor u/3\rfloor\). Every squarefree product in the support \(Y e^{-.31}\le n\le Ye^{.31}\) of the modified weight \(\widetilde W_{Y,S}\) contains at least \(j_0\) primes. In Mellin inversion on the whole vertical line we may therefore replace \(P_\chi(1;s)\) exactly by \(P_{\chi,\ge j_0}(s)=\sum_{j\ge j_0}e_{j,\chi}(s)\). This uses the compact support in the integer variable before restricting the frequency integral. For every \(t\) the truncated sum is bounded by \(F(\alpha)=\prod_{p\in\mathcal P}(1+p^{-\alpha})\) by absolute values.

For nonprincipal \(\chi\) and \(|t|\le R^2\), the GRH prime-sum bound gives
\[
 \left|\sum_{p\in\mathcal P}\chi(p)p^{-\alpha-it}\right|
          \ll B^{-1/100}.
\]
For the principal character and \(L^{30}\le |t|\le R^2\) the upper bound is \(O(B^{-1/100}+L^4/|t|)\). Indeed apply Cogentic Lemma 9.2(1), partial summation in \(\log p\), and fixed zero-free width \(\nu=1/8\). For an inducing primitive nonprincipal character take the Perron height \(h=B^{1/20}\). For the principal character take \(h=\min(B^{1/20},|t|/4)\), keeping its pole outside the local rectangle. The first Perron error is at most a fixed polynomial in \(L\) times \(B^{-1/32+o(1)}\) because the lower endpoint is \(\sqrt B\) and \(\alpha=1-o(1)\). The second is \(O(L^4/h)\), since \(B^{1-\alpha}=O(u\log(2u))\), \(\log q,\log(2+|t|),\log B=O(L)\), and \(u\log(2u)=o(L)\). Passing to the inducing character and deleting \(O(L)\) primes costs \(O(L B^{-\alpha/2})\). The elementary bound \(\sum_{p\in\mathcal P}p^{-2\alpha}\ll B^{-1/2+o(1)}\) holds uniformly. [Cogentic, Lemma 9.2(1)](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=45)

For nonprincipal characters use radius \(r=B^{1/400}\). For principal characters at the indicated high frequencies use \(r=\min(B^{1/400},|t|^{1/100})\). Uniformly on \(|z|=r\) the linear term in \(\log P_\chi\) has bounded modulus by the prime-sum estimate, and the remaining Taylor series is \(O(r^2\sum_p p^{-2\alpha})=o(1)\). Consequently \(|P_\chi(z;s)|\ll1\) and Cauchy's formula gives
\[
                  |P_{\chi,\ge j_0}(s)|\ll r^{-j_0}.
\]
At all large inputs \(j_0\ge u/4\), so the fixed-radius saving is at least \(Y^{-1/1600}\).

## Integration and the principal saddle

The absolute Mellin integral up to \(R^2\) has cost \(O(RY^{\alpha-1})\) by Lemma 8.4(iii). For the nonprincipal terms, even charging all \(\varphi(q)\) characters, the normalized cost after dividing by \(Y^{\alpha-1}\) is at most \(O(qRY^{-1/1600})\). Its logarithm is at most \(-(60+o(1))V\) for the displayed schedule. Beyond \(R^2\) the trivial bound \(F(\alpha)\) and Lemma 8.4(iv) give \(O(qF(\alpha)e^{-R^{.6}/2})\). Relative to \(I_{\rm pure}\asymp Y^{\alpha-1}F(\alpha)/\sqrt{\varphi''(\alpha)}\), the latter tail and the fixed-radius term are both \(o(e^{-50t_0^2})\).

For the principal character, compare the low-frequency truncated polynomial with the full positive Euler product. Give each prime an independent Bernoulli variable of mean \(p^{-\alpha}/(1+p^{-\alpha})\), and write \(K\) for their sum. The saddle equation gives \(\mathbb E K\ge u\), because each \(\log p\le\log B\). Then
\[
 \Pr(K<j_0)\le 2^{u/3}\mathbb E 2^{-K}
       \le\exp(-[1/2-(\log2)/3]u).
\]
Thus the omitted low-degree terms have total absolute weight at most \(F(\alpha)e^{-cu}\), uniformly in \(t\). On \(|t|\le L^{30}\) the modified Gaussian transform has pointwise bound \(O(Y^{\alpha-1})\) by positivity and direct integration. Reinstating the full product on this finite segment costs \(O(L^{30}Y^{\alpha-1}F(\alpha)e^{-cu})\).

For \(|t|\le1/\log B\), the Mellin factor equals \(Y^{\alpha-1+it}(1+O(R^{-2}))\), with bounded absolute saddle mass relative to \(I_{\rm pure}\). For \(1/\log B\le|t|\le L^{30}\), the prime-band resonance estimate on page 47 gives \(|P_{\chi_0}(1;\alpha+it)|\le F(\alpha)\exp(-c u/\lambda^2)\). This range lies inside the source's low-frequency range \(|t|\log B\le L^{50}\); only a polynomial length and the pointwise Mellin majorant enter. Finally, on \(L^{30}\le|t|\le R^2\) use the marked polynomial and the pointwise majorant again. The integral of its bound is
\[
 \int_{L^{30}}^{R^2}\min(B^{1/400},t^{1/100})^{-j_0}\,dt
 \le R^2Y^{-1/1600}+O((L^{30})^{1-j_0/100}).
\]
After restoring \(Y^{\alpha-1}\) all these errors are \(o(I_{\rm pure} e^{-50t_0^2})\), since \(u/\lambda^2\gg t_0^3\). The far principal tail uses the same trivial estimate as above. Replacing \(\widetilde W\) by the original Gaussian has error \(O(Re^{-cR^2})\) after progression normalization by Cogentic Lemma 8.4(i), which also lies below this tolerance.

Character orthogonality now gives, for each unit residue \(r\bmod q\),
\[
 q\sum_{\substack{n\equiv r\bmod q\\n\ {\rm squarefree},\ p\mid n\Rightarrow p\in\mathcal P}}
             W_{Y,S}(n)
   =\frac q{\varphi(q)}I_{\rm pure}
        (1+O(e^{-50t_0^2})).
\]
The positive-saddle, one- and two-prime ratios remain those of Cogentic Lemma 9.2(2). This supplies the [complete factoring proof](cogentic-deterministic-two-thirds.md#all-required-progression-estimates) with the same public constants and bit model. The selection by the number of primes accounts for cancellation from the many factors of every supported integer.

The replay forms the factor-count polynomial by elementary symmetric recurrence and by complete enumeration, verifies the lower support in degrees, the low-degree positive bound, and a finite Cauchy coefficient bound via exact rational Parseval. [Integer and rational replay](../experiments/cogentic-marked-smooth-windows.py)
