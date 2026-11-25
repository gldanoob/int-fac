# Uniform squarefree smooth windows in the deterministic Cogentic construction

Let $L=\log N$, $z=\log L$, and write $L_N[2/3,C]$ for $\exp((C+o(1))L^{2/3}z^{1/3})$. The analytic result below treats squarefree products of primes in $(\sqrt B,B]$ in every reduced residue class. Its input is ordinary and Dirichlet RH. The companion note applies it to the two-field relation extractor and its deterministic search. [Alpöge’s November 20 theorem](https://alpo.ge/remark.pdf) · [Sutherland’s independent kernel checks and exact statements](https://math.mit.edu/~drew/grh/) · [Cogentic’s deterministic paper, §§8–10](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf)

## An individual character estimate

In this section assume $L^c\le\log B\le L^C$, and $\log(q+2),\log(2+|t|)\le L^C$, for fixed $0<c<C$. Let $J$ be the primes in $(\sqrt B,B]$ with at most $L^C$ deletions. For a Dirichlet character $\chi\bmod q$ put
$$
 F_\chi(s)=\prod_{p\in J}(1+\chi(p)p^{-s}),\qquad
 \delta=D_0\frac{\log L}{\log B}.
$$
Choose $D_0=D_0(C)$ sufficiently large. Uniformly on $1/2+\delta\le\sigma\le1$ one has
$$
 \log F_\chi(\sigma+it)
 =\mathbf1_{\chi=\chi_0}\int_{\sqrt B}^{B}\frac{v^{-\sigma-it}}{\log v}\,dv
   +O(L^{-10}).                                               \tag{1}
$$
Here the logarithm is the sum of the Taylor branches at each Euler factor. In particular every nonprincipal product is $1+O(L^{-10})$ on this entire segment, including characters induced from proper divisors of $q$.

For detail, pass first to the primitive character inducing $\chi$, allowing at most $O(L^C)$ more deleted factors. On $\Re w\ge1/2+\delta/2$, the logarithmic derivative of its $L$-function, with the pole at 1 subtracted in the principal case, is $O(\delta^{-2}\log^2(q(4+|\Im w|)))$. For example the partial-fraction expression for $L'/L$ sums the zeros with imaginary parts within 1 of $\Im w$ with remainder $O(\log(q(4+|\Im w|)))$ in $1/2\le\Re w\le2$. There are $O(\log(q(4+|\Im w|)))$ such zeros and their real parts are $1/2$. The bounded-height principal case follows after removing its pole. This is the usual effective explicit-formula input, also obtained from the disk argument in Cogentic Lemma 9.2(1) with a disk contained in $\Re w>1/2$. [Cogentic, Proposition 7.1 and Lemma 9.2](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=45)

Apply truncated Perron to the sum of $\Lambda(n)\chi(n)n^{-\sigma-it}$ for $x<n\le y$ with $\sqrt B\le x\le y\le B$, using half-integer endpoints and a height $H_0\in[B^3,2B^3]$ satisfying $\big||t|-H_0\big|\ge B^3/4$. This last choice keeps a potential principal pole away from the horizontal contours. The truncation error is $O(B^{1-\sigma}\log^2 B/H_0)$ by the harmonic sum of the inverse distances to a half-integer. Move the line from $1-\sigma+1/\log B$ to $1/2+\delta/2-\sigma$. Work with the difference of the endpoint powers so its quotient by the integration variable is regular at zero. The vertical error is $O(x^{-\delta/2}L^{O(C+1)})$, and the two horizontals cost $O(B^{1-\sigma}L^{O(C+1)}/H_0)$. In the principal case the pole gives $\int_x^y v^{-\sigma-it}\,dv$ up to the harmless endpoint errors. If the pole lies beyond the integration height, that integral is $O(B^{1-\sigma}/H_0)$ instead. Prime powers of exponent at least two contribute $O(x^{1/2-\sigma}L^{O(C+1)})$ by dyadic subdivision and $\sum_{p^k\le v,\ k\ge2}\log p\ll\sqrt v\log^2(2v)$. Partial summation removes the factor $\log p$. The half-integer endpoint replacement costs $O(x^{-\sigma}\log B)$, and the deleted primes change the sum by $O(L^CB^{-1/4})$. Finally the logarithm adds $O(\sum_{p>\sqrt B}p^{-2\sigma})=O(\delta^{-1}B^{-\delta})$. Since $x^{-\delta/2}\le L^{-D_0/4}$, enlarging $D_0$ proves (1).

## A Gaussian distribution in progressions

Use Cogentic's normalized Gaussian $W_{Y,S}(n)=S^{-1}\exp(-\pi(n-Y)^2/S^2)$, $R=Y/S$, and its compactly supported modification $\widetilde W$ from Lemmas 8.3–8.4. Put $J_q=\{p\in J:p\nmid q\}$, $F(s)=\prod_{p\in J_q}(1+p^{-s})$, and write $\alpha$ for the positive saddle solving $-(\log F)'(\alpha)=\log Y$. One may equally use the common saddle before deleting the $O(L^C)$ primes. All stated errors absorb that change. Let $u=\log Y/\log B$ and $\lambda=(1-\alpha)\log B$. Assume $L^c\le u\le L^C$, $L^c\le\log R\le L^C$, and $q\le S$. At an application of (1) choose the exponent in $D_0$ to allow $\log q\le\log Y\le L^{2C}$ and $\log(B^4R^2)=O(L^C)$. Set
$$
 I_{\rm pure}=\frac1{2\pi}\int_{|t|\le1/\log B}
                     Y^{\alpha-1+it}F(\alpha+it)\,dt .
$$
This integral is positive and $I_{\rm pure}\asymp Y^{\alpha-1}F(\alpha)/(\sqrt u\log B)$, uniformly in the deletions. The standard saddle calculation gives $\lambda=\log u+\log\log u+O(1)$ and $\log F(\alpha)=(1+o(1))u$. These statements follow directly from PNT on $(\sqrt B,B]$ and the small-$t$ expansion in Cogentic Lemmas 9.1(2), 9.2(2). Its relative $O(u^{-2})$ Edgeworth expansion and the associated one- and two-prime ratios also hold throughout these ranges. In the ratio at a reference scale $X$, the source uses $|\log(Y/X)|=O(\log B)$, a condition verified in the application. [Cogentic, pp. 43–47](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=43)

For every $r$ coprime to $q$, and squarefree $n$ composed of primes in $J$, the estimate is
$$
 q\sum_{n\equiv r\ (q)} W_{Y,S}(n)
 =\frac q{\phi(q)} I_{\rm pure}
  \left(1+O\!\left(R^{-2}+e^{-c_1 u/(\log(2u))^2}\right)\right)
 +O\!\left(qR Y^{-1/2+\delta}+
            Y^{-1/2+\delta} B^4R^2 e^{o(u)}
            + R e^{-c_1R^2}\right).                         \tag{2}
$$
The $o(u)$ is uniform as $L\to\infty$ for the specified fixed powers. The large second error is a convenient bound on the far principal contour. The expression uses the common saddle form $I_{\rm pure}$ also appearing in the extractor.

For a nonprincipal character Mellin-invert on the line $\sigma=1/2+\delta$. Up to $T=B^4R^2$ the Euler product is bounded by (1), and the Mellin transform has $L^1$ norm $O(RY^{\sigma-1})$ by Lemma 8.4(iii). For $|t|>T$ the proof of its part (iv) gives $|\widetilde M(\sigma+it)|\ll Y^{\sigma-1}\exp(-c(|t|/R)^{2/3})$. Even the trivial $|F_\chi|\le\exp(O(\sqrt B))$ suffices there. Orthogonality costs at most $q$ on these absolute errors. Truncating the Gaussian in the progression costs $O(R e^{-cR^2})$ by Lemma 8.4(i).

For the principal character, retain the saddle through $|t|\le1$. Over $|t|\le1/\log B$, Lemma 8.4(ii) approximates the Mellin transform by $Y^{\alpha-1+it}(1+O(R^{-2}))$. The absolute integral there is $O(I_{\rm pure})$ by the same Gaussian saddle majorant. On $1/\log B\le |t|\le1$, the interval of primes with $\log p/\log B\in[1-1/\lambda,1]$ gives $|F(\alpha+it)|\le F(\alpha)\exp(-c u/\lambda^2)$. Indeed PNT replaces the sum of $p^{-\alpha}(1-\cos(t\log p))$ by the corresponding integral with negligible error, and the integral of $1-\cos$ on this band is $\gg e^\lambda/\lambda^3$, uniformly even when $t\log B$ nearly resonates. This is the small-frequency argument in the proof of Lemma 9.2(3). The bounded length of this segment absorbs $\sqrt u\log B$ after slightly reducing $c$. Pointwise $|\widetilde M(\sigma+it)|\ll Y^{\sigma-1}$ follows from positivity and change of variable $v=\log(x/Y)$.

For $1\le |t|\le T$ bend the principal contour to
$$
       \sigma(t)=\max\!\left(\frac12+\delta,                   \alpha-\frac{\log |t|}{\log B}\right).
$$
It joins the saddle at $t=\pm1$, and $|\sigma'(t)|\le1/(|t|\log B)$ away from its two corners. The product is entire. The Mellin transform of the modified Gaussian is entire and its endpoint horizontal integrals at $\pm T$ are negligible by the bound just used for the far tail, uniformly in $\sigma$. Integrating by parts in (1) on this contour gives
$$
 \log |F(\sigma+it)|\ll \frac{B^{1-\sigma}}{|t|\log B}+L^{-10}
                 \ll \frac{e^\lambda}{\log B}+L^{-10}=o(u).
$$
The curved portion contributes $O(Y^{\alpha-1}e^{o(u)}\int_1^\infty t^{-u}\,dt)$, hence $O(e^{-c u}I_{\rm pure})$. The part on the vertical line contributes $O(T Y^{-1/2+\delta}e^{o(u)})$. For a principal character the orthogonality prefactor $q/\phi(q)\ll\log\log(3q)$ is absorbed in $e^{o(u)}$. This proves (2). It permits $\log R\gg u$ because the high-frequency integral gains $t^{-u}$ before reaching the vertical line.

## Literature and scope

Younis shifts a Perron contour left of the saddle for ordinary smooth integers in short intervals and obtains asymptotics under RH with $h\ge x^{1/2+\epsilon}$. Soundararajan and Harper study uniform reduced-class distribution at moduli bounded by powers of the smoothness bound. The progression in (2) is individual, carries a lower cutoff on every prime factor, allows squarefree support and deletions, and retains the saddle expression used by Cogentic. This proof adapts standard contour methods to this combination. Pascadi's distribution exponent above $1/2$ concerns an average over moduli. None of these comparisons establishes priority for a general square-root-contour argument. [Younis, Theorem 1.1](https://arxiv.org/abs/2409.05761) · [Soundararajan](https://arxiv.org/abs/0707.0299) · [Harper](https://arxiv.org/abs/1103.2106) · [Pascadi](https://www.cambridge.org/core/journals/compositio-mathematica/article/smooth-numbers-in-arithmetic-progressions-to-large-moduli/D8E4EE07BDAA6D41CCD8C5455D81CD7A)

The [finite replay](../experiments/cogentic-smooth-windows.py) checks 300 squarefree Euler products against direct enumeration and 300 progression masses against exact character orthogonality up to floating-point rounding. Twelve numerical integrals reproduce the enumerated mass on both a vertical and the bent contour to absolute tolerance $2\cdot10^{-11}$. The replay uses a log-Gaussian so that its Mellin transform is explicit. The theorem above uses Cogentic's compactly truncated Gaussian.
