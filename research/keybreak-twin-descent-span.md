# What twins of a public top-prime descent can learn

Fix a single input \(N\), its accepted field and rational environment, the character probes, and the finite descent caps. A completed top request for a unit prime \(p\) has a certified identity
\[
 p=q_p\psi(\gamma_p)\pmod N.
\]
The rational correction and signed algebraic occurrence list are recorded as for an anchored row. Two independent completed requests for \(p\) have combined target \(p^2\) with known root \(p\). Their parity-vector sum is a valid public row with no private label. Equivalently one can divide their identities and use target \(1\), since inversion has the same binary parity. All algebraic verification and path work is charged to this input. [KeyBreak §5.2 and Appendix H.6](https://crypto.sjtu.edu.cn/factoring.pdf#page=136)

## Modal part and local path variation

Write \(V_{\mathrm{par}}\) for the common binary vector space of recorded parity and character checks. For each proposed prime \(p\), let \(c_p\) be the probability of completing the bounded request and \(X_p\) the law of its parity vector conditional on completion when \(c_p>0\). A failed pair attempt contributes the zero vector. An independently drawn pair therefore has a public vector distribution \(\mu\) obtained by proposing \(p\) with law \(\nu\) and, with probability \(c_p^2\), taking \(X_p+X'_p\) for independent conditional draws.

For an arbitrary binary linear probe \(\ell\), put \(s_p=\Pr[\ell(X_p)=1]\) and let \(m_\ell(p)\) be a modal bit. The bit differs from its mode with probability \(\epsilon_p=\min(s_p,1-s_p)\). The twin detects disagreement at that prime with probability \(2s_p(1-s_p)\) conditional on both completions, between \(\epsilon_p\) and \(2\epsilon_p\). For a fixed prime multiset \(p_1,\ldots,p_k\) in a private shape, conditional on its independent top paths completing, the probability its parity differs from the sum of its modal bits is
\[
 \frac{1-\prod_{i=1}^k(1-2\epsilon_{p_i})}{2}
 \le \sum_{i=1}^k\epsilon_{p_i}.
\]
Here the shape has positive coordinates as in the counted construction. Inverses in its target quotient give the same binary bits. Any known extra parity correction can be included on both sides. For a fixed probe whose unconditional twin detection probability is \(\theta\), \(m\) independent pair attempts all miss it with probability \((1-\theta)^m\le e^{-m\theta}\).

A simultaneous version uses the whole quotient by a realized public subspace \(U\subseteq V_{\mathrm{par}}\). If \(\pi_p\) is the law of \(X_p\bmod U\), choose one modal vector \(M_U(p)\) in that quotient. Then
\[
 1-\max_x\pi_p(x)\le
 \Delta_U(p):=\Pr[X_p+X'_p\notin U]=1-\sum_x\pi_p(x)^2
 \le 2(1-\max_x\pi_p(x)).
\]
Consequently the chance that an anchored quotient vector differs from the sum of its prime modes is at most \(\sum_p I(p)\Delta_U(p)\), where \(I(p)\) is the expected number of requests at \(p\) in the private shape law. This estimate compares complete quotient vectors and requires no union over probes.

## The staged shape law supplies incidence domination

Write \(D=(\log N/\log\log N)^{1/3}\), \(H=D\log\log N\) and \(V=DH\). Work on the good-field event and the rough-input branch of the existing prepass, so \(2^{\omega(N)}=\exp(o(H))\). Take the private component consisting of counted good shapes whose descents complete, with the source's exact predicates. The staged lower count and bounded-completion result give raw probability at least \(\exp(-(\sum_j w_j+o(1))H)\) for a counted completion or an immediate factor. When the factor event accounts for at least half that lower bound, it already supplies a split at the ordinary attempt rate. Otherwise the lower exponent holds for the counted completed component. The all-stage prefix upper bound gives the matching upper exponent for every accepted shape. In particular this component has mass at least \(\exp(-o(H))\) among retained shapes. These estimates apply to the same field and do not require an additional model for the distribution of the top primes. [Staged shape and prefix counts](keybreak-private-band-stages.md) · [Rough-input prepass](keybreak-private-shape-work.md#ensuring-the-count-suffices-on-every-input) · [KeyBreak Lemmas H.4–H.5](https://crypto.sjtu.edu.cn/factoring.pdf#page=132)

To bound incidence, prescribe that a prime \(p\) of stage \(j\) divides one coordinate. Its certified stage divisor \(d_j\) then contains \(p\), so in the ordinary multiple count this coordinate's stage sum becomes
\[
 \sum_{\substack{d\ge T_j,\ p\mid d\\P^+(d)\le Y_j}}\frac1d
 \le T_j^{-\eta_j}p^{-1+\eta_j}
       \prod_{q\le Y_j}(1-q^{-1+\eta_j})^{-1}.
\]
This follows by applying the Rankin bound and comparing its Euler factor at \(p\) with and without \(p\mid d\). The other stage sums, second coordinate, and unit-square fiber upper bound stay as before. Here \(p^{\eta_j}\le Y_j^{\eta_j}=O(D)\) since this is a fixed positive stage cutoff. Apply the bound to either coordinate and divide by the raw lower probability of the counted completed component. Uniformly for its possible requested primes,
\[
 I(p)\le \frac{\exp(o(H))}{p}.
\]
Squarefreeness and coprimality of the counted coordinates mean each prime is requested at most once. The displayed estimate also bounds expected multiplicity directly by summing the two coordinate occurrences.

For training, select uniformly among the complete dyadic bands used by the finite shape recipe, then sample a uniform prime within that band by independent integer proposals and exact primality tests. There are polynomially many bands in \(\log N\). The prime number theorem gives polynomial expected proposal work and allows a polynomial cap with negligible failure probability. The resulting law on supported primes satisfies \(\nu(p)\ge 1/[p\,\operatorname{poly}(\log N)]\) after including the negligible cap loss. It does not need to decide which primes are good. The incidence comparison is \(I(p)\le L\nu(p)\), \(L=\exp(o(H))\), on the private component.

When all relevant \(c_p\ge c_*>0\), a fresh private shape and any fixed public subspace satisfy
\[
 \Pr[\text{private quotient differs from its prime-mode sum}]
 \le \frac{L}{c_*^2}\,\mu(V_{\mathrm{par}}\setminus U).
\]
The source bounds failure *without a factor*. To keep that distinction, take \(c_*=1/2\) and let \(q\) be the probability of a proper factor during a public pair attempt. A good prime with \(c_p<1/2\) has per-request factor probability at least \(1/4\) for large inputs, so the proposal mass of those primes is at most \(4q\). Their entire private incidence costs at most \(4Lq\). In a virtual public sampler record a factor outcome as a new independent basis vector in \(V_{\mathrm{par}}\oplus\mathbf F_2\). While the actual pool has found no factor, that vector lies outside \(U\). The augmented public law \(\bar\mu\) then gives the unconditional version of the preceding inequality on this event, with upper bound \(4L\bar\mu((V_{\mathrm{par}}\oplus\mathbf F_2)\setminus U)\).

If \(U_m\) is spanned by \(m\) independent attempts, the leave-one-out bound now gives
\[
 \mathbb E\!\left[\mathbf 1_{\rm no\ public\ factor}\,
       \Pr[\text{private quotient differs from its prime-mode sum}\mid U_m]\right]
 \le \frac{4L(\dim V_{\mathrm{par}}+1)}{m+1}.
\]
One can use the dimension of the support span of the augmented sampler. For a fixed realized \(U\) the quotient mode refers to the conditional per-prime path law, so no enumeration of the modes is needed. The training paths and prime choices use only public data. They leave the conditional hidden-root fiber of fresh anchored rows unchanged. [Leave-one-out span bound and tagged extraction](keybreak-public-span-schedule.md)

The prime proposals take polynomial work per attempt. Every attempt still charges up to two complete capped descents, with records and character checks. In the illustrative \(1.922\) public-span schedule the per-tree search allowance at the largest charged stage is about \(1.19897\) in \(H\) units, after subtracting the private row-count coefficient \(.720\). At \(m=\exp((.9608+o(1))H)\), using that cap gives a public search budget of about \(2.15977\), even before any additional work. This calculation is an upper allowance for direct sampling. Smaller effective noise dimension or a cheaper shared way to build the twins would need its own work and supply estimate.

## Deterministic modes need different relations

At the full twin span \(U_\infty=\operatorname{span}(\operatorname{supp}\mu)\), all \(X_p\) for a fixed supported \(p\) have a single class. Let \(E\) be the binary space with one basis vector \(e_p\) per such top prime. Then
\[
 \phi:E\longrightarrow V_{\mathrm{par}}/U_\infty,\qquad
 e_p\longmapsto [X_p]
\]
is well-defined. It determines the modal quotient of a positive private shape from the prime parity vector of its target. A relevant arithmetic comparison is
\[
 \sigma:E\longrightarrow
       (\mathbb Z/N)^\times/((\mathbb Z/N)^\times)^2,\qquad
 e_p\longmapsto[p].
\]
Every anchored target belongs to \(\ker\sigma\). A public combination of top paths with a certified modular square root yields a top parity vector in \(\ker\sigma\). If the resulting parity vectors span \(W\), the corresponding public relations kill \(\phi(W)\). The exact remaining modal contribution on private shapes lies in the image of \(\ker\sigma/W\) under \(\phi\). In particular if \(\phi\) vanished on \(\ker\sigma\) after the public quotient, every surviving functional on the modes would be a character of the image of \(\sigma\), and every private top parity would have zero modal response. The useful quantity here is the image on retained shapes, which may be smaller than either full space.

Twins themselves enforce no equation between different top primes. At the level of the law alone, point masses \(X_p=e_p\) give zero twins, while private products of two distinct primes in the same modular squareclass give nonzero modes \(e_p+e_q\). Known scalar corrections and combinations whose targets are exact rational squares likewise impose zero top parity. A small-height variant gives the same obstruction for modular certificates. Suppose a root and an optional top-free rational factor have the form
\[
 (a/b)^2\equiv (u/v)\prod_p p^{e_p}\pmod N,
\]
all denominators being units, with \(a,b,u,v\) of height \(\exp(O(V))\). The numerator and denominator of \(u/v\) contain no top primes. If \(\sum_p |e_p|=o(D)\) and the top primes have size \(\exp(O(V))\), both terms after clearing denominators are \(N^{o(1)}\). Their congruence is exact over the integers and forces every \(e_p\) to be even. This rules out short small-height root identities as a source of inter-prime mode constraints.

The space \(E\) has \(\exp(\Theta(V))\) coordinates on any fixed eligible stage, while the target squareclass space has dimension at most \(\omega(N)\). Generating the whole kernel \(\ker\sigma\) by separately acquired parity records would therefore exceed the current budget. Also a public table of explicitly named primes of size \(\exp(O(H))\) has probability at most
\[
 \sum_{p\ {\rm in\ table}} I(p)\le \exp(-\Omega(V))
\]
of containing even one requested prime of an independent counted private shape. Thus direct lookup of per-prime modal bits cannot identify the private modes at this scale. An arithmetic identity extending to unseen primes, a targeted bound on the modal image, or an independent cheaper source of known-root rows would address this part of the problem. The twin transfer supplies only the path-variation estimate.
