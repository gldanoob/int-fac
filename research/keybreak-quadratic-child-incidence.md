# Bounding bad-child incidence by the resultant

In a complete parent dyad at quadratic width \(\sigma\ge V^{2+\xi}\), an upper bound on the normalized loss to bad children follows from the shared-root algebraic moment and an elementary count of primes dividing a resultant. This argument works for a collection chosen using the rational anchor. It also applies when bad children depend on that same anchor and on the entire sampled field.

For a band with \(n_P\asymp P/\log P\) eligible parents, retain up to \(T\) rationally suitable marks per parent, in any order independent of the multiplier and the coefficient Gaussian. Here \(T=(V^3/P)\exp(-O(d\log d))\), rounded to an integer, is sufficient for the estimate. Use a weight \(w_h=1/(n_P T)\) for each retained mark, so \(\sum_h w_h\le1\) and \(w_{\max}\le V^{-3+o(1)}\). The proof below also permits arbitrary nonnegative anchor-dependent weights satisfying these two bounds. A primitive positive mark occurs at most once in this union because its value at the anchor is \(pn\) with \(n\) smooth below the parent band. This uniqueness is used before forming pairs. The cap describes a subset for counting good records; no efficient enumeration of the subset is asserted.

Write \(U=V^{-o(1)}\) for the common algebraic core reference in this band. For each child label \((q,s)\) define \(H_{q,s}\) to be the sum of the weights of retained marks that vanish at \(s\bmod q\) and pass the algebraic test, times the indicator of the field-root event \(F(s)=0\bmod q\). One may further restrict to labels actually occurring in the records. If incidences are counted with multiplicity, its polynomial bound from the norm size can be inserted in the estimates below. The child's actual bad mass in this public law is
\[
 W_1\delta_1=\mathbb E\sum_{q,s} B_1(q)\,\mathbf1_{F(s)=0}\mathbf1_{\rm bad(q,s)} ,
\]
where the deterministic positive profile satisfies \(B_1(q)\ge 1/q\) and \(W_1\) is polynomial in the degree parameter. The estimate charges the same collection of labels and the same field law as this definition. The active source profile has exactly this lower bound. [KeyBreak, (G.39)–(G.41) and (G.54)–(G.55)](https://crypto.sjtu.edu.cn/factoring.pdf#page=118)

Condition first on the anchor. For each nonanchor projective root the probability of the field-root event is \(O(1/q)\), since one coefficient enters with unit slope and \(\sigma/q\to\infty\). This includes finite roots when \(q\mid Q\), since \(Qs-r\) is then a unit by primitivity. At the anchor itself the field value is nonzero modulo \(q\) on the admitted range \(q\nmid kN\). At infinity the same conclusion or estimate follows from the leading coefficient and the homogeneous anchor equation. For the finite active labels use the wide shared-root pair bound under the actual conditional Gaussian: the two-shape probability for distinct marks is at most \((\log V)^{O(1)}U^2\). This upper bound holds phase by phase and permits marks of different discriminants as well as distinct primitive marks of the same discriminant. [Wide algebraic pair comparison](keybreak-quadratic-pair-reserve.md#counting-cores-in-a-phase)

For two distinct primitive positive definite forms \(h,g\), their nonzero integral resultant has absolute value \(O((V(\log V)^{O(1)})^4)\). Each common projective root requires \(q\mid\operatorname{Res}(h,g)\); there are at most two such roots per prime because the reductions are nonzero quadratics. Consequently a fixed pair occurs in at most \(O(\log V)\) labels even after summing *all* active child primes. A single mark occurs in at most two labels at each prime. Write \(Y_1\le V^{1+o(1)}\) for the largest child. Expanding the square and using the root-probability bound together with \(1/B_1(q)\le q\) gives
\[
 \mathbb E\sum_{q,s}\frac{H_{q,s}^2}{U^2B_1(q)}
 \ll (\log V)^{O(1)}\left(\sum_h w_h\right)^2
      + \frac{Y_1}{U^2} w_{\max}\sum_h w_h
 \ll (\log V)^{O(1)}.
\]
The middle expression holds conditionally on the anchor, with its realized weights. For diagonal terms the conditional shape probability was bounded simply by one. The deterministic square expansion and the distinct-pair and diagonal count are kernel-checked in finite form. [Weighted incidence inequality](../formal/cogentic/Cogentic/RandomizedWeightedIncidence.lean)

The displayed label sum uses finite child states. If a separate projective state is needed, the same proof requires its corresponding conditional pair estimate and bad-state profile.

Cauchy–Schwarz on the joint label and field measure now yields
\[
 \frac1U\,\mathbb E\sum_{q,s} H_{q,s}\mathbf1_{\rm bad(q,s)}
 \ll (\log V)^{O(1)}\sqrt{W_1\delta_1}.
\]
In particular no additional rational second-moment assumption *conditioned on a child label* appears in this deletion estimate. A parent retaining order \(T\) suitable marks has one-mark mean at least \(TU/(\log V)^{O(1)}\), so the same conclusion with a polynomial loss applies to its reference normalization after averaging over the band. Proving this happens with polynomial probability for the intended parent population still needs an ordinary rational concentration estimate. With only the current exponentially small anchor hit bound, the displayed deletion error need not be small relative to that hit probability. Internal bad-state propagation under the full composite-anchor law and a narrower algebraic pair estimate are separate requirements.
