# Transferring short-root sign estimates to binary dependencies

A signed short-root estimate can replace the independent private root in the final square comparison. The estimate must apply on the law of admitted, completed relations and against the block weights induced by both a CRT sign and the recorded checks. A bound on the unsigned supply of short roots gives no such conclusion. Square detection is a separate requirement. [Unsigned short-root window](keybreak-public-quadratic-window.md) · [Original hidden-root argument](keybreak-anchor-reuse.md)

## The group carrying the square comparison

Let \(N\) be odd with at least two distinct prime factors, \(U=(\mathbb Z/N)^\times\), and \(K=U[2]\). Choose groups \(G_{\mathbb Q}\subseteq\mathbb Q^\times\) and \(G_F\subseteq F^\times\) of evaluable units, with evaluations into \(U\) for the rational numbers and the number field \(F\). Write \(G=G_{\mathbb Q}\times G_F\), and write \(\phi:G\to U\) for the product evaluation. Groups can be taken as the units of suitable evaluation localizations. For square extraction choose the groups so that the certified square roots also belong to them. For example, in a localization of the ring of integers admitting the evaluation, a field square root of a unit belongs to the localization by integral closedness, and its inverse does too. With only a power-order evaluation, the ability to evaluate the reconstructed root must be supplied by the extraction certificate.

Form the abelian groups
\[
 \mathcal H=\{(g,h)\in G\times U:\phi(g)=h^2\},\qquad
 \Delta=\{(g^2,\phi(g)):g\in G\},\qquad
 V=\mathcal H/\Delta.
\]
Here the defining map for \(\Delta\) uses all of \(G\). It is not in general the group of squares of \(\mathcal H\). For every \((g,h)\in\mathcal H\), its square is \((g^2,\phi(g))\), so \(V\) is an \(\mathbb F_2\)-vector space. Projection to \(G/G^2\) has kernel \(K/\phi(G[2])\). Indeed a pair with first coordinate \(g=t^2\) is represented in that kernel by \((1,h/\phi(t))\). Two such sign representatives differ by \(\phi(s)\) for \(s\in G[2]\) precisely when their classes in \(V\) agree.

Because both factor groups lie in characteristic-zero fields, \(\phi(G[2])\subseteq\{1,-1\}\). Choose a CRT character \(\chi:K\to\{\pm1\}\) trivial on \(\{1,-1\}\) and nontrivial on \(K\). For example multiply the signs at two distinct prime-power factors. This character descends to the kernel and extends to a sign character \(\widetilde\chi\) of \(V\) by linear extension over \(\mathbb F_2\). The extension need only be defined on the span of the relations, their block lifts and the kernel. Neither the hidden factors nor the extension are used in the algorithm. On any selected product with \(g=t^2\) the extension takes the value \(\chi(h/\phi(t))\), independently of the choice of \(t\). A value of \(-1\) means the comparison is a mixed CRT sign. The verified modular square congruence then gives a proper factor by a gcd with either sign.

## Exactly which weights factor

Fix the public field, the tests and all public data defining the row distribution. Suppose each completed row carries two block records defining \(g_A,g_B\in G\) and a short unit root \(h\) with \(h^2=\phi(g_A)\phi(g_B)\). The full descended rational and field factors are included in the block records. Recorded columns \(C\in\mathbb F_2^d\) must decompose as \(C_A+C_B\) on the completed rows. This includes parity and multiplicative probe tests where their factors are units at the probes, and permits a constant row contribution on a fixed class. The basic group argument uses only block additivity of the recorded columns, while the separate square detector determines whether they suffice for extraction.

Condition on a square class \(c\in U/U^2\) of the first block. The second block lies in the same class because the total evaluation is a square. Choose \(g_c\in G\) whose value lies in \(c\), for example one first block in that class. For each individual block choose arbitrary reference roots
\[
 h_A^2=\phi(g_A/g_c),\qquad h_B^2=\phi(g_Bg_c).
\]
The lifts depend on the block and its class only. Their existence follows from the class condition, and neither root needs to be found algorithmically. Set \(v_A=[(g_A/g_c,h_A)]\), \(v_B=[(g_Bg_c,h_B)]\). For the actual row \(v=[(g_Ag_B,h)]\), the group law gives
\[
 \widetilde\chi(v)=\widetilde\chi(v_A)\widetilde\chi(v_B)\,
                       \chi(h/(h_Ah_B)).
\]
For any linear functional \(\ell:\mathbb F_2^d\to\mathbb F_2\), multiplication by \((-1)^{\ell(C)}\) just changes each of the first two signs to a function of its own block. This handles the fact that neither the character extension nor the parity functional can be predicted from the bare modular residue of the block. If a descent or acceptance rule makes a column depend jointly on the two records, one needs a new estimate that handles that rule or a reformulation with additive columns.

A sufficient analytic hypothesis on the admitted law \(\mu_c\), for every class of positive mass, is the following single-character bound for every choice of block reference roots and every pair of block sign functions \(f_A,f_B\):
\[
 \left|\mathbb E_{\mu_c}\left[f_A(A) f_B(B)\,
                  \chi(h/(h_Ah_B))\right]\right|\le\epsilon.
\]
The same bound for the mixture follows by summing with its nonnegative class probabilities. In the extraction proof one only needs it for one nontrivial CRT character and the weights from \(\widetilde\chi\) and the recorded linear functionals. A short-root law stated for the bare squares, or for a fixed reference lift without sign weights, is insufficient. The needed estimate must hold after the descent has completed and the retained rows have been defined, or have an error bound strong enough to survive those filters. Restricting the shell or the square classes alone does not guarantee this.

## Rank on the recorded columns and the independent square check

Given the fixed public state, let \(m\) admitted rows be independent draws from the preceding law. Write \(C\) also for the \(d\times m\) matrix of their check columns and let \(z_i\in\mathbb F_2\) encode \(\widetilde\chi(v_i)=(-1)^{z_i}\). For each prescribed \(\ell\), the estimate bounds the probability of \(z_i=\ell(C_i)\) by \((1+\epsilon)/2\). Independence and a union bound give
\[
  \Pr\{z\in\operatorname{rowspan} C\}
       \le 2^d\left(\frac{1+\epsilon}{2}\right)^m .
\]
For example \(\epsilon\le1/4\) and \(m\ge 2(d+s)\) give a bound at most \((25/32)^d(25/64)^s\). The matrix need not have full row rank. The argument also works with a conditional upper bound \((1+\epsilon)/2\) on each new agreement, given all previously drawn rows, for each fixed \(\ell\). Uniform sampling with replacement from a fixed admitted pool is one interpretation of the independence assumption. An adaptive capped sampler without the stated conditional bound needs a separate transfer.

On the complement of this event, \(z\) is a nonzero functional on \(\ker C\). A uniform binary vector \(\lambda\in\ker C\) therefore has \(\sum_i\lambda_i z_i=1\) with probability \(1/2\). This includes the zero vector in the sampling law. The selected modular root is the known product of the selected \(h_i\). For its matching lifted root one still needs the chosen product in \(G\) to belong to \(G^2\) and the square roots to be actually reconstructed and evaluated. A subspace cut out by finitely many characters cannot simply be identified with \(G^2\).

A sufficient implementation premise is an event of probability at least \(1-\eta\) on which the recorded checks certify both squares for *every* dependency on the retained pool. The character sampler's uniform separation of the allowed class group, together with the other square tests, is one way to supply this premise if all the new relations belong to that group and meet its local restrictions. In odd field degree the needed implication is concrete. Suppose the rational prime and sign rows force the rational coordinate to be a square, the field norm and sign rows force the norm of the field coordinate to be a rational square, and the ideal parity and successful probes force the remaining field squareclass to be rational. Write the field coordinate as \(r\,t^2\) with \(r\in\mathbb Q^	imes\). Its norm is \(r^{[F:\mathbb Q]}\operatorname{Nm}(t)^2\). The norm condition and odd degree force \(r\) to be a rational square. The exact lift must still give evaluable roots as specified above. More weakly, it suffices to bound by \(\eta\) the probability that the uniformly selected dependency has no certified square in \(G\). Include a bound \(\eta'\) for an abort in exact reconstruction on certified instances. With
\[
 \delta=2^d((1+\epsilon)/2)^m,
\]
the split probability is at least \((1-\delta)/2-\eta-\eta'\), besides any sampler failures. This uses a union bound on the original law, so neither square certification nor reconstruction needs to be independent of the signs. A proof that some dependency is a square, or that the checks evaluate correctly on individual atoms, would not give the required probability bound. With simultaneous certification and uniformly bounded reconstruction failure, multiple fresh kernel draws can be compared by separate gcds. [Class separation and exact square checks](keybreak-cumulative-character-probes.md)

## Uniform kernel sampling

An arbitrary null vector can lie in the kernel of \(z\) even when that functional is nonzero. One way to implement the required uniform choice is to construct a linear projection onto the binary kernel over a finite extension \(L/\mathbb F_2\). Use the diagonal-weighted Gram matrix \(S\) for the check matrix \(C\). On the event that its rank-index coefficient is nonzero, \(\ker_L S=\ker_L C\) and \(\ker_L S\) complements the range of \(S\). In particular the minimal polynomial is \(Xq(X)\) with \(q(0)\ne0\), and \(q(S)/q(0)\) is a projection onto \(\ker_L S\). The rank hypothesis for this step is supplied by the randomized Gram coefficient, independently of the unknown CRT signs. [Gram coefficient failure bound](../formal/cogentic/Cogentic/RandomizedGramMinor.lean) · [Equal kernel and complementary range](../formal/cogentic/Cogentic/RandomizedGramRank.lean)

A scalar Krylov sequence with independent uniform left and right probes over \(L\) recovers the whole minimal polynomial with failure at most \(2m/|L|\) from \(2m\) terms. Indeed, for each irreducible \(f\mid\mu_S\), dropping one copy of \(f\) from the scalar minimal polynomial implies the scalar recurrence is annihilated by \(\mu_S/f\). The operator \((\mu_S/f)(S)\) is nonzero. The right probe lands in its kernel with probability at most \(1/|L|\), and otherwise the left probe annihilates its image with probability exactly \(1/|L|\). Use the union bound over at most \(m\) factors. After this preprocessing, apply the projection to a fresh uniform vector in \(L^m\). A fixed surjective \(\mathbb F_2\)-linear coordinate of \(L\), applied entrywise, sends the resulting uniform kernel vector to a uniform element of \(\ker_{\mathbb F_2} C\). This map is onto since a binary kernel vector can be lifted by multiplying it by a field element of coordinate one. Fresh draws therefore need a polynomial application and a check, rather than a computed kernel basis. The usual sparse costs apply to these additions if the original stored incidence bound holds for the short-root data. [Sparse Krylov sequence and cost](keybreak-sparse-dependency.md)

## A diagnostic for the strength of the analytic hypothesis

For a fixed class, view each supported record \((A,B,h)\) as an edge of the bipartite graph of block records. Parallel edges are allowed. Along an even cycle the alternating product of the edge roots has square one: the evaluations on both sides telescope. Its \(\chi\)-value is the product of the signed edge values \(\chi(h/(h_Ah_B))\), since the vertex lifts also telescope. If every cycle has positive sign, then the edge signs factor as a product of vertex signs, by propagating a choice along a spanning forest. Those vertex signs are allowable weights and give correlation one. In particular the stated arbitrary-weight estimate cannot hold for a law supported on a forest, or for a one-edge conditional law with a unique root. If the estimate holds with \(\epsilon<1\) on the full support, some cycle has a mixed CRT comparison. Existence of a cycle in that support supplies no bound on its appearance in an affordable sample. The recorded-column argument avoids requiring such a collision bound.

These implications are conditional on a signed short-root estimate and on square-detector coverage for the new row law. They do not supply either of those analytic inputs.
