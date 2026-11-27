# Minor-arc bounds for narrow two-mark Gaussian probes

A raw dual frequency that stays away from a specified set of rational arcs gives a power-saving smooth Fourier coefficient on each Cartesian progression. The estimate is unconditional. A tested coordinate contributes a saving arbitrarily close to \(X^{-1/4}\) at top scale, where \(X\) bounds the raw values. The criterion concerns the actual dual frequencies. Counting their weighted mass in the remaining arcs is a separate requirement. [Exact dual-mode expansion](keybreak-narrow-smooth-probes.md) · [Cartesian support and ideal Gaussian widths](keybreak-top-residue-conditioning.md)

## The raw frequency and its progression

Write \(e(t)=e^{2\pi it}\) and use \(\|\cdot\|\) for distance modulo one. At endpoint \(X\), assume \(\log y/\log\log X\to\infty\) and \(y=X^{o(1)}\). For a coordinate progression \(n\equiv r\bmod m\) and phase \(e(n\theta)\), additive orthogonality represents its smooth prefix as

\[
\frac1m\sum_{h=0}^{m-1}e(-hr/m)
 \sum_{\substack{1\le n\le x\\ P^+(n)\le y}}e(n(\theta+h/m)).
\]

This applies to any residue, including a nonunit. If \(\theta=a/q+\delta\), the reduced denominator \(q_h\) of \(a/q+h/m\) satisfies \(q/m\le q_h\le qm\), because each rational can be recovered from the other by adding a rational of denominator dividing \(m\). The error \(\delta\) stays the same. For fixed \(0<\eta<1/2\), a sufficient single-approximation criterion for Harper’s Theorem 1, simultaneously for \(X^{1/2}\le x\le X\) and all \(h\), is

\[
\begin{split}
(q/m)(1+X|\delta|)&\ge X^\eta,\\
(qm)^2y^3\max_{t\in\{X^{1/2},X\}}
     (1+t|\delta|)^2/t&\le 1/4.
\end{split}
\]

Only the two upper endpoints of the convex function \(1/t+2|\delta|+t\delta^2\) need to be checked for the size condition. Shorter prefixes can be estimated by \(X^{1/2}\). In the applicable range Harper bounds the smooth sum by \(x^{1+o(1)}K_x^{-1/2}\), with \(K_x=q_h(1+x|\delta|)\). In fact the leading factor is \(\Psi(x,y)K_x^{-1/2+(3/2)(1-\alpha(x,y))}\) times logarithmic factors, and \(\alpha(x,y)=1-o(1)\) uniformly in this range. The lower bound at \(X\) gives \(K_x\ge(x/X)X^\eta\), so

\[
xK_x^{-1/2}\le X^{1-\eta/2}.
\]

This avoids losing the saving when differencing prefixes at different endpoints. [Harper, Theorem 1 and (2.1)](https://arxiv.org/pdf/1408.1662#page=7)

There is a criterion that avoids choosing one good approximation in advance. Require

\[
  q\bigl(1+X\|\theta-a/q\|\bigr)\ge mX^\eta
  \qquad\text{for every reduced }a/q. \tag{1}
\]

It suffices to check \(q<mX^\eta\). An approximation \(a'/q'+\delta\) to \(\theta+h/m\) gives an approximation to \(\theta\) with denominator at most \(mq'\) and the same error. Thus (1) ensures \(q'(1+X|\delta|)\ge X^\eta\) for every shifted approximation. At each prefix \(x\ge X^{1/2}\), Dirichlet gives \(q'\le x^{1/2+\tau}\), \(|\delta|\ll(q'x^{1/2+\tau})^{-1}\), for fixed \(0<\tau<1/4\). When \(q'\le x^{1/2-\tau/2}\), one has \(K_x\ll x^{1/2-\tau/2}\), so Harper’s condition \(K_x^2y^3\le x/4\) holds eventually. For larger \(q'\), \(|\delta|x\ll x^{-\tau/2}\), and the Fouvry–Tenenbaum bound quoted and used by Harper gives

\[
\ll x(1+|\delta|x)(\log x)^3
 \left(\frac{\sqrt y}{x^{1/4}}+\frac1{\sqrt{q'}}
                       +\sqrt{\frac{q'y}{x}}\right)
\le x^{1-(1/4-\tau/2)+o(1)}.
\]

Combining the ranges, every smooth prefix and interval in the progression has absolute bound \(X^{1-s+o(1)}\), where \(s=\min(\eta/2,1/4-\tau/2)\). The average over the \(m\) additive shifts costs no factor \(m\) at this stage. To obtain an average per point in an interval of length \(\ell\gg m\), the bound is \(O(mX^{1-s+o(1)}/\ell)\), capped trivially by \(1\). Negative values use reflection and zero can be treated separately. For a support step \(m=X^{o(1)}\), the union of arcs excluded in (1) has Lebesgue measure \(O(m^2X^{2\eta-1})\), obtained by summing \(O(mX^\eta/(qX))\) over the at most \(q\) numerators at each denominator. This measure concerns continuous angles. [Harper, (1.1) and the proof of Theorem 3](https://arxiv.org/pdf/1408.1662#page=32) · [Fouvry–Tenenbaum](https://doi.org/10.1112/plms/s3-63.3.449)

An invariant sufficient test uses the progression frequency \(m\theta\) itself. Require \(q(1+(X/m)\|m\theta-a/q\|)\ge X^\eta\) for every reduced \(a/q\). Multiplying a rational approximation to \(\theta+h/m\) by \(m\) can only decrease its denominator and multiplies the phase error by at most \(m\). Thus this test also gives the needed lower bound on \(K_x\). Its exceptional set for raw \(\theta\) has measure \(O(mX^{2\eta-1})\), since \(\theta\mapsto m\theta\) preserves normalized Lebesgue measure.

If a predicate first divides by a specified positive \(g\), put \(n=gu\) on that branch, omitting the branch when the divisibility and progression conflict. The quotient progression has period \(m'=m/\gcd(g,m)\), endpoint \(X'=X/g\), and raw frequency \(g\theta\). In particular (1) with exponent \(\eta+\kappa<1/2\) for fixed \(\kappa>0\) implies (1) with exponent \(\eta\) for the new parameters when \(g=X^{o(1)}\). Indeed a rational approximation to \(g\theta\) of denominator \(q\) lifts to one of denominator at most \(gq\) for \(\theta\), and (1) gives \(q(1+X'\|g\theta-a/q\|)\ge(m/g)X^{\eta+\kappa}\ge m'(X')^\eta\). Thus a band-semismooth predicate that is a disjoint union of \(X^{o(1)}\) such branches keeps the exponent using this fixed slack.

## Gaussian insertion and the weighted mode count

On one raw Cartesian phase let \(W(z)=\exp(-\pi(z-a)^{\mathsf T}Q(z-a))\) with positive definite \(Q\). Assume the two Gaussian semiaxes are \(X^{1+o(1)}\), both steps \(m_i=X^{o(1)}\), and \(X\) includes the center and a \(\log X\) marginal tail cutoff, as can be arranged at top scale. The Gaussian normalizer on each phase is \(\asymp(\det Q)^{-1/2}/(m_1m_2)\) uniformly in the translate, by comparing progression rectangles to the Gaussian integral. The excluded tail is smaller than every fixed power of \(X^{-1}\). Each dual character on the raw affine lattice extends to a constant phase times \(e(\theta_1z_1+\theta_2z_2)\), by choosing real arguments on a lattice basis.

With one minor-arc coordinate \(i\), use one-dimensional partial summation along that coordinate for each fixed other coordinate. The Gaussian along the line is unimodal, so the variation bound costs a constant times its line supremum. The line suprema are a Gaussian in the other coordinate. Dividing their sum by the lattice normalizer gives the normalized bound

\[
O\bigl(X^{1-s+o(1)}m_i\sqrt{Q_{ii}}\bigr)=X^{-s+o(1)}.
\]

With both coordinates minor, use two-dimensional partial summation, extending the truncated prefix sums constantly beyond the cutoff endpoints. The mixed derivative satisfies

\[
 \int_{\mathbb R^2}|\partial_1\partial_2W|
   \ll \sqrt{Q_{11}Q_{22}}\,(\det Q)^{-1/2}.
\]

Indeed it is \(W\) times \(4\pi^2(Q(z-a))_1(Q(z-a))_2-2\pi Q_{12}\), and the normalized Gaussian second moments and Cauchy–Schwarz bound both terms. The resulting normalized bound is \(X^{-s_1-s_2+o(1)}\). Interval cutoffs can be included in each coordinate prefix. This calculation keeps the exact Gaussian and the entire phase \(e(\theta_1z_1+\theta_2z_2)\). Uniformity in each progression allows summing over support phases by their Gaussian masses.

The unweighted denominator probe in the dual expansion has a simpler estimate under (1). Choosing a nearest integer to \(m\theta\) and reducing its ratio with \(m\) gives \(\|m\theta\|\ge m(X^\eta-1)/X\). The geometric progression bound is \(O(X^{1-\eta}/m)\) on all intervals. The same Gaussian estimates apply.

Thus a set of modes with one tested coordinate is negligible by absolute summation if its total Poisson weight is \(O(X^{s-\zeta})\) for fixed \(\zeta>0\). A set with two tested coordinates can have weight \(O(X^{s_1+s_2-\zeta})\). The numerical thresholds can approach \(1/4\) and \(1/2\) per coordinate set, respectively, by taking \(\eta<1/2\) near its endpoint and \(\tau>0\) small. For \(X=V^{d+o(d)}\) and \(\sigma=V^{2-\epsilon}\), the unconditioned weight allowance from the native kernel is \(X^{\epsilon+o(1)}\), with the known additional \((d-2)\log J\) in log mass if a congruence lattice is bounded only by \(J\mathbb Z^d\). The errors are also relative when the ideal smooth probability is \(X^{-o(1)}\). [Dual Gaussian tail and mass](keybreak-narrow-smooth-probes.md)

## What remains on the rational arcs

The bound separates only modes satisfying the Diophantine condition. In particular, rational frequencies with denominator dividing the progression step give a constant phase on that progression. The pinned Dirichlet GRH progression estimate can expand a rational twist of denominator \(q\) by residue classes modulo \(\operatorname{lcm}(m,q)\), leaving a weighted principal term. With a residual factor \(e(\delta n)\), direct partial summation costs \(1+|\delta|X\) on the prefix error. For a prime \(q>y\) coprime to \(m\), the principal term at \(\delta=0\) gives the existing nonzero-class cancellation \(1/(q-1)\) in a single coordinate. These calculations do not bound an arbitrary irrational phase from a Dirichlet character estimate, and the principal terms can remain large on other arcs. The continuous size of the arc union gives no mass estimate for the discrete dual modes. A full narrow-image smoothness comparison still needs a bound or cancellation for the weighted modes with neither coordinate certified by the minor-arc criterion. [KeyBreak, (G.7)–(G.8)](https://crypto.sjtu.edu.cn/factoring.pdf#page=109) · [Leading residue calculation](keybreak-narrow-smooth-probes.md)
