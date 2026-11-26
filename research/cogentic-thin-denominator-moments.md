# Centered trace bounds on a thin prime-denominator grid

The high-trace rank argument transfers to every fixed subset of the admissible prime denominators of the required size, using all the original numerator intervals at each selected denominator. The transfer keeps the denominator range and numerator lengths. It changes the one-mark atom and the effective number of smooth columns. The denominator menu can be chosen deterministically within the thin-grid time budget. [Thin-grid candidate](cogentic-thin-denominator-candidate.md) · [Full-grid trace proof](cogentic-projective-trace.md)

## Schedule and inputs

Use the variable-multiple Gaussian with the finite-order degree slack and width. Write $L=\log N$, $z=\log L$, $D=(L/z)^{1/3}$ and $H=Dz$. Let $\log A=(c+o(1))H$, $\log B=(b+o(1))H$, $d\sim xD$, $S=xc+1/x$ and $\rho=2S/(3b)$. Assume $c>2b$ and choose a fixed $\eta>0$ with
\[
 r=b+\rho+\eta,\qquad c<r<2c.
\]
Take $K=\lceil\exp((r-c)H)\rceil$ distinct primes from $[A(1-e^{-30z^2}),A]$. At each denominator use the original numerator grid, including the prime-to-$N$ check for $a-b_v m$. An early proper gcd completes the split. On trials that reach the Gaussian draws the whole selected grid is fixed independently of those draws. There is no sieve involving random field cofactors in the variable-multiple construction. [Grid and polynomial family](cogentic-variable-multiple-lattice.md#the-two-polynomial-fields)

Use the following inputs of the existing moment analyses under the same Dirichlet GRH and algebraic hypotheses.

- The finite-order Gaussian projection, conditional root probabilities, rough joint smoothness bound and clean distinct-mark formula are uniform on the individual primitive mark tuples. These are the finite-order statement in the narrow-band note and equation (1) of the trace note, with the allowed fixed choices of accuracy constants. The target prime satisfies $\log\ell\sim z^3$ and is outside the small-prime singular series. The one-mark joint reference density is $\exp((-\rho+o(1))H)$, uniformly over the original grid. [Finite-order Gaussian estimates](cogentic-narrow-band-moments.md#any-fixed-number-of-marks) · [Clean formula and root conditioning](cogentic-projective-trace.md#joint-smoothness-at-distinct-marks)
- The pointwise reference model, its exact local incidence identity after suppression of unneeded target hits, and its bounds for one- and two-row entries are those used in (2) of the variable-multiple note and (2) of the trace note. On any single numerator interval the model entry has supremum $L^{O_k(1)}M_j$ and variation $L^{O_k(1)}M_j$. Here $M_j$ is the entry scale for its endpoints and $k$ is fixed. Use the pointwise model from the same saddle and geometric grid, with its global mean recomputed for the selected measure. [Two-row estimate and incidence identity](cogentic-variable-multiple-lattice.md#the-cell-estimate-with-two-prescribed-rows) · [Trace centering](cogentic-projective-trace.md#expansion-of-the-centered-trace)
- The narrow-band cleanliness and root-mass estimates concern the field draws alone. The reference quadratic-form bounds, the rank criterion and the norm-direction elimination are those of the existing projective extension of Cogentic Proposition 10.1 and Lemmas 7.4–7.5. The dependence of their interval averages on the selected grid is checked below. [Narrow-band cleanliness](cogentic-narrow-band-moments.md) · [Projective rank and field map](cogentic-homogeneous-marks.md#rank-the-field-map-and-time)

Give each of the $2d+1$ grid intervals equal mass, uniform over all its selected marks. Conditional on the interval and denominator, the numerator is uniform over an integer interval of length $\asymp Aw$, as in the original grid. The mixture weights of the denominators in an interval are proportional to their numerator counts. They stay fixed in every estimated congruence sum. Since $Aw=\exp((c+o(1))H)$, the largest mark atom is
\[
 \|\pi_0\|_\infty\le \exp((-r+o(1))H),\qquad
 n_{\mathrm{thin}}=\exp((r-\rho)H).
\]
The atom times the reciprocal joint smoothness density is at most $n_{\mathrm{thin}}^{-1}\exp(o(H))$, and $n_{\mathrm{thin}}/B=\exp((\eta+o(1))H)$.

## Congruences at fixed denominators

Every selected denominator exceeds $B$ and is a unit at each prime used in the row constraints and small-prime series. For each fixed denominator, slope $s\bmod t$ is the single numerator class $a\equiv s b_v\bmod t$. An integer interval of length $J\asymp Aw$ gives this class mass $1/t+O(J^{-1})$, for every $t$ supported below or at $B$. This also applies when $t>J$. With a weight $F$ of bounded variation on the numerator interval, partial summation gives
\[
 \mathbb E_a\!\left[F(a)1_{a\equiv s b_v\bmod t}\right]
 =\frac1t\mathbb E_a F(a)
   +O\!\left(\frac{\sup|F|+\operatorname{TV}_{I}(F)}{J}\right).
\]
Here $\operatorname{TV}_{I}(F)$ is the total variation of $F$ along the numerator interval. The same estimate applies after combining two compatible classes with CRT. In particular, for a hit class modulo $Q\le B^2$ and $\gcd(t,Q)=1$, the bracket $1+Q1_{\rm hit}$ gives the $t$-class mass $O(1/t+Q/(Aw))$. All these upper bounds survive any mixture of the denominators.

For marks $(a,b_v)$ and $(a',b_{v'})$ put $\Delta=ab_{v'}-a'b_v$. At fixed first mark and fixed second denominator, $t\mid\Delta$ is again a single numerator class. At prescribed $p$ or at $\ell$, the same is true of $p^2\mid\Delta$. Intersecting it with the second hit class costs at most
\[
 O\!\left(p^{-2}+\frac{Q}{\operatorname{lcm}(Q,p^2)}+\frac{Q}{Aw}\right)
 =O\!\left(p^{-1}+\frac{Q}{Aw}\right).
\]
These counts include $b_{v'}=b_v$, where $\Delta=b_v(a-a')$. Equality of denominators creates neither a new exception for the congruence bounds nor an identification of two different marks. Since $0<a<b_v$ and $b_v$ is prime, the fractions are reduced. Rational proportionality of two marks occurs precisely when both coordinates agree. [Primitive Farey marks and projected classes](cogentic-homogeneous-marks.md#conditional-classes-and-smoothness)

## Distinct positions and centering

Fix a cyclic trace row tuple with no two distinct labels at the same physical prime. A position $j$ then has the bound $L^{O_k(1)}M_j(1+Q_j1_{\rm hit})$ with $Q_j\le B^2$. At fixed denominator and interval, use the local incidence identity $f_j\Pi^\circ_j=Q_j1_{\rm hit}\overline U_j(v)$. For $t\le T=\exp(Cz^2)$ supported on the small-prime band, numerator partial summation in the combined $tQ_j$-class gives $t^{-1}$ times that denominator's mean of $\overline U_j$, with error $L^{O_k(1)}M_jQ_j/(Aw)$. The same count without the incidence weight gives $t^{-1}$ times the constant mean, with the expected single hit errors. Unneeded additional prescribed slopes, including those at $\ell$, have the same absolute suppression bounds as in the full-grid trace argument.

Now average using the fixed interval and denominator weights of the selected grid. The point-model mean is its actual selected-grid mean, so the centered main terms cancel after this averaging. Individual denominators do not need the same mean, and conditioning the denominator weights on a slope class would change this calculation. This gives exactly the selected-grid form of (2) in the trace proof,
\[
 \left|\sum_{\operatorname{slope}(v)\equiv s(t)}
       \pi_0(v)g_j(v)\prod_i\Phi_i(v;R_i)\right|
 \le \frac{L^{O_k(1)}M_j}{t}
       \left[\ell^{-1+o(1)}+\frac{tB^2}{Aw}\right].
\]
Here the bracket tends to zero uniformly for $t\le T$, with room for any fixed $e^{-C'z^2}$ tolerance. [Cogentic Proposition 10.1(1), pp. 52–53](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=52)

For the product of small-prime partition expansions in the trace proof retain one required pair agreement at each prime in a tail term with prime product $t>T$. Expose the marks in their fixed order. The classes imposed at the later marks have aggregate moduli $t_j$ with $\prod_j t_j=t$. Their weighted mass is $O_k(1/t+B^2/(Aw))$ by the fixed-denominator bracket bound. The sum of the partition coefficients in absolute value is $L^{O_k(1)}$. This absorbs arbitrarily large $t$ without requiring any extra denominator averaging. For $t\le T$ use the displayed centered sum on each slope class. The unclean $p^2$ pairs cost $O_k(p^{-1}+B^2/(Aw))$ in weighted mass and use the rough joint bound. The exceptional tuples with distinct labels at one physical prime retain their $B^{-1+o(1)}$ row-choice saving, independent of the mark weights. [Distinct-position expansion and tail estimate](cogentic-projective-trace.md#expansion-of-the-centered-trace)

Once the clean formula has been applied on the distinct rational marks, the product of independent marked sums can be restored to include coincident positions. At a fixed first mark, the second weighted atom is at most $O(B^2\|\pi_0\|_\infty)$. Restoration therefore costs $\exp((2b-r+o(1))H)$ up to the fixed-order polynomial weight, negligible since $r>c>2b$. This is an estimate for the expanded main sum. For genuine repeated positions of the original moment one instead identifies the repeated smoothness indicators before bounding their probability.

## Repeated positions, diagonal and rank

For a partition of the $k$ trace positions into $h<k$ distinct marks, each duplicate costs $n_{\mathrm{thin}}^{-1}\exp(o(H))$ after identifying its smoothness indicators. The rough $h$-mark bound is used on those distinct marks. After that pointwise bound, dropping the distinctness restriction in the nonnegative geometric upper bound is valid. For the bipartite graph of active row hits, the tree constraints are single slope classes of mass $B^{-1+o(1)}$, at any denominator. At a closing mark of a simple cycle with distinct physical primes, the two row constraints have mass $B^{-2+o(1)}$ by CRT and $c>2b$. This includes a four-cycle with two distinct marks sharing two rows. If two labels share a physical prime, use the row-choice saving instead. The bridge-only exception of the original cyclic closed walk still has $2h\le k$. Thus (3) and the resulting sums in the trace proof become
\[
 B^{o(1)}\sum_{h<k}(B/n_{\mathrm{thin}})^{k-h}
   + B^{1+o(1)}\sum_{h\le k/2}(B/n_{\mathrm{thin}})^{k-h}.
\]
Choose fixed even $k>2b/\eta$ with positive slack and then enough degree and Gaussian width for its finite-order estimate. Both sums decay by a fixed exponential factor on the $H$ scale. Taking the even trace moment and applying Markov gives the full-grid operator-norm tolerance $e^{-c_k z^2}$ on the large off-diagonal block, with probability $1-o(1)$. [Masked closed-walk count, equation (3)](cogentic-projective-trace.md#repeated-marked-positions)

For the target, constant, real and diagonal entries, use the two-point centered estimate. Their main-band support modulus is at most $BE^2=B^{1+o(1)}$, where $\log E\sim z^3$ is the target band scale. With $Q$ the actual support modulus, the square of the hit bracket has average $O(Q+Q^2/(Aw))=O(Q)$ at every denominator. The true duplicate term is bounded by $L^{O(1)}M_{\alpha\beta}^2 B^{1+o(1)}/n_{\mathrm{thin}}$. Unlike restoration in the large off-diagonal trace, this duplicate term includes the reciprocal smoothness density. The distinct-pair estimates just proved give the required fixed $e^{-Cz^2}$ error. The total mass variance uses the same pair-class estimate with $Q=1$ and the ordinary $\sum_{p>d}p^{-2}$ bound. Thus the diagonal, target and constant-mass conclusions used by the full-grid peeling argument hold with the same tolerances. [Target and diagonal bounds](cogentic-projective-trace.md#the-target-and-the-diagonal)

The narrow-band root cleanliness, mass and normalizer estimates are unchanged because they involve the field draws alone. The stopping rule in the original high-trace peeling uses the off-diagonal operator norm, the weighted diagonal estimates and the protected target bounds. It applies to the selected Gram matrix with these inputs. For the reference spectral lower bound, the equal interval masses give the same Cauchy–Schwarz bound by the sum of squared interval averages. Each selected mark in the interval satisfies the original pointwise logarithm bounds, so the diagonal dominance of the root-interval average matrix and the baseline estimate hold for these averages. The projective discrepancy in the two norm directions is $d\log(b_v/A)=O(de^{-30z^2})$ at each selected mark. These facts give the same polynomial spectral margin on the retained rows. Consequently the Gaussian pair satisfies the rank precondition with probability $1-o(1)$ uniformly over the fixed menu. [Cogentic Proposition 10.1(2), pp. 54–55](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=54) · [Projective norm-direction error](cogentic-homogeneous-marks.md#rank-the-field-map-and-time)

## Deterministic menu construction

The prime number theorem under RH gives $\exp((c+o(1))H)$ primes in the prescribed denominator interval. Its length is $Ae^{-30z^2}$ and exceeds the RH counting error by an exponential factor. There are more than $K$ available because $r<2c$. Scan the at most $A$ integers in that interval, apply deterministic polynomial-bit primality testing, and keep the first $K$ primes. This costs $\exp((c+o(1))H)$, below the grid scan because $r>c$. The prime test and the selected-grid preliminary gcds can all run before the Gaussian pair is drawn.

The one-mark upper bound sums over the selected grid to give $\mathbf E M\le \exp((b+\eta+o(1))H)$ for its number $M$ of joint smooth columns. Markov's inequality makes the proposed cap $M\le \exp((b+2\eta)H)$ fail with probability at most $\exp((-\eta+o(1))H)$. Use this as an unconditional error for discarding the run, without conditioning the moment estimates on the cap or on later extractor success. This transfer certifies the selected grid's moment and rank inputs. The cost and accuracy of the smaller exact lift concern the separate extraction path. [Thin-grid and transposed-lift candidate](cogentic-thin-denominator-candidate.md)
