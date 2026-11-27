# Conditioning the ideal top-pair law on the leading residue

For two ordinary top marks with distinct prime denominators, the ideal Gaussian law in KeyBreak (G.19) has a simple smoothness response to fixing the leading coefficient residue. On all but one residue class at each denominator, the conditional joint smoothness probability is the unconditioned probability times the usual unit normalization, with a power-saving additive error. On the excluded classes the probability is exactly zero. This concerns one decoded residue and the ideal law, and does not supply (G.19) for a narrower actual coefficient law. [KeyBreak, Lemma G.2 and (G.19)–(G.23)](https://crypto.sjtu.edu.cn/factoring.pdf#page=106) · [Leading-residue obstruction to full image comparison](keybreak-two-mark-gaussian-width.md)

## Refining the separate periods

Write $F=F_0+2GR$ as in the source, with $R$ of degree $d-1$ and leading coefficient $c_0$. Take two primitive top marks $P_i=(a_i,b_i)$, with distinct odd prime denominators $b_i\asymp V$, nonzero determinant $\Delta=|\det(P_1,P_2)|$, and $b_i\nmid 2G(P_i)$. The last condition holds in the ordinary top regime because $G(X,Y)=QX-rY$, the public rational modulus $Q$ is prime and larger than $b_i$, and $a_i$ is a unit modulo $b_i$. Set $B=b_1b_2$. In this setting $\gcd(\Delta,B)=1$, since reducing the determinant modulo either denominator leaves the product of two units.

Let $q=c_0\bmod B$, decoded from the evaluation image. If $z_i=F(P_i)$, the additional condition is exactly
$$
z_i\equiv F_0(P_i)+2G(P_i)a_i^{d-1}q\pmod{b_i},\qquad i=1,2 .
$$
Indeed each equation recovers $q\bmod b_i$, and CRT combines them. In an original phase of the affine image, the separate periods are $m_i=2|G(P_i)|\Delta$ by (G.21) at the top. Since $(m_i,b_i)=1$, refining by the respective affine congruence leaves one Cartesian progression in that phase with separate periods $m_i'=b_i m_i$. In particular every old phase survives for every $q$, and its covolume increases by exactly $B$.

Suppose the two tests are ordinary smoothness tests with cutoffs below both denominators. A band-semismooth test with every allowed exceptional prime also below both denominators works the same way. Let a residue $q$ be good if both affine values above are nonzero modulo their respective denominators. Exactly one class modulo each $b_i$ is forbidden, so the bad fraction among the $B$ residues is $1/b_1+1/b_2-1/B$. A bad $q$ forces one value divisible by a prime larger than any permitted factor, and the joint event then has probability zero.

## An unchanged principal count on good classes

On an old phase in coordinate $i$, use (G.8) on an interval $I$. If its residue is $s\bmod m_i$, put $g=(s,m_i)$. A good $q$ keeps this gcd equal to $g$ after refinement to $m_i'$. Among smooth numbers, the extra principal condition of being coprime to $b_i$ holds automatically. Thus the principal count in the new progression is precisely the old principal count divided by $b_i-1$, since its divisor denominator changes from $\phi(m_i/g)$ to $\phi(m_i/g)(b_i-1)$. If $g$ itself excludes smoothness, both main counts are zero. For an allowed exceptional prime in a semismooth test, division by that prime leaves the same reasoning, since it is different from $b_i$. One can sum the errors using (G.10).

Let $M_I$ and $M'_I$ denote the counts of all points in the old and new one-dimensional progressions in $I$. The endpoint estimates are $M_I=|I|/m_i+O(1)$ and $M'_I=|I|/m_i'+O(1)$. With a global endpoint bound $U$ and a fixed small $\epsilon>0$, the absolute difference of the new test density from $b_i/(b_i-1)$ times the old test density is therefore bounded by
$$
O_\epsilon\!\left(\frac{m_i'}{|I|}\left(1+U^{1/2+\epsilon}(m_i')^\epsilon\right)\right).
$$
This bound holds for intervals crossing zero by splitting signs and using the prefix bound (G.7). It gives absolute accuracy even for the phases whose principal smooth count is zero. A band-semismooth test with prime bound $U^{o(1)}$ only changes the error by $U^{o(1)}$.

## Integrating the ideal Gaussian

Here are sufficient size conditions, including those of ordinary fixed top bands. For some scale $L_*\to\infty$, assume the two ideal Gaussian marginal width parameters are $T_i=L_*^{1+o(1)}$, the centers have magnitude at most $L_*^{1+o(1)}$, the angle loss $\vartheta=B/\Delta$ is $L_*^{o(1)}$, and the refined periods satisfy $m_i'=L_*^{o(1)}$. For instance take $L_*=V^d$ in a fixed top band with $\log M=O(\log V)$, $b_i\asymp V$, $d\to\infty$, and ideal coefficient parameter $\sigma=V^{O(1)}$ with $\sigma\ge1$. Then $|G(P_i)|\asymp MV$, $T_i\asymp \sigma |G(P_i)| b_i^{d-1}$, and $m_i'\ll MV^4$. Comparability $b_i\asymp V$ contributes at most $O(d)$ to logarithmic sizes. For large top-band smoothness cutoff $Y_1$ one still needs $Y_1<\min b_i$, as in an ordinary top band. These explicit conditions avoid inferring a progression error merely from comparison of value height with $B$ alone.

In marginal coordinates, first restrict to the box $|z_i-F_0(P_i)|\le T_i\log L_*$. The Gaussian mass outside it is $\exp(-\Omega((\log L_*)^2))$ uniformly on each phase, with or without the extra residue. To see this, tile with the corresponding separate-period rectangles. In Mahalanobis coordinates every tile has diameter $O(\vartheta\max_i m_i'/T_i)=L_*^{-1+o(1)}$. Comparing to the continuous Gaussian integral on these tiles gives a uniformly comparable normalizer and the stated tail bound. This argument works for arbitrary translates of the progression. Next partition the capped box into rectangles of side lengths comparable to $T_i L_*^{-1/8}$. Their lengths are $L_*^{7/8+o(1)}$ and their endpoint bound is $L_*^{1+o(1)}$. On each rectangle the Gaussian weight varies relatively by at most $L_*^{-1/8+o(1)}$, since the logarithmic derivative in marginal coordinates is $O(\vartheta^2\log L_*)$ within the capped box. The progression density comparison above gives a power-saving absolute error on every rectangle in every phase, for example using $\epsilon=1/16$.

Inside one rectangle and phase, the two one-coordinate test densities multiply because the unweighted progression is Cartesian. Refining the phase divides its unweighted size by $B$ up to a power-saving relative endpoint error, while the joint test density is multiplied by $B/\phi(B)$ up to a power-saving additive error. Freezing and restoring the Gaussian weights changes either assertion only by a power-saving error. When summed, the errors are weighted by unweighted phase sizes and Gaussian weights, rather than by a bare count of rectangles or phases. The refined ideal Gaussian normalizer is $1/B$ times the original one up to the corresponding relative error. It follows that, for some fixed $c>0$ and all good $q$,
$$
\mathbb E_{\rm ideal}[f_1(z_1)f_2(z_2)\mid q]
=\frac B{\phi(B)}\,\mathbb E_{\rm ideal}[f_1(z_1)f_2(z_2)]
+O(L_*^{-c}).
$$
This is also relative accuracy whenever the unconditioned probability dominates the error, as it does for a probability $\exp(-O(H))$ if $\log L_*\gg H$.

A model that changes **only** the mixture weights of these ideal conditional laws therefore loses only the weight of the bad $q$ classes, up to the unit normalization and the displayed additive error. A one-dimensional discrete Gaussian leading coefficient of parameter $\sigma_*\ge1$ assigns at most $O(1/b_i+1/\sigma_*)$ to any given residue modulo $b_i$. The bound follows by summing the monotone Gaussian tails on a progression of spacing $b_i$ and dividing by the full Gaussian mass, which is $\gg\sigma_*$. Thus these exceptional residues have small total weight even in a much narrower leading-coordinate prior if $\sigma_*\to\infty$.

The result does not assert that the actual law conditional on $q$ has the ideal within-residue distribution. Other kernel obstructions, including restrictions that couple several coefficient residues, may remain after the leading residue is fixed. It also does not handle shared denominators or a band in which a denominator itself is an allowed factor.
