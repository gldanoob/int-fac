# Exact sparse coefficient images and the support needed to sample them

A degree-$e$ homogeneous form needs only its first and last $h$ powers to realize the unrestricted integer evaluation image at any $h$ primitive rational marks. The result extends to finitely many prescribed congruences and the common-root divisibility condition. It describes the infinite coefficient lattice. A short coefficient menu can have this lattice image while giving very different probabilities to the evaluation classes. [Integral projective evaluation](cogentic-projective-kernel.md) · [Variable-multiple Gaussian](cogentic-variable-multiple-lattice.md)

## The two ends of the coefficient basis

Let $e\ge h-1$ and let $v_i=(a_i,b_i)$ be primitive pairwise nonproportional marks. Let $\mathcal S_h$ be the integer span of $X^jY^{e-j}$ for $0\le j<h$ or $e-h<j\le e$, omitting overlaps. Then
\[
 E(\mathcal S_h)=E(\mathbb Z[X,Y]_e)
\]
for their simultaneous evaluation $E$. The full image has index $D_h=\prod_{i<j}|a_i b_j-a_j b_i|$ by the integral kernel lemma. It suffices to find, for each prime $p$, a sparse minor with exactly the $p$-valuation of $D_h$.

At $p$, split the marks into $l$ with $p\nmid b_i$, using coordinates $t_i=a_i/b_i$, and $h-l$ with $p\mid b_i$, using $w_i=b_i/a_i\in p\mathbb Z_p$. Divide each row by the unit $b_i^e$ or $a_i^e$ in its own chart. Take the first $l$ columns and the last $h-l$ columns, ordering the latter by ascending powers of $w$. Take successive Newton divided differences in each chart. The removed determinants are the two within-chart Vandermonde products. Each accounts for exactly the $p$-valuation of the corresponding within-chart factors of $D_h$, and all cross-chart determinants are $p$-units.

Modulo $p$, the divided-difference matrix on the lower-left block vanishes. Its monomials there are $w^{e-j}$ with $j\le l-1$, and a divided difference of order at most $h-l-1$ leaves positive homogeneous degree, since $e-j-(h-l-1)\ge1$. The two diagonal blocks use consecutive powers in their own charts and are triangular with unit diagonal. All normalized entries are integral, as divided differences of monomials are complete homogeneous polynomials. The resulting determinant is a unit. This proves equality of the integer images by their indices.

For a bounded number of root tests, append $(r,1)$ for each integer representative of a row residue and use the sparse lemma for the enlarged set of marks, merging equal rational nodes. Equality at these appended nodes is stronger than the required congruence. For a derivative modulo $q$, also append $(r+q,1)$, since $F(r+q,1)-F(r,1)\equiv q\,\partial_X F(r,1)\bmod q^2$. For $N\mid F(m,1)$ include $(m,1)$ as one more node. For the fixed-multiple family apply the argument to $G$ in the perturbation $(X-mY)G(X,Y)$ and substitute the same fixed multiplier at the prescribed nodes. All these exact image transfers use a bounded number of powers at the two ends of the free coefficient basis. For a modular comparison alone modulo $Q=\exp(O(H))$, take a box in an integral basis of the chosen sparse lattice, with coordinate widths $\exp(C H)$ for a sufficiently large fixed $C$. Elementary interval residue counts reproduce the uniform compatible modular distributions to exponentially small error. Intersecting with the common-root congruence can enlarge that basis, so this statement gives no coefficient-height guarantee.

## Evaluation classes for a fixed multiple

For the variable-multiple family with $e\ge h$, write $A_h=E(\mathbb Z[X,Y]_e)$ and $B_h=E((X-mY)\mathbb Z[X,Y]_{e-1})$. At primitive marks with $a_i-b_i m$ units modulo $N$, the projected variable-multiple lattice is $A_h$. Its original coefficient lattice has the digit basis $R,(X-mY)Y^{e-1},\ldots$ where $R(m,1)=N$. It follows that
\[
 A_h/B_h=\langle E(R)\rangle,\qquad |A_h/B_h|=\prod_i |a_i-b_i m|.
\]
The order follows because the unrestricted degree-$e$ and degree-$(e-1)$ images have the same index $D_h$, and the fixed-multiple evaluations multiply coordinate $i$ by $a_i-b_i m$. This calculation does not require the coordinate multipliers to be pairwise coprime. The quotient class of a field is specified by its multiple of $N$ at $m$.

On the full Gaussian schedule the output class in this cyclic quotient is nearly uniform. Normalize the $i$th output by $b_i^e$ and use the covariance of the projected real Gaussian. On the ordinary Farey marks the normalized covariance has inverse norm $\exp(O_h(H))$ from the first $h$ powers and their Vandermonde determinant. Before whitening, the normalized fixed-multiple lattice contains the $h$ independent low-power columns with entries $(a_i/b_i-m)(a_i/b_i)^j$, $0\le j<h$. After whitening their basis norm is $m\exp(O_h(H))$. The full Gaussian width $W=m\exp(sH+o(H))$ with enough fixed slack gives Poisson equidistribution over all translates of the fixed-multiple image lattice. The uniform projected-Gaussian error then gives the same quotient law on the coefficient Gaussian. [Projection and Poisson bounds](cogentic-narrow-band-moments.md#any-fixed-number-of-marks)

A menu using $K$ multiples of $N$ reaches at most $K$ of these classes. Comparing it in total variation with the uniform quotient at any fixed error below one requires $K\gg\prod_i |a_i-b_i m|=\exp((h/x+o(1))V)$. In the fixed-multiple family there is a separate obstruction if the comparison preserves the whole law of even one normalized mark output. Its largest atom is bounded by a constant times $(Wb_i^{e-1})^{-1}=\exp((-xc+o(1))V)$ by Gaussian projection, so a support of size $\exp(O(H))$ misses almost all of that law. Exact lattice surjectivity and exact small congruences thus do not establish the clean smoothness probabilities for a short enumerable menu.

These are restrictions on distribution comparisons. The score uses particular smoothness predicates, and neither support estimate gives a lower bound on searches that exploit those predicates directly. The fixed-multiple conditional estimator uses their arithmetic bounds in genuinely long progressions instead. [Deterministic conditional trace selection](cogentic-projective-trace-selection.md) · [Averaged fixed-multiple improvement](cogentic-fixed-multiple-averaged-trace.md)

An exact finite check computed the gcd of the sparse minors and the full determinant index for 80 primitive mark tuples with one to four marks.
