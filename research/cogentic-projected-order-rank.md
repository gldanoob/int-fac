# Projected rank of exact product order relations

An augmented finite-valuation matrix can test certification of products selected after the smooth marks are known. Two unit-logarithm ranks give the exact loss between the finite target span and the certified relation span. The criterion allows a nonzero loss, and it accepts unit logarithms that span a proper subspace of the full logarithm space. In a totally real field of degree at least six, the three prescribed marks alone cannot produce a nontrivial rational scalar identity with balanced exponents. [Collective extraction](cogentic-collective-field-extraction.md) · [Three prescribed marks](cogentic-three-prescribed-marks.md)

## The finite kernel and its target projection

For each chart choose a totally real polynomial field $K_i=\mathbb Q(\theta_i)$ of degree $d_i$, a root $m_i$ of its primitive defining polynomial modulo $N$, and admissible linear marks $a-\theta_i$. Their evaluations $a-m_i$ must be units modulo $N$. As in collective extraction, use known exact finite-prime valuations, including the prescribed leading-coefficient cancellation on nonmonic charts. Also allow rational scalar columns coprime to $N$ in each chart. A rational prime $p$ gives the whole valuation column of $p$, including every prime above $p$ with its ramification index. In the clean linear mark setting any prime above $p$ absent from the marks can be represented by a constraint forcing that scalar coefficient to vanish. One only needs primes present in the chart in order to include every possible nonzero scalar coefficient.

Write $z$ for the tuple of mark exponents $c_{ia}$ and scalar exponents $b_{ip}$. The finite matrix $V$ imposes cancellation of the valuations of
\[
 u_i(z)=\prod_p p^{b_{ip}}\prod_a(a-\theta_i)^{c_{ia}}
\]
in each chart, with the required balance rows. Thus $u_i(z)$ is a unit on $K=\ker_{\mathbb Z}V$. With monic fields and the full valuations no balance row is needed. Other desired linear conditions can be appended to $V$.

The target matrix $T$ records the rational exponent vector of the absolute value of the product of all evaluations,
\[
 \prod_i\left(\prod_p p^{b_{ip}}\prod_a |a-m_i|^{c_{ia}}\right).
\]
For a common evaluation, the mark-sum equations may instead be imposed in $V$. Then $T$ only sums the scalar exponents over the charts. Without the mark-sum equations, coordinates for the full rational product can be computed by gcd refinement of all numerator and denominator labels, together with any specified public bases. The resulting pairwise coprime integers greater than one give multiplicatively independent coordinates and require no factoring of the large residual labels. Signs can be omitted since the order certificate will use an even multiple. [Exact rational label matching](cogentic-rational-root-matching.md)

Choose the desired target coordinates after collecting the labels. To certify relations supported only on those coordinates, append the other rows of $T$ to $V$ and then retain just the desired rows in $T$. To use the rank for the saturated-product factoring bound, the retained bases must generate the quadratic quotient. For that application one can include the [small prime generators](cogentic-saturated-product-certificates.md#use-rational-rank-by-saturating-the-verified-relations) explicitly before gcd refinement.

## Exact rank and polynomial extraction

Let $U$ send an exponent vector to the separate trace-zero log vectors of the units $u_i(z)$ on $K$. It is given by the trace-zero logarithms of the linear marks, with zero columns for rational scalars. Put
\[
 K_0=K\cap\ker T,\qquad
 r_f=\operatorname{rank}_{\mathbb Q}T(K),\qquad
 r_u=\dim_{\mathbb R}\operatorname{span}U(K),\qquad
 r_0=\dim_{\mathbb R}\operatorname{span}U(K_0).
\]
Then the exact projected rank of the torsion identities on the given charts and equations is
\[
 \boxed{\operatorname{rank}_{\mathbb Q}T(K\cap\ker U)=r_f-r_u+r_0.}
\]
Indeed both logarithm images are subgroups of a product of unit-logarithm lattices, so their rational ranks are their real-span dimensions. Their rational spans form nested spaces. Sending $Tz$ to the class of $Uz$ in $\operatorname{span}_{\mathbb Q}U(K)/\operatorname{span}_{\mathbb Q}U(K_0)$ is therefore a well-defined surjective rational map. If the class vanishes, subtract a rational combination of vectors of $K_0$ from $z$ and clear denominators. The resulting multiple has zero unit logarithms and the same target direction. The kernel of this map is exactly the rational span of the displayed torsion projection. For an integer vector therein each $u_i(z)$ is $1$ or $-1$, since the zero trace-zero vector of a unit implies that every embedding has absolute value one. After clearing the mark and scalar denominators, the field identity is an integer polynomial equation divisible by the primitive defining polynomial by Gauss's lemma. It therefore holds at $m_i$ modulo $N$. The denominators evaluate to units, so multiplying the identities and squaring certifies the exponent vector $2Tz$ modulo $N$.

Both integer kernels can be spanned over $\mathbb Q$ by clearing denominators in rational elimination. The resulting logarithm columns lie in the product unit lattice, so the determinant gap and coordinate denominator bound in [collective extraction](cogentic-collective-field-extraction.md) apply to both computed image ranks. A maximal independent list spans a finite-index sublattice of the product unit lattice intersected with its own real span. This gives the coordinate denominator bound even when the real span is proper. The rational logarithm coordinates recovered against such a list from $U(K)$ give a rational matrix for $\ker U$ on $K$. Elimination followed by denominator clearing and direct modular verification returns a list of valid exponent vectors of the displayed rank. These steps take polynomial bit work in the explicit clean chart data under the precision bounds there. A list of size $e^{O(H)}$ can thus be tested together, with no separate order search for each proposed product. The criterion concerns exact chart torsion identities. Modular orders that happen to hold for other reasons can add independent certificate directions.

In particular, at least one exact product direction exists if and only if $r_f>r_u-r_0$. A single public prime can be individually unreachable while some product of public primes lies in the projected space. If the retained bases generate the quadratic quotient and there are $t$ of them, the deficit for saturation is $t-r_f+r_u-r_0$. The loss $r_u-r_0$ counts only directions in unit logarithm space that vary with the target, even if $r_0$ is smaller than the total unit rank.

An entirely finite sufficient test uses $r_f=\operatorname{rank}_{\mathbb Q}\binom{V}{T}-\operatorname{rank}_{\mathbb Q}V$. Since $r_u\le\sum_i(d_i-1)$, if this rank difference exceeds $\sum_i(d_i-1)$ then a nonzero product direction is guaranteed before checking any logarithms. The same inequality with $\sum_i(d_i-1)-r_0$ as the threshold uses any certified lower bound on $r_0$. The finite test needs no distinguished prime in the target span.

## An obstruction with a bounded number of linear marks

In one field let a proposed rational identity use $s$ distinct marks with nonzero exponents $c_a$ and $\sum_a c_a=0$. If $s=1$ the balance already rules it out. For $s\ge2$, suppose the product equals $q\in\mathbb Q^\times$. Every real conjugate of $\theta$ is a zero of
\[
 g(x)=\sum_a c_a\log|x-a|-\log|q|.
\]
The numerator of $g'(x)$ over $\prod_a(x-a)$ has degree at most $s-2$, by balance. It is nonzero since its residues at the marks are the corresponding nonzero exponents. If the conjugates occupy $b$ connected intervals in $\mathbb R\setminus\{a\}$, Rolle's theorem requires at least $d-b$ distinct zeros of $g'$. Consequently any nontrivial balanced identity must have $s\ge d-b+2$. In particular $b\le s+1$ gives $d\le 2s-1$. If all conjugates lie in one interval, the stronger bound is $s\ge d+1$.

Thus any number of charts containing at most three prescribed marks apiece in degrees at least six leaves the exact balanced torsion projection zero. Across charts the unit logarithms are separately indexed, so extra copies of a chart cannot cancel this obstruction. The same conclusion about scalar contributions alone follows directly from finite valuations if the only possible target primes are clean completely split primes and there are fewer than $d$ marks in a chart. These exclusions apply to the supplied small marked sets. They leave open a construction of larger sets meeting the projected-rank inequality.

## Exact finite check

Take $N=119$, $K_1=\mathbb Q(\sqrt2)$ and $m_1=45$. The monic polynomial $X^2-2$ vanishes at $m_1$ modulo $N$ with unit derivative. Use marks $0,-1,1$ and scalar column $2$. The first mark has valuation one at the prime above 2, the rational scalar has valuation two there, and the other marks have norm $-1$. Thus $K$ has a basis given by the field elements $(0-\sqrt2)^2/2$, $-1-\sqrt2$, and $1-\sqrt2$. The absolute rational evaluation labels of these three generators are $45^2/2$, $46$, and $44$. They have independent rational valuation vectors, as witnessed by primes 5, 23, and 11 respectively. The first field element is 1. The two others are non-torsion units with product 1. Hence $r_f=3$, $r_u=1$, $r_0=0$, and the two exact torsion directions have labels $45^2/2$ and $46\cdot44$. The modular checks are $45^2-2=17\cdot119$ and $46\cdot44-1=17\cdot119$. Both are valid product relations even when the labels from the non-torsion generators are considered together. This example checks the rank loss and product projection. Its two directions have trivial modular order, so they supply no splitting witness.
