# Smooth leading coefficients in reduced square classes

Let \(N\) be odd, \(\Delta=-4N\), \(L=\log N\), \(D=(L/\log L)^{1/3}\), and \(H=D\log L\). Write \(Y=\exp((y+o(1))DH)\) for a fixed \(y>0\). Under Dirichlet GRH, a uniform square in the proper form class group of discriminant \(\Delta\) has \(Y\)-smooth reduced leading coefficient with probability
\[
 \exp\!\left(-\bigl(1/(6y)+o(1)\bigr)H\right)
\]
on the rough-input branch \(\min_{p\mid N}\log p/H\to\infty\), \(\omega(N)=o(H)\). The lower bound already holds for squarefree leading coefficients prime to \(2N\) in \([\sqrt N/4,\sqrt N/2]\). The proof counts classes; it assumes a uniform class before squaring and does not construct that sampler. [Rough-input branch](keybreak-private-shape-work.md#ensuring-the-count-suffices-on-every-input)

## Genus as a finite Dirichlet condition

Let \(K=\mathbb Q(\sqrt{-N})\), and let \(\mathcal C\) be the proper ideal class group of the order \(\mathbb Z[\sqrt{-N}]\), equivalently the primitive proper form class group of \(\Delta\). Write \(h=|\mathcal C|\) and \(g=|\mathcal C/\mathcal C^2|\). In the ring class field, complex conjugation acts on \(\mathcal C\) by inversion. The field fixed by \(\mathcal C^2\) therefore has elementary abelian Galois group of order \(2g\) over \(\mathbb Q\). Its quadratic characters are unramified outside \(2N\), since the ring class extension over \(K\) is unramified outside the conductor. They all have conductor dividing \(8\operatorname{rad}_{\rm odd}(N)\), where \(\operatorname{rad}_{\rm odd}\) denotes the product of odd prime divisors. In particular \(g\le 2^{\omega(N)+1}\). For a split prime outside \(2N\), the two prime ideals give inverse classes, which agree modulo squares. The rational Frobenius at that prime in the elementary abelian quotient is exactly this class. This gives the genus condition for arbitrary \(\Delta=-4N\), including nonfundamental discriminants, without assuming a fundamental-discriminant genus formula for the order. [Ring class correspondence and Lemma 9.3](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf#page=180)

By character orthogonality and the Dirichlet GRH prime estimate, each specific class in \(\mathcal C/\mathcal C^2\) occurs with density \(1/(2g)\) among rational primes when the splitting condition is included. Uniformly for a dyad of size \(Z=\exp(\Theta(\log Y))\), its count is \(\gg Z/(g\log Z)\) provided \(\log g=o(\log Y)\). Indeed the weighted error of the character average is \(O(\sqrt Z\log^2(NZ))\), independent of the number of characters after averaging. For the lower bound below, the factor \(1/g\) from one prime restriction cancels with the size \(h/g\) of the square subgroup. There is no need to prescribe genus independently on every prime.

## Lower count by reserving one prime

Put \(T=\sqrt N/2\), \(W=\log Y\), and choose a fixed small \(\epsilon>0\). Let
\[
 k=\left\lceil\frac{\log T}{(1-2\epsilon)W}\right\rceil,\qquad
 \mu=\frac{\log T}{k}.
\]
Draw the first \(k-1\) split primes from the broad log band \([\mu-\epsilon W/2,\mu+\epsilon W/2]\). Weight each prime by \((\log p)/(pW)\le1/p\). The total weight in the band is \((1+o(1))\epsilon/2\) by the quadratic character prime estimate. More precisely, partition the log band into \(k^2\) equal cells. Partial summation with Dirichlet GRH gives total weight \((1+o(1))\epsilon/(2k^2)\) uniformly in every cell, with an exponentially small relative error on the \(W\) scale. The discretized log laws are therefore uniformly comparable to independent uniform real logs, at a total multiplicative cost \(\exp(o(k))\). Within matching cells each pair differs by at most \(\epsilon W/k^2\), which loses only \(O(\epsilon W/k)\) in the sum.

The sum of \(k-1\) independent uniform logs has an even unimodal density around \((k-1)\mu\), by convolution. Its standard deviation is \(O(\epsilon W\sqrt{k})\). Chebyshev and unimodality give probability \(\gg k^{-1/2}\) in the centered interval of radius \(\epsilon W/8\): the average density of that centered interval is at least the average density of a fixed-standard-deviation interval. After discretization the band primes therefore give log sum within \(\epsilon W/4\) of \((k-1)\mu\) with at least this order of mass. Tuples with repetitions have negligible mass since each atom is \(\exp(-\Omega(W))\). Thus for the retained ordered distinct tuples of product \(P\),
\[
 \sum_P \frac1P \ \ge\ \exp(-O_\epsilon(k))\,k^{-1/2},
\]
where the sum is over tuples and counts repeated products with multiplicity.

For each tuple choose the final prime in \([T/(2P),T/P]\). The endpoints have logarithm \(\mu+O(\epsilon W)\) and are below \(W\). Demand the split Frobenius class inverse to the product of the first \(k-1\) genus classes. The uniform dyad estimate above supplies \(\gg T/(P g W)\) choices, even after excluding the first \(k-1\) primes. Then \(A=Pp\) is squarefree, \(Y\)-smooth and in \([T/2,T]\), split at every prime, with trivial product genus. Counting each \(A\) at most \(k!\) times gives at least
\[
 \frac{T}{g W k!}\exp(-O_\epsilon(k))\,k^{-1/2}
\]
distinct leading coefficients.

There are \(2^k\) roots \(b\bmod A\) of \(b^2\equiv-N\bmod A\). Choose each representative with \(|b|<A/2\). Each form \([A,2b,(N+b^2)/A]\) is primitive since \((A,2N)=1\), and strictly reduced since \(2|b|<A<(N+b^2)/A\). Distinct tuples \((A,b\bmod A)\) give distinct reduced forms and hence distinct classes, using uniqueness of the normalized reduced representative. The corresponding ideal class modulo squares is the product of the chosen prime ideal classes above the primes in \(A\). The sign choices at those primes give inverses and so do not alter the genus. Every counted form is a square class. [Form and ideal correspondence and reduction](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf#page=111)

The ordinary imaginary quadratic class number formula, including its conductor factor, gives \(h\le\sqrt N\,\operatorname{poly}(\log N)\) uniformly for these orders. Dividing by \(h/g\), even using only one root per \(A\), gives the lower bound with log loss at most \((1/(6y(1-2\epsilon))+o(1))H\) by Stirling. Let \(\epsilon\) decrease through fixed positive choices to get the claimed leading lower loss. This lower argument only needs \(\log g=o(\log Y)\) for the final prime distribution.

## Normalization and upper count

Writing \(\Delta=f^2 d_K\) with \(d_K\) fundamental, the class number formula is a bounded unit factor times
\[
 \sqrt{|\Delta|}\,L(1,\chi_{d_K})
               \prod_{p\mid f}(1-\chi_{d_K}(p)/p).
\]
The conductor product and its inverse are bounded by powers of \(\log N\), by the elementary prime harmonic bound or by ordering the distinct prime divisors. Under Dirichlet GRH, \(L(1,\chi_{d_K})\) and its inverse are also bounded by powers of \(\log N\), uniformly even when \(d_K\) is fixed. For example, the GRH character prime-sum bound and partial summation give a bounded tail to the log Euler product beyond \((\log N)^K\) for fixed sufficiently large \(K\). The remaining prime harmonic sum is \(O(\log\log\log N)\). It follows that \(h\) is \(\sqrt N\) up to polylogarithmic factors for all these discriminants. On the rough branch \(g=\exp(o(H))\), so \(h/g=\sqrt N\exp(o(H))\). A uniform element of \(\mathcal C\) squared is exactly uniform on \(\mathcal C^2\), since every fiber of squaring has the same cardinality. [Order class number formula](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf#page=147)

For the upper bound count all primitive reduced forms of discriminant \(\Delta\), including all genera and allowing \(A\) to share primes with \(N\). Reduction gives \(A\le\sqrt{|\Delta|/3}\). The number of \(b\bmod A\) with \(b^2\equiv-N\bmod A\) is at most \(4\cdot 2^{\omega(A)}\gcd(A,N)^{1/2}\). For a prime power \(p^e\) dividing \(A\), if \(e\le v_p(N)\) the local root count is \(p^{\lfloor e/2\rfloor}\). Otherwise remove the even valuation of \(N\) if the equation has a solution, and use the bound of two roots of a unit at an odd prime power or four at a power of two. The canonical reduced form uses at most one \(b\) per congruence class, up to a bounded edge convention.

Apply Rankin's bound with \(\beta=1-(\log D-2\log\log D)/\log Y\). The leading factor is
\[
 (\sqrt{|\Delta|/3})^\beta
   =\sqrt N\,\exp\!\left(-\bigl(1/(6y)+o(1)\bigr)H\right).
\]
For primes not dividing \(N\), the logarithm of the resulting Euler product is \(O(\sum_{p\le Y}p^{-\beta})=o(H)\), by partial summation with the prime counting upper bound. For primes dividing \(N\) the local nonconstant terms are at most \(2/(p^{\beta-1/2}-1)\), independent of the multiplicity in \(N\). Their total is \(o(1)\) on the rough branch. Division by \(h/g\) proves the matching leading upper loss. This covers nonfundamental orders and arbitrarily high valuations in \(N\) on the stated branch.

The supply theorem charges neither a uniform class sampler nor a method to turn these forms into verified public parity rows. Those are separate algorithmic steps. It does show that the smooth-leading-coefficient loss itself survives exact reduction and the square-class restriction.

## Field-good prime bands and staged prefixes

The preceding single-prime correction uses all primes in its final dyad. It need not survive deletion of field-bad top parents, since they could include that entire genus class. The central-index recipe (H.20) instead mixes genus over all its prime positions, and yields the staged lower bound on the same field.

Use a fixed finite staged recipe with total \(m=\Theta(D)\) prime positions and the usual H.20 log allocations and complete dyadic bands; keep the upper product target below \(\sqrt N/2\). Write \(S_j\) for the sum of one-coordinate inverse-density coefficients through the first \(j\) stages, and \(S\) for the full sum (these are half the two-coordinate \(w_i\) sums in the staged notation). The original H.20 count before split or genus restrictions has lower size \(\sqrt N\exp(-(S+o(1))H)\). Suppose these bands satisfy the pinned quantitative G.12 hypotheses. Its expected bad-parent fraction, together with Markov and the polynomial number of bands, gives a single field with bad fraction at most \(D^{-B_0}\) in every band for any fixed \(B_0\). Include any other already justified \(O(D^{-B_0})\) deletions, such as the relevant elliptic eligibility exceptions. [Quantitative good-parent event](keybreak-public-quadratic-window.md#there-are-enough-modular-square-products-before-the-root-restriction) · [H.20 staged bookkeeping](keybreak-private-band-stages.md#the-shapes-counted-below)

In each dyad, first restrict to primes splitting in \(K\) and prime to \(2N\). This keeps an asymptotic half of the primes by GRH. For any nontrivial character of \(\mathcal C/\mathcal C^2\), its mean over the split primes before deletion is \(\exp(-\Omega(DH))\). Indeed, extend it to the elementary abelian quotient over \(\mathbb Q\). Averaging a character over the split restriction gives half the sum of that extension and its product with the splitting character. Both are nontrivial. Dirichlet GRH bounds their prime sums uniformly. The deleted fraction of split primes remains \(O(D^{-B_0})\), so the normalized mean on the retained split primes is \(O(D^{-B_0})\).

Now fix an ordered tuple of band choices at the H.20 central indices, and sample a retained split prime independently at each position. On any nontrivial genus character the product bias is at most \((CD^{-B_0})^m\). By orthogonality the probability of principal genus is \(g^{-1}(1+O(g(CD^{-B_0})^m))=g^{-1}(1+o(1))\), uniformly in the tuple and field on the good event. Here \(\log g=o(H)\) and \(m\log D\asymp H\). Repeated prime choices have probability at most \(O(m^2/\min|\mathcal P|)=\exp(-\Omega(DH))\), where \(\mathcal P\) ranges over the retained split-prime sets of the dyads. This is negligible relative to \(g^{-1}\), so deleting all repeats does not change the leading bound. Summing the surviving ordered tuple counts and dividing by the original within-stage factorials retains the H.20 product lower bound, multiplied by \(g^{-1}\exp(-o(H))\). The splitting restriction itself loses only a constant at each prime position. Reduction is strict, and the resulting \(A\)'s are prime to \(2N\). Dividing the class count by \(h/g\) gives probability at least \(\exp(-(S+o(1))H)\) for a uniform square class. This proves the full lower supply for field-good staged shapes, without requiring a good parent in any individually selected genus class of a single dyad.

For upper bounds on every prefix, reject any output with \(\gcd(A,N)>1\), after checking for a proper gcd. For unit \(A\), the number of possible reduced middle coefficients is at most \(4\cdot2^{\omega(A)}\). If the certified pairwise coprime band parts are \(d_i\ge T_i\) for \(i<j\), write \(A=m_0\prod_{i<j}d_i\). There are \(O(D)\) prime factors in the product of the certified parts since all those primes exceed \(\exp(\Omega(DH))\) and \(A=O(\sqrt N)\). Therefore
\[
 2^{\omega(A)}\le e^{O(D)}2^{\omega(m_0)},\qquad
 \sum_{m_0\le U}2^{\omega(m_0)}\le U(1+\log U),
\]
the latter by summing \(2^{\omega(m_0)}=\sum_{d\mid m_0}\mu(d)^2\). Count the residual integers with this weight first, then drop the restrictions on how the individual parts were certified. The result is at most
\[
 \sqrt N\,e^{o(H)}
 \prod_{i<j}\sum_{d_i\ge T_i,\ P^+(d_i)\le Y_i^*}\frac1{d_i}.
\]
The original per-band Rankin bounds give \(\exp(-(S_j+o(1))H)\) for the product. After division by \(h/g\) this is the desired prefix probability. It counts even those retained unit \(A\)'s with no verified full factorization and works for every stage, independently of whether a recognition procedure fails to find some factors. It makes no claim about the distribution of the later parity vectors. [Original prefix bounds and band thresholds](keybreak-private-band-stages.md#testing-and-counting-a-prefix)
