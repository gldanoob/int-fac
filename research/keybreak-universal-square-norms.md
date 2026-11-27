# Universal square norms force a large discriminant or lattice index

Let \(\mathcal O\) be an order in a number field \(K/\mathbb Q\) of degree \(d\), and let \(N>1\) be odd and squarefree. Suppose every \(a\in\mathcal O\) has norm a square modulo each \(p\mid N\), allowing zero. Then \(d\) is even and

\[
N^{d/2}\mid \operatorname{disc}(\mathcal O).
\]

More generally, let \(\Lambda\subseteq\mathcal O\) be a full-rank integral lattice containing \(1\), and impose the same norm condition on every \(a\in\Lambda\). Write \(I=[\mathcal O:\Lambda]\) and \(N_*=\prod_{p\mid N,\ p>d^2}p\). Then \(d\) is even and

\[
N_*^{d/2}\mid I\operatorname{disc}(\mathcal O).
\]

If \(\Lambda\) is itself an order, one can take \(N_*=N\). These claims use regular multiplication on the ambient order and apply to nonmaximal orders. The even-degree condition follows already from \(\operatorname{Nm}_{K/\mathbb Q}(t)=t^d\) for integer scalars \(t\).

## Local norm and trace

Fix an odd prime \(p\) and set \(A=\mathcal O/p\mathcal O\). Write \(\overline A=A\otimes_{\mathbb F_p}\overline{\mathbb F}_p\) as a product of \(s\) local Artinian algebras of dimensions \(m_1,\ldots,m_s\). Each has residue field \(\overline{\mathbb F}_p\). Let \(\ell_i\) be its residue evaluation on \(\overline A\). The \(\ell_i\) are independent linear forms since the quotient map onto the product of residue fields is onto. Each local multiplication by \(x\) is \(\ell_i(x)\) times the identity plus a nilpotent endomorphism. Thus the reduction of the integral norm and trace satisfies

\[
\operatorname{Nm}(x)=\prod_{i=1}^s\ell_i(x)^{m_i},
\qquad
\operatorname{Tr}(xy)=\sum_{i=1}^s m_i\ell_i(x)\ell_i(y).
\]

In particular, the trace-form nullity is at least \(d-s\), with equality when all \(m_i\) are nonzero in \(\mathbb F_p\). The Gram matrix is the reduction of the integral trace Gram matrix of \(\mathcal O\). By Smith normal form, \(v_p(\operatorname{disc}\mathcal O)\ge d-s\). The construction uses the finite algebra structure of \(A\) even if it has nilpotents. [Artinian factors and geometric evaluations](https://stacks.math.columbia.edu/tag/0FHN)

For the full-order hypothesis, work over \(\mathbb F_p\) and decompose \(A\) into local factors with residue fields \(\mathbb F_{p^f}\). If a factor has dimension \(fm\), its norm on \(x\) is \(\operatorname{Nm}_{\mathbb F_{p^f}/\mathbb F_p}(\bar x)^m\). This follows from a composition series of its regular module, whose \(m\) simple factors are the residue field. If \(m\) is odd, surjectivity of the finite-field norm gives a residue with nonsquare norm, and we may set all other residues to \(1\). Therefore every \(m\) is even. After base change that factor has \(f\) geometric components of length \(m\). All \(m_i\ge2\), so \(s\le d/2\). Conversely, even local lengths give squares by the same norm formula. For a maximal order the local lengths are the ramification indices.

## Restricting to a sublattice

Let \(V\subseteq A\) be the image of \(\Lambda\) modulo \(p\). It is an \(\mathbb F_p\)-subspace containing \(1\), and Smith normal form gives \(v_p(I)\ge\operatorname{codim}(V)\). Partition the \(s\) evaluations by equality on \(V\otimes\overline{\mathbb F}_p\), and let \(c\) be the number of classes. If \(p>c^2\), we can choose \(b\in V\) that distinguishes all \(c\) restrictions. Each difference of two distinct restrictions has a proper kernel on \(V\), so the excluded fraction is at most \(\binom c2/p<1\).

The polynomial \(F_b(T)=\operatorname{Nm}(T+b)\in\mathbb F_p[T]\) has exactly \(c\) distinct geometric roots. The multiplicity at each is the sum of the \(m_i\) in its evaluation class. Every \(F_b(t)\) with \(t\in\mathbb F_p\) is a square by the lattice hypothesis. For the quadratic character \(\chi\) extended by zero, this gives \(\sum_t\chi(F_b(t))\ge p-c\). If some multiplicity were odd, the complete Weil bound would give an absolute upper bound of \((c-1)\sqrt p\). These bounds conflict since \(p-c-(c-1)\sqrt p=(\sqrt p+1)(\sqrt p-c)>0\). Thus every class has even total multiplicity. Conversely, even totals imply the norm restricted to \(V\) is a square polynomial over \(\mathbb F_p\): the monic factors are normalized by \(\ell_i(1)=1\), and Frobenius permutes the distinct restrictions and their half-multiplicities. [Weil, *On Some Exponential Sums*](https://doi.org/10.1073/pnas.34.5.204)

Let \(u=\#\{i:m_i\text{ odd}\}\). The equations equating evaluations within each class have rank \(s-c\) on \(\overline A\), by independence of the \(s\) original evaluations. Each class contains an even number of odd lengths, so its contribution \(|\text{class}|-1\) is at least half that number. Consequently

\[
v_p(I)\ge\operatorname{codim}(V)\ge s-c\ge u/2,
\qquad
d=\sum_i m_i\ge 2s-u.
\]

Combining gives \(v_p(\operatorname{disc}\mathcal O)+v_p(I)\ge d-s+u/2\ge d/2\). Multiplying the divisibilities uses \(p>d^2\) as a uniform sufficient condition. The local proof uses only \(1\in V\), so it also applies at any eligible prime where an integer scalar prime to \(p\) lies in the lattice.

If \(V\) is a subalgebra, its image in \(A_{\rm red}\) is a product of finite fields. The geometric embeddings of this image are exactly the classes of restricted evaluations. Frobenius makes the total length constant on the embeddings of each residue field, and the restricted norm is a product of finite-field norms with those total lengths as exponents. The same independent residue choices as for \(A\) force all exponents to be even at every odd prime, without a size condition. In particular this applies when \(\Lambda\) is an order. The single index factor in the bound comes from the codimension estimate. The discriminant of the lattice itself satisfies \(\operatorname{disc}(\Lambda)=I^2\operatorname{disc}(\mathcal O)\).

A small-prime exception really can occur for an additive lattice. Take \(p=3\) totally split in a degree-four field, for example \(\mathbb Q(\sqrt{13},\sqrt{37})\), and let \(\mathcal O\) be its maximal order. In \(A=\mathbb F_3^4\), the hyperplane \(x_1+x_2=x_3+x_4\) contains \(1\) and all its elements have square norm. Indeed, if every coordinate is nonzero, each is \(1\) or \(-1\). A pair sum in \(\mathbb F_3\) determines the number of minus signs in that pair, so the two pairs together have even parity. Norms with a zero coordinate vanish. The preimage lattice has index \(3\), while \(v_3(\operatorname{disc}\mathcal O)=0\), so their valuation sum is \(1<d/2\).

## Coefficient height and scope

Let \(\theta\in\mathcal O\) be an integral primitive element with monic minimal polynomial \(f\) of degree \(d\) and coefficient height \(H\ge1\). Since \(\operatorname{disc}(f)=[\mathcal O:\mathbb Z[\theta]]^2\operatorname{disc}(\mathcal O)\), the discriminant bound and Mahler's inequality give

\[
N_*^{d/2}\le I\,d^d M(f)^{2d-2}
\le I\,d^d(1+dH^2)^{d-1}.
\]

Here \(M(f)=\prod_\alpha\max(1,|\alpha|)\) over the roots of \(f\). The constants follow by applying Hadamard to the Vandermonde matrix and applying Jensen and Parseval to bound \(M(f)\le\|f\|_2\). With \(I=1\) and the full-order hypothesis, \(N_*=N\), and

\[
H\ \ge\ \frac{N^{d/(4(d-1))}}
{d^{d/(2(d-1))}\sqrt{d+1}}.
\]

In the lattice setting the height bound has the additional divisor \(I^{1/(2d-2)}\). In particular, \(\log H+\log d=o(\log N_*)\) requires \(\log I\ge(d/2-o(d))\log N_*\). The same inequality also bounds the height of a primitive integral generator belonging to a nonmonogenic order. [Mahler, *An inequality for the discriminant of a polynomial*](https://doi.org/10.1307/mmj/1028999140)

The tradeoff can be sharp at a prime. In a ramified quadratic maximal order the full order has square norms modulo the odd ramified prime and discriminant valuation \(1\). For the index contribution, \(\mathcal O=\mathbb Z[i]\) and \(\Lambda=\mathbb Z+N\mathbb Z i\) have square norms on \(\Lambda\) modulo \(N\), index \(N\) and discriminant prime to \(N\). For a native monogenic order \(\mathbb Z[\theta]\) and \(p>d^2\), there is a smaller sufficient test than the entire order: check \(\operatorname{Nm}(t+\theta)\) for every \(t\in\mathbb F_p\). The geometric evaluations of \(\theta\) are already distinct, so the same complete character sum forces all multiplicities to be even. A bounded set of marks can behave differently. For instance \(\theta=i\) has square norm at \(t=0\) for every odd prime, while its discriminant is prime to every odd prime. The argument gives a constraint on universal square norms, and leaves open whether a sieve or other restricted selection of marks produces enough square norms for its own purposes.
