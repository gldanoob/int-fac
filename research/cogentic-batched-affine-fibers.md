# Simultaneous discrete-Gaussian fibers for Cogentic's two-mark scores

Let $L=\log N$, $D=(L/\log L)^{1/3}$, $H=D\log L$ and $V=DH$. In the [square-root-contour schedule](cogentic-deterministic-two-thirds.md) each polynomial has two integer perturbation coordinates $u_0,u_1$, with independent centered discrete Gaussians of widths $S_0=UA$ and $S_1=U$. Here $A,B=\exp(O(H))$ and $\log U=(v+o(1))V$. This note computes all conditional expectations of one- and two-mark terms over the second coordinate at every possible value of the first in $U\exp(O(H))$ bit operations. A choice of each coordinate by conditional expectation then takes this same time. The [explicit separable score and coefficient algorithm](cogentic-conditional-score.md) supply the remaining hypothesis of the selection theorem. [Primary paper, square completion and peeling in §§9.4–10](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=48)

## A batched computation for one field

Use centered integer coordinates $t=u_0-\bar u_0$, $k=u_1-\bar u_1$. A mark $a\in[1,A]$ depends on the second perturbation only through $x=t+ak$, because $f_u(a)=f^{(0)}(a)+P_0\ell(a-m)(\bar u_0+a\bar u_1+x)$. Its indicator that $|f_u(a)|$ is squarefree and built from the permitted prime band is therefore a one-variable function $F_a(x)\in\{0,1\}$. The values needed for any mark have $|x|\le 3\lceil L_0^2\rceil A U=:C_0$. Compute them by exact polynomial evaluation and trial division by the allowed primes, costing $U\exp(O(H))$ across the required marks. Any prescribed congruences on $f_u(r)$ or $f_u'(r)$ are affine in $(t,k)$ modulo the row prime. Their joint indicator is an arbitrary explicitly computable function $G(t\bmod Q,k\bmod Q)$ for a product $Q\le B^{O(1)}$. This includes overlapping or incompatible conditions.

Fix two distinct marks $1\le a<b\le A+1$, let $\Delta=b-a$, and set $x=t+ak$, $y=t+bk$. All assignments correspond bijectively to
$$
 x=r+\Delta i,\qquad y=r+\Delta j,\qquad
 t=r+b i-a j,\qquad k=j-i,\qquad 0\le r<\Delta.
$$
The exact square completion
$$
 k^2=\frac{t^2}{ab}-\frac{x^2}{a\Delta}+\frac{y^2}{b\Delta}            \tag{1}
$$
makes the Gaussian $g(k)=\exp(-\pi k^2/U^2)$ separable into a factor at $t$ and one at each mark. For each triple $r,i_0,j_0$ with $i_0,j_0\bmod Q$, the congruence indicator $G$ is constant. If it vanishes skip the triple. Otherwise form the two arrays
$$
 \begin{aligned}
 A_{bi}&=F_a(r+\Delta i)\exp\!\left(\frac{\pi(r+\Delta i)^2}{a\Delta U^2}\right)
                &&(i\equiv i_0\pmod Q),\\
 B_{-aj}&=F_b(r+\Delta j)\exp\!\left(-\frac{\pi(r+\Delta j)^2}{b\Delta U^2}\right)
                &&(j\equiv j_0\pmod Q),
 \end{aligned}
$$
retaining only mark arguments in $[-C_0,C_0]$. One ordinary integer-indexed convolution gives the coefficient at $t-r$ for all $t$. Translate the indices, sum the surviving triples, and multiply at index $t$ by $\exp(-\pi t^2/(abU^2))$. By (1) the resulting value equals
$$
  \sum_k g(k) F_a(t+ak)F_b(t+bk) G(t,k)
$$
on the padded mark support. Single-mark terms can use a second mark at $a+1$ with constant value 1. Coincident mark terms combine into one indicator; a term with no marks uses any two constant indicators.

Within the official first-coordinate interval $|t|\le L_0^2 A U$, the padding contains every value from the official second-coordinate rectangle. The sum over all $k$ outside the rectangle $1\le k+\bar u_1\le2\bar u_1$ is $O(U\exp(-cL^4))$, uniformly in $t$. The same bound covers an endpoint shift by one. Normalize by the sum of $g(k)$ on the official interval, which is $\asymp U$, to obtain the actual conditional probability to $O(e^{-cL^4})$.

There are $O(AQ^2)=\exp(O(H))$ triples per condition. Shift negative indices to zero; the largest needed polynomial length is $O(AC_0)=U\exp(O(H))$. The absolute logarithms of the three Gaussian factors in (1) are bounded by $O((C_0/U)^2)=\exp(O(H))$. Individual factors may be large, but their values can be rounded to dyadic rationals with $P=\exp(O(H))$ fractional bits so that all convolution coefficients have absolute error $\le e^{-2L^3}$. More explicitly take $P$ a sufficiently large multiple of $L^3+(C_0/U)^2+\log(2UAC_0Q)$. A summand contains at most three rounded factors, each of magnitude $\le\exp(O((C_0/U)^2))$, and there are at most $U\exp(O(H))$ summands per returned fiber. Pi, exponentials and products at this precision have cost polynomial in $P,L,C_0/U$. For instance use binary-scaled exponentiation from a Taylor series on a bounded argument with guard digits accounting for the displayed absolute-magnitude bound. Clearing the dyadic denominator gives nonnegative integer coefficients of $O(P)$ bits. Packing them into slots of length $O(P+\log(2AC_0))$ bits, multiplying integers, then unpacking implements the convolution without carry between coefficients in $U\exp(O(H))$ bit operations using quasi-linear integer multiplication. The tables of the second-coordinate weights, the first-coordinate weights, and their normalizing sums cost the same. This proves the time bound and a final uniform absolute error $O(e^{-L^3})$ per one-field conditional probability. [Schönhage–Strassen integer multiplication](https://doi.org/10.1007/BF02242355)

## Four-coordinate selection

Suppose a nonnegative sufficient score $S(u,v)$ for a pair of polynomials has expectation $o(1)$ under the independent discrete Gaussians, and $S<1$ inside the official rectangle ensures the extracted target exponent. Assume $S$ expands into at most $\exp(O(H))$ terms
$$
             c_j F_j(u)G_j(v)
$$
with computable real coefficients of total absolute sum $\exp(O(L))$. Here each $F_j,G_j$ consists of at most two smooth-value indicators and finitely many affine row conditions of combined modulus $B^{O(1)}$. Functions identically 1 are allowed. Coefficients can be signed. Assume all coefficients to absolute error $e^{-L^2}$ cost at most $U\exp(O(H))$ once per generator prime. Conditioning on the whole official rectangle preserves $\mathbf E S=o(1)$ because its probability tends to one and $S\ge0$.

For each polynomial and term compute its conditional-probability table, then sum against the known first-coordinate weights to get its unconditional probability on the rectangle. To choose $u_0$, combine the $u$-tables at each index with the unconditional $v$ weights and the coefficients. Among the returned values choose a minimum, then fix $u_1$ by a direct scan over its interval using the same unconditional $v$ weights. Continue with the $v$-tables at each $v_0$ and a direct scan at each $v_1$. Each direct evaluation explicitly checks the smooth and congruence predicates for its fixed coordinates. Each of the four stages takes $U\exp(O(H))$ bit operations. A genuine conditional average is a convex combination of the next conditional values, and the uniform absolute score errors are $o(1)$ after the signed sums. Thus each chosen coordinate increases the true conditional expectation by at most $o(1)$; at the end the certified order extractor succeeds for all sufficiently large $N$. The search may simply return its verified result and otherwise use the specified finite fallback.

For Cogentic Proposition 10.1, a suitable score combines the scaled squares of the total mass defect, the factor-base masses and the two logarithmic prime-weight norms, the masses of shared or repeated roots, the diagonal defects, their weighted squares, and the off-diagonal squared Gram entries with the source's peeling thresholds. Membership in an actual row is enforced by the affine root conditions. Each squared Gram sum expands over two marks independently in each field. The source's one- and two-point bounds, Markov inequalities and deterministic peeling implication verify that the correctly scaled sum has expectation $o(1)$ and that $S<1$ suffices. The [explicit score and coefficient proof](cogentic-conditional-score.md) gives the expansion, the implication and the required deterministic real-coefficient approximations in $\exp(O(H))+O(A\sqrt m\,\mathrm{poly}(L))=O(U\exp(O(H)))$ operations. It permits a uniform score error $o(1)$ by increasing the fixed precision constant. The plain four-coordinate bound in the [parameter proof](cogentic-deterministic-two-thirds.md) uses no such selection.

Combining these results, each fixed strict parameter choice (3) now has cost $\exp((v+o(1))V)$, and the single-algorithm limit gives coefficient $(32/3)^{1/3}=2.2012848\ldots$. The initial divisions through $B$, exact prime tests, $\ell$-loop and recursive verified splitting add lower-order factors. The register width of the tables is exponential in $H$ and their length is $U\exp(O(H))$; this is a worst-case bit bound, with no claim that the parameters are practical.

The [finite exact replay](../experiments/cogentic-gaussian-fibers.py) checks 1,500 individual fiber masses across 60 mark and congruence cases. It uses the Gaussian $2^{-ab\Delta k^2}$, whose three factors in (1) are rational powers of two with integer exponents. Packed integer convolution agrees exactly with direct enumeration in every case, including 796 positive masses.
