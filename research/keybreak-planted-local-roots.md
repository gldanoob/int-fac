# Planting known small-prime divisors in a KeyBreak field

One can impose small-prime root conditions while preserving the native affine form, the exact value \(F(r,Q)=N\), and the leading coefficient height. In a terminal box this cheaply produces a known smooth divisor of logarithmic size \((1+o(1))d\log d\) on average. The reduction is lower order on the norm-height scale. The existing KeyBreak success proof uses a different coefficient law. [KeyBreak, equation (G.4) and Lemma H.1](https://crypto.sjtu.edu.cn/factoring.pdf#page=105) · [Terminal height and work scales](keybreak-higher-degree-terminal-budget.md)

## The affine CRT construction

Use the source's \(G=QX-rY\) and \(F=F_0+2GR\), with \(F_0(r,Q)=N\) and \(R\) a binary form of degree \(d-1\). For each odd prime \(p\le d\) with \(p\nmid NQ\), let \(s=r/Q\bmod p\) and \(k_p=\lfloor d/p\rfloor\). The form
\[
L_p(X,Y)=Y\prod_{j\in\mathbb F_p\setminus\{s\}}(X-jY)
\]
uses arbitrary integer representatives of \(j\). It vanishes modulo \(p\) on the \(p\) projective directions other than \((s:1)\). Its value at \((r,Q)\) is a unit. Set
\[
F\equiv u_pY^{d-pk_p}L_p^{k_p}\pmod{p^{k_p}},
\]
where \(u_p\) scales the right side to evaluate to \(N\bmod p^{k_p}\). The difference from \(F_0\) vanishes at \((r,Q)\) over \(\mathbb Z/p^{k_p}\mathbb Z\). Since \(Q\) is a unit, the change of variables \((X,Y)\mapsto(G,Y)\) is invertible there. The zero evaluation therefore determines a unique class of \(R\) through division by \(2G\).

Combining these classes gives one class per coefficient modulo \(J=\prod_p p^{k_p}\). Draw the coefficients independently in their prescribed classes using a Gaussian of the original parameter \(\sigma\). Here \(\log J=O(d\log d)=O(H)\) and \(\log \sigma\asymp DH\), with \(D=(\log N/\log\log N)^{1/3}\), \(H=D\log\log N\), and \(d\sim\delta D\). Each class has spacing \(J\ll\sigma\), so each Gaussian has its original scale. A direct sampler works in the coset coordinate, where the parameter is \(\sigma/J\). For example, truncate at parameter times the input bit length, propose a uniform index in that interval, and accept with the scalar Gaussian weight. The expected proposal count is polynomial in the input bit length, and polynomial caps with rounded weights can give negligible sampling failure. This avoids rejection of entire unplanted field draws. The coefficient-height cap, with the source's polynomial padding, need not grow by \(J\). Modulo two the polynomial is still \(F_0\), preserving the simple irreducibility argument. If a nontrivial content is found it divides \(N\), giving a proper split under the ordinary height bound.

Trial divide through \(d\) before this construction, at polynomial bit cost, if the original small-prime pass has not already done so. For sufficiently large native inputs \(Q>d\). Thus every continuing composite input uses all odd primes \(p\le d\) and
\[
\log J=\sum_{3\le p\le d}\lfloor d/p\rfloor\log p
       =d\log d+O(d)\sim(\delta/3)H.
\]
The sum follows from \(\sum_{p\le d}\log p/p=\log d+O(1)\) and the prime-product bound \(\sum_{p\le d}\log p=O(d)\). The required forms and CRT representatives have polynomial bit complexity.

## Exact divisibility and the best universal exponent

At a primitive mark \(P=(a,b')\), every planted prime with \(p\nmid G(P)\) gives \(p^{k_p}\mid F(P)\). If \(p\mid G(P)\), the point is proportional to \((r,Q)\bmod p\) and \(F(P)\) is a unit there. Therefore the explicitly known divisor is
\[
J_P=\prod_{p\nmid G(P)}p^{k_p}.
\]
For a reference law uniform on the primitive projective classes at \(p\), the exceptional probability is \(1/(p+1)\). The source terminal box uses prime denominators \(b'\gg d\), so its uniform affine directions instead give \(1/p\) to leading order. In fact for a fixed environment and an allowed denominator, the numerator requirement \(r b'-Qa\in[MV/16,MV/8]\) gives an interval of integers \(a\) of length \(\Theta(V)\). The excluded nonprimitive \(a\)'s are only \(O(1)\) multiples of \(b'\). Among the remaining \(a\)'s the exceptional fraction is \(1/p+O(1/V)\), uniformly in \(p\le d\). Consequently, before the smoothness filters, the mean loss \(\mathbb E(\log J-\log J_P)\) is \(O(d)\) since \(\sum_p\log p/p^2<\infty\). Both reference laws give \(\mathbb E\log J_P=d\log d+O(d)\). A box with additional input-unit filters, or a set selected by terminal smoothness, needs its own incidence comparison.

There is a sharp local improvement to the universal exponent \(k_p\). For a fixed \(p\), put \(k=\lfloor d/p\rfloor\) and \(L=k+v_p(k!)\). At each finite direction \(j\ne s\), use the \(k\) factors \(X-(j+p\ell)Y\), \(0\le\ell<k\). At infinity use \(Y-p\ell X\) for the same indices. Multiply the resulting degree-\(pk\) form by \(Y^{d-pk}\) and normalize at \((r,Q)\) modulo \(p^L\). At every primitive mark on a planted direction one can divide by its unit coordinate in \(\mathbb Z_p\). The corresponding \(k\) factors then give \(p^k\) times a product of \(k\) consecutive \(p\)-adic integers. This product is divisible by \(k!\) in \(\mathbb Z_p\), by density of the integers and the integral binomial polynomial. The other branches are units before the extra power of \(Y\).

To prove optimality, interpolate a binary form of degree \(d\) at \(d+1\) normalized marks distributed as evenly as possible among the \(p\) planted directions. In a branch receiving \(n_j\le k+1\) marks use the same direction representatives with consecutive indices \(0,\ldots,n_j-1\). The determinant of two marks from distinct branches is a unit. For the mark with index \(\ell\) in branch \(j\), the product of its determinants with the other marks has valuation
\[
n_j-1+v_p(\ell!)+v_p((n_j-1-\ell)!)\le k+v_p(k!).
\]
Every numerator determinant in homogeneous Lagrange interpolation at \((r,Q)\) is a unit. If all the interpolated values were divisible by \(p^{L+1}\), every summand at \((r,Q)\) would be divisible by \(p\), contradicting \(F(r,Q)=N\). This proves that \(L\) is maximal for universal divisibility on the non-target directions. Using this optimum for the CRT increases \(\log J\) by only \(O(d)\), from \(v_p(k!)\le k/(p-1)\).

## Effects on a terminal search

Dividing a known \(J_P\) out before testing smoothness is exact as long as the cutoff includes the planted primes. A complete factor list restores the removed factors. In the one-mark affine value lattice the step changes from \(2|G(P)|\) to \(2|G(P)|J\) upon planting, because evaluation of \(R\) at a primitive mark is onto and the coefficient variation is now in \(J\mathbb Z^d\). After dividing by \(J_P\) the step is \(2|G(P)|J/J_P\). Thus each successful planting cancels its own extra progression modulus, while a missed planting retains it. The same sublattice scaling applies to the separate steps before any joint density comparison.

The saving in logarithmic height is at most \(\log J=O(H)\) against a terminal logarithmic norm height of order \(DH\). At a cutoff with logarithm \(bH\), the Dickman argument shifts by at most a constant. On that model this gives an \(O(\log D)\) improvement in the log smoothness density, leaving the leading stationary coefficient unchanged. Ordinary unconditioned marks realize the full leading shift on average, but that does not compare the incidence after smoothness selection. In addition, the planted coefficient law forces many discriminant primes and changes the progressions used in the source's one- and two-point estimates. A lower bound on accepted proposals, a verified small-prime ideal treatment, and a success and work comparison would be needed for an expected running-time claim. The unconditional gain here is a known smooth divisor with polynomial setup and no leading enlargement of the coefficient width.
