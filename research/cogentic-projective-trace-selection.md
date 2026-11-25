# Deterministic selection from a fixed trace moment

Let \(L=\log N,\ z=\log L,\ D=(L/z)^{1/3}, H=Dz, V=DH\). The conditional averaging algorithm for [projective marks](cogentic-projective-selection.md) extends to **any fixed number of marks per score term** in the fixed-multiple family \(f_{i,u}=f_i^{(0)}+P_0\ell(X-m)G_u(X,1)\). The [fixed-multiple arithmetic trace estimate](cogentic-fixed-multiple-trace.md) and the selection argument below together give a deterministic complete factoring coefficient at most \((16/9)^{1/3}=1.2114137\ldots\) at \(L_N[2/3]\). This is a manuscript-level improvement on the base papers' published guarantees. The arithmetic estimate bounds the trace, root and diagonal expectations under the fixed-cofactor sieve. This note computes their conditional averages and optimizes the parameters.

## Tensor calculation with partially fixed coefficients

Fix \(k\ge2\). Suppose each term in a score is the product of at most \(k\) bounded unary smooth-value indicators per field and finitely many affine congruence predicates at row primes. Assume their combined modulus \(Q\) in one field is \(B^{O_k(1)}\). Take \(n=d-2,\ d\sim xD,\ \log A\sim cH,\ \log B\sim bH,\ \log W\sim sH\), with \(s\) large enough that \(W/(Q(2A)^k)\gg L^3\). This only changes the constant multiplying \(H\) in \(\log W\). Within each field fix coefficients in descending degree. With the remaining degrees \(0,\ldots,j\), use the exact evaluation identity in the [two-mark proof](cogentic-projective-selection.md#projecting-the-remaining-coefficients). Known high coefficients enter the unary test's constant term, and the free degree-\(j\) projection enters with multiplier \(b_v^{n-j}\) at the mark \(v=(a,b_v)\). The center remains zero in each free coefficient.

Combine predicates at coincident marks, leaving \(h\le k\) distinct slopes \(v_1,\ldots,v_h\). When \(j<h-1\), there are at most \(k-1\) remaining coefficients, so direct enumeration of their truncated intervals costs \((O(L^2 W))^{k-1}=\exp(O_k(H))\). The cases \(h=0,1\) use the previous direct formulas. For all other cases let \(E\) map the free form to its \(h\) integer evaluations. Write
\[
     D_h=\prod_{\nu<\mu}|a_\nu b_\mu-a_\mu b_\nu|,\qquad q'=Q D_h .
\]
The [integral projective kernel lemma](cogentic-projective-kernel.md) gives image index \(D_h\), including \(j=h-1\) when the kernel has rank zero. The congruence sublattice \(\Lambda\) contains \(Q\mathbb Z^{j+1}\), so \(q'\mathbb Z^h\subseteq E(\Lambda)\). Enumerate at most \(q'^h\le\exp(O_k(H))\) residue tuples to determine the exact affine image. As in the two-mark proof, normal forms compute the two indices \(I=[\mathbb Z^{j+1}:\Lambda]\) and \(I_E=[\mathbb Z^h:E(\Lambda)]\), including dependent row prescriptions. Incompatible affine systems give zero.

For each compatible output \(y\), the projected Gaussian mass with its row event is, to uniform relative error \(O(e^{-\Omega(L^6)})\),
\[
 \frac{I_E}{I W^h\sqrt{\det(EE^\mathsf T)}}
            \exp[-\pi y^\mathsf T(EE^\mathsf T)^{-1}y/W^2].
\]
Indeed the fiber kernel contains \(Q\) times all coefficient shifts of \(\prod_\nu(b_\nu X-a_\nu Y)\), with unscaled basis operator norm \(\le(2A)^h\). The Poisson estimate of the kernel lemma applies. The normalizing lattice density also has this relative accuracy. The rank-zero kernel has an exact numerator.

Normalize \(y_\nu\) to \(\xi_\nu=y_\nu/(Wb_\nu^j)\). Let \(T\) be the Gram matrix of the \(h\) real vectors \((1,t_\nu,\ldots,t_\nu^j)\), \(t_\nu=a_\nu/b_\nu\in(0,.8]\). It has top eigenvalue \(O_k(1)\). Cauchy–Binet and the minor on the first \(h\) powers give
\[
           \det T\ \ge\prod_{\nu<\mu}(t_\nu-t_\mu)^2
                   \ge A^{-2h(h-1)} .
\]
In particular \(\|T^{-1}\|\le O_k(A^{2h(h-1)})\) regardless of how many high coefficients have already been fixed. Keep \(|\xi_\nu|\le L^3\) with total probability error \(O_k(e^{-cL^6})\) by the geometric-series bound on \(t_\nu\) and the one-dimensional coefficient tails.

Choose a rational radius \(\rho\asymp_k A^{-h(h-1)}\) such that \(\pi h\rho^2\|T^{-1}\|\le1\). Partition the first \(h-1\) coordinates into intervals of half-width \(\le\rho/2\). For fixed real \(\xi_h\) the entire function \(g(\xi)=\exp(-\pi\xi^\mathsf TT^{-1}\xi)\) has modulus at most \(e\) on the concentric complex polydisk of radius \(\rho\) in the other coordinates. This follows by bounding the quadratic form on their imaginary parts. Its Taylor polynomial through degree \(m_0=\lceil L^4\rceil\) **in each of these \(h-1\) variables** has absolute error at most \(O_k(2^{-m_0})\) throughout the product panel, by summing the Cauchy bounds over all multi-indices with some coordinate exceeding \(m_0\).

For each panel, multi-index \(\alpha\), and compatible residue tuple, the resulting term factors into \(h\) independent one-dimensional sums. The first \(h-1\) sums multiply the respective unary test by the corresponding normalized coordinate power \(((\xi_\nu-u_\nu)/\rho)^{\alpha_\nu}\). The last multiplies its unary test by the Taylor coefficient \(c_\alpha(\xi_h)\) for the given panel centers \(u\). Their product sums the entire tensor term. The number of panels, degrees, and residue tuples combined is \(\exp(O_k(H))\). Every individual array has length \(O(L^3WA^j)\). The total numerical work therefore uses
\[
                         WA^j\exp(O_k(H))
\]
bit operations. Even bounding the number of original lattice-output terms by \((O(L^3WA^j))^h=\exp(O_k(V))\) preserves absolute accuracy \(e^{-\Omega(L^3)}\).

For numerical detail, on a scaled panel the exponent is a quadratic polynomial in its \(h-1\) variables. Each of its nonconstant coefficients has absolute value at most \(\exp(O_k(H+\log L))\). Compute the constant exponential at the center and the Taylor coefficients by differentiating \(\exp(P)\) and using \(\partial_i\exp(P)=(\partial_iP)\exp(P)\). Each new coefficient is obtained from at most \(h\) earlier coefficients and an integer division by an index in \(1,\ldots,m_0\). At most \((h-1)m_0\) successive increases of total degree occur. Thus \(L^{O_k(1)}\) guard bits suffice under the same absolute error and normalization argument as in the two-mark calculation. All \((m_0+1)^{h-1}\) coefficients cost polynomial time in \(L\) at fixed \(k\).

## A sufficient nonnegative trace score

Here is the needed implication of the trace estimates for fixed \(k\). Use the source's \(\widehat C,\mu(F_i),\mu_0,W_0,w_i,D_A,F_\ell\) and protected rows \(l_j\). Write \(A_0\) for the symmetric main-band off-diagonal block on *different physical primes*, with other entries zero, and \(A_{\rm small}\) for the remaining off-diagonal entries involving a target, constant or real row, excluding distinct root rows at the same physical prime. Set \(t=\exp(-z^2/k)\). Take the sum of the following nonnegative quantities:

* \(64(\widehat C-1)^2+C_{\rm bad}\), with the integer \(C_{\rm bad}\) counting multiple and shared roots on the narrow band.
* For each field, \(4(\mu(F_i)-\mu_0)^2/u^2+t^{-12}(\|w_i\|^2/W_0-1)^2\).
* \((4/t)^k\operatorname{Tr}(A_0^k)\), and \(t^{-12}(\|A_{\rm small}\|_F^2+D_A+\ell^{\alpha_s}F_\ell^2+\sum_j\widetilde A_{l_jl_j}^2)\).

The trace is nonnegative because \(k\) is even. If the trace expectation is \(\le e^{-20z^2}\), its displayed scaled contribution has expectation \(o(1)\). The two-point estimates on the other entries can be taken with any fixed \(\exp(-Cz^2)\) tolerance, and the narrow prime band gives \(\mathbf E C_{\rm bad}=o(1)\). The small deterministic generator's relative error in the norm statistic is \(e^{-(1+o(1))z^3}\). The normalized expected score tends to zero with the stated fixed-multiple analogues of these estimates. A score below one implies \(C_{\rm bad}=0\), all mass and target conditions of the [trace peeling proof](cogentic-projective-trace.md#the-target-and-the-diagonal), and \(\|\widetilde A_{\rm off}\|\le t\). Indeed \(\|A_0\|\le t/4\), \(\|A_{\rm small}\|_F<t^6\), and the same-prime off-diagonal blocks have absolute norm \(O(d\widehat C\,\min(B^{1-\delta},\ell)^{-\alpha_s})=o(t)\). The diagonal threshold \(t^{1/4}\), deletion threshold \(t^{1/8}\), and mass threshold \(t^{1/4}\) in that proof are then available. Its bounds involving \(D_A\) and \(\ell^{\alpha_s}F_\ell^2\) are supplied by \(t^{12}\), and every protected individual diagonal is below \(t^6\).

Expanding the trace cycles gives a finite sum over \(k\) row labels, \(k\) marks and a bounded number of root rows per label. All other score terms need at most two marks. Thus there are \(\exp(O_k(H))\) separated terms with at most \(k\) distinct marks in either of the two fields. Their total absolute coefficient weight is \(\exp(O_k(H))\) by the [reciprocal-density and fixed power bounds](cogentic-universal-score-sampler.md), and their actual real values admit the same finite-interval arithmetic as in the two-mark score. The averaging algorithm computes the conditional mean and selects one integer coefficient at a time, with the previously proved uniform projection error holding on every in-box prefix. Each candidate scan costs \(WA^n\exp(O_k(H))\), including both independent fields, all terms and all \(\exp(O(H))\) one-coordinate choices. This gives deterministic cost \(\exp((xc+o(1))V)\) at every strict feasible fixed-\(k\) schedule.

## Parameter limit

Put \(v=xc,\ S=v+1/x\). For the fixed-multiple local progression theorem take \(x>1/v\). Fix \(c>2b\) and an \(\eta>0\) with \(2c-2S/(3b)>(1+\eta)b\), then take a fixed even \(k>2/\eta\) and enough Gaussian-width slack for all its row conditions. Necessarily \(S<\tfrac32 b(2c-b)<9c^2/8\), whence
\[
                      v^2>\frac89(vx^2+x)>\frac{16}{9v}.
\]
Conversely any \(v>(16/9)^{1/3}\) admits feasible schedules arbitrarily close to \(x=1/v,\ c=v/x,\ b=c/2\), by approaching the two inequalities from their strict sides and taking a suitably small fixed \(\eta\). Rational approximations preserve all margins. Interleaving the countably many fixed rational choices gives the limiting coefficient as in the previous selection theorem. The [integer and numerical replay](../experiments/cogentic-projective-trace-selection.py) checks 36 restricted three-mark contractions against direct summation, with maximum absolute difference \(3.2\times10^{-14}\), and four strict rational schedules down to \(24229/20000=1.21145\). Its Gram inverses and parameter margins use exact rational arithmetic.
