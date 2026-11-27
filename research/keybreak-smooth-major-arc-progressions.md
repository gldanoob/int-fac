# Major-arc smooth probes on a single progression

The principal term of the Dirichlet GRH progression estimate admits a rational-denominator saving and an independent saving in the residual frequency. In particular, use the progression phase \(\beta=m\theta=a/q+\delta\), where \((a,q)=1\), and write

\[
D=|\delta|X/m,\qquad T=q(1+D).
\]

The bound below pays no polynomial factor in the support period \(m=V^{O(1)}\) after normalization. It applies to each phase modulo \(m\), including those with a forced divisor. The denominator \(q\) here measures the phase on a progression step. [Minor-arc probes and Gaussian partial summation](keybreak-smooth-minor-arc-probes.md)

## A single-progression bound

Assume \(m=V^{O(1)}\), \(X=V^{\omega(1)}\), \(\log\log X=o(\log V)\), \(y=X^{o(1)}\), and \(\log y/\log\log X\to\infty\). Fix \(\eta<1/2\) and assume \(T\le X^\eta\). For integers \(n\equiv r\bmod m\), let \(g=(r,m)\), \(m'=m/g\), and \(U=X/g\). If \(g\) has a prime factor greater than \(y\), the ordinary smooth probe at \(n\ne0\) is zero. Otherwise, for every interval \(I\subset[-X,X]\), under the pinned Dirichlet GRH estimate its character sum satisfies

\[
\left|\sum_{\substack{n\in I,\ n\equiv r\bmod m\\n\ne0,\ P^+(|n|)\le y}}
           e(n\theta)\right|
\ll\
 \frac{\Psi(U,y)}{m'}\,
      V^{o(1)}T^{o(1)}q^{-1}(1+D)^{-1/2}
 +O_\tau\!\left(TX^{1/2+\tau}(mq)^\tau\right)
\tag{1}
\]

for each fixed \(\tau>0\), uniformly in the residue. The first term can be omitted if \((q,m')>1\). For \(T\le V^C\) with fixed \(C\), the factor \(T^{o(1)}\) is \(V^{o(1)}\). Relative to the unweighted progression scale \(X/m=U/m'\), the main term is the smooth density \(\Psi(U,y)/U\) times this saving. The error in (1) has arbitrary fixed power slack from the pinned GRH estimate. [KeyBreak, (G.7)–(G.8)](https://crypto.sjtu.edu.cn/factoring.pdf#page=106)

To see the principal term, first consider positive prefixes and put \(n=gu\), \(u=r'+m'k\), \(r'=r/g\). The phase, up to a constant, is \(e(ak/q+\delta u/m')\). Apply (G.8) to each residue \(k\bmod q\), hence each \(u\) residue modulo \(m'q\), and use partial summation for \(e(\delta u/m')\). The total error is \(O_\tau(q(1+D)X^{1/2+\tau}(mq)^\tau)\). The principal progression count depends only on the gcd of the residue with \(m'q\). If \(p\mid(q,m')\), then \(p\nmid u\) since \((r',m')=1\). The gcd is unchanged as the \(p\)-part of \(k\bmod q\) varies with its other components fixed. The additive character on that \(p\)-part is primitive and sums to zero. This proves the asserted vanishing.

If \((q,m')=1\), the additive rational phase is \(e(a' u/q)\) times a constant, where \(a'\equiv a(m')^{-1}\bmod q\). Group the refined residues by \(h=(u,q)\). Writing \(u=hv\) and summing their primitive additive phases gives the Ramanujan sum \(\mu(q/h)\). At a raw prefix endpoint \(x\le X\), the principal term, up to its constant phase, is exactly

\[
\frac{1}{\phi(m')}\sum_{\substack{h\mid q\\P^+(h)\le y}}
 \frac{\mu(q/h)}{\phi(q/h)}
 \sum_{\substack{v\le x/(gh),\ P^+(v)\le y\\(v,m'q/h)=1}}
       e(\delta hv/m').
\tag{2}
\]

The formula also covers \(q=1\). Negative prefixes follow by reflection of the interval and conjugation of the phase, with the same divisibility and frequency conditions.

Expand the coprimality constraint in (2) by Möbius inversion over \(j\mid m'q/h\), retaining only \(y\)-smooth \(j\). Each resulting unrestricted smooth sum has endpoint \(x/(ghj)\) and additive frequency \(\delta hj/m'\). Apply Harper’s Theorem 1 with rational denominator \(1\) and normalized offset \(D_x=D x/X\). Since \(h j\le m'q\), its size hypothesis is satisfied throughout \(\sqrt X\le x\le X\). Indeed at \(x=X\) the quantity \(y^3ghj(1+D_x)^2/x\) is at most \(m y^3 T^2/X=X^{2\eta-1+o(1)}\), and at \(x=\sqrt X\) it is \(X^{\eta-1/2+o(1)}\). Between them the quantity is a positive multiple of \(1/x+2D/X+(D/X)^2x\), which is convex. The range of smoothness cutoffs in Harper holds uniformly, since \(x/(ghj)\ge X^{1/2-\eta-o(1)}\). Shorter raw prefixes are bounded by \(O(\sqrt X)\).

Let \(\alpha=\alpha(U,y)=1-o(1)\) be the saddle point for the global endpoint. The smooth scaling estimate gives

\[
\Psi(x/(ghj),y)\ll ((X/x)hj)^{-\alpha}\Psi(U,y).
\]

Harper’s oscillatory factor is \((1+D_x)^{-1/2}V^{o(1)}T^{o(1)}\). Because \(1+D_x\ge(x/X)(1+D)\) and \(\alpha>1/2\) eventually, the product of these two bounds is at most \(\Psi(U,y)(hj)^{-\alpha}(1+D)^{-1/2}V^{o(1)}T^{o(1)}\). The harmless losses absorb the logarithmic factors and Harper’s saddle-point correction, uniformly in the shorter endpoints. Finally,

\[
\sum_{h\mid q}\frac{h^{-\alpha}}{\phi(q/h)}
       \sum_{j\mid m'q/h}j^{-\alpha}
\ \le\ q^{-\alpha} V^{o(1)}T^{o(1)}
\ =\ q^{-1} V^{o(1)}T^{o(1)}.
\]

For this use \(h^{-\alpha}/\phi(q/h)=q^{-\alpha}(q/h)^\alpha/\phi(q/h)\), then bound the divisor counts and totient ratios. Also \(1/\phi(m')\le V^{o(1)}/m'\). The bound on all prefixes gives the bound on every interval by subtraction. [Harper, Theorem 1](https://arxiv.org/pdf/1408.1662#page=7) · [Saddle point and smooth scaling, §2.1](https://arxiv.org/pdf/1408.1662#page=12)

## Relative scale for the top Gaussian

One sufficient geometry for relative use of (1) has each endpoint \(X_i\) at most \(V^{o(1)}\) times that coordinate's conditional Gaussian width and at least the absolute cutoff of the Gaussian box. Assume the center lies within \(O(1)\) in Mahalanobis norm of the origin and the Gaussian cutoff tail is negligible. The top formulas in KeyBreak give conditional widths comparable to \(T_i/\vartheta\), raw caps \(X_i=8n^{11}T_i\), and center shifts at most \(\operatorname{poly}(d)2^d/\sigma\) times the marginal widths \(T_i\). These give the required geometry for \(\vartheta=V^{o(1)}\), \(d=o(\log V)\) and \(\sigma=V^{2-\epsilon}\) with fixed \(\epsilon<2\), at the stated top sizes. In the two coordinates \(X_i=V^{d+o(d)}\), assume \(y_i=V^{c_i+o(1)}\) for fixed \(c_i>0\), with \((\log\log X_i)^2=o(\log V)\), as in the fixed top bands. The smooth density at \(X_i/g_i\) is within \(V^{o(1)}\) of the density at \(X_i\), uniformly for \(g_i\le V^C\). Indeed the global Dickman approximation applies in this range. Changing the endpoint by a factor \(V^{O(1)}\) changes \((\log X_i)/\log y_i\) by \(O(1)\), which changes the logarithm of the Dickman density by \(O(\log\log X_i)=o(\log V)\). [KeyBreak, (G.23) and the top Gaussian widths](https://crypto.sjtu.edu.cn/factoring.pdf#page=110) · [Hildebrand’s smooth-density estimate](https://arxiv.org/pdf/1408.1662#page=12) · [Hildebrand–Tenenbaum, Corollary 2.4](https://tenenb.perso.math.cnrs.fr/PPP/Survey_friables.pdf#page=15)

An elementary lower bound handles good phases with a modulus containing smooth primes. Write \(\Psi_{\mathrm{cop}}(U,y)\) for the smooth count coprime to \(m'\). Each smooth integer throughout the prefix is \(av\), where \(a\) is coprime to \(m'\) and \(v\) is supported on the primes of \(m'\) at most \(y\). For \(W=\exp(\sqrt{\log V})\), the number with \(v>W\) is at most

\[
\ll \Psi(U,y)W^{-1/10}
       \prod_{p\mid m'}(1-p^{-(\alpha-1/10)})^{-1}
=o(\Psi(U,y)).
\]

This follows from the same smooth scaling bound. For example, eventually \(\alpha-1/10\ge 3/4\), and the logarithm of the product is \(O((\log V)^{1/4})\) by bounding the sum of inverse \(3/4\)-powers over at most \(O(\log V)\) distinct integers. The other \(v\)'s take at most \(W\) values. Thus \(\Psi_{\mathrm{cop}}(U,y)\ge V^{-o(1)}\Psi(U,y)\). The argument works at smaller endpoints comparable to the conditional widths.

On a Cartesian phase where both forced divisors are smooth, take a rectangle near zero with each side comparable to the conditional Gaussian width. The weights are bounded below on a suitable such rectangle under the center hypothesis, and its area is at least \(V^{-o(1)}\) times the Gaussian area. Apply (G.8) and the coprime lower bound to the positive coordinate prefixes in this rectangle. The ideal conditional smooth probability in that phase is at least \(V^{-o(1)}\) times the product of the two global smooth densities. A phase with a nonsmooth forced divisor contributes zero. Use the uniform prefix bounds in (1) with Gaussian partial summation. In a coordinate with an untested phase, use the ordinary smooth prefix count as an absolute bound, so both smooth densities remain in the estimate. Dividing by the phase normalizer and comparing to the ideal conditional probability therefore gives a relative principal-term bound of \(V^{o(1)}T^{-1/2+o(1)}\) per certified coordinate. For a Gaussian mixed with a linear phase whose derivatives in Mahalanobis coordinates are \(V^{o(1)}\), its differentiated weights only change this loss by \(V^{o(1)}\). The normalized GRH error is \(T X^{-1/2+O(\tau)+o(1)}\) per certified coordinate before the mode sum. [Gaussian partial summation and normalization](keybreak-smooth-minor-arc-probes.md#gaussian-insertion-and-the-weighted-mode-count)

The all-integer denominator probe uses a geometric sum. For \(q>1\), \(q|\delta|=o(1)\) in the stated range, so \(\|\beta\|\ge1/(2q)\) and interval sums are \(O(q)\). Relative to the progression scale this is \(X^{-1+\eta+o(1)}\). For \(q=1\) one instead gets \(O((X/m)\min(1,D^{-1}))\), with \(D=0\) interpreted as giving the trivial bound.

For an individual progression far from the origin or a thin correlated conditional direction, \(X_i/\text{width}\) can be a fixed power of \(V\). Prefix estimates still hold, but an offset that oscillates across the endpoint scale can be essentially constant across the occupied width. The relative small-offset assertion for the Gaussian needs the width conditions above or a separate local estimate.

If a probe first divides by a prescribed \(s\), let \(d_0=(s,m)\). A branch with \(d_0\nmid r\) is empty. Otherwise \(n=su\) leaves an affine progression in \(u\) of period \(m/d_0\), with endpoint \(X/s\) and raw frequency \(s\theta\). Its progression frequency is \((s/d_0)\beta\), so the normalized offset \(D\) is unchanged but the rational denominator becomes \(q/(q,s/d_0)\). If the divisor is already forced and \(s\mid m\), both quantities are unchanged. In other branches a large rational denominator can disappear, as with \(m=1\), \(\theta=1/p\), and the restriction \(p\mid n\). On that branch the phase is constant.
