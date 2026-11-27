# Discrete major-arc counts for the native two-mark dual

Take distinct primitive marks \(P_i=(a_i,b_i)\) with distinct prime denominators \(b_i\asymp V\), determinant \(\Delta\ne0\), and \(b_i\nmid 2G(P_i)\). Use forms of degree \(d-1\) and put \(h=d-2\) and \(B=b_1b_2\). Write \(G_i=G(P_i)\) and \(m_i=2|G_i\Delta|\) for the two Cartesian periods of the raw evaluation image. In particular, \((m_i,b_i)=1\). In the native kernel basis of shifted copies of \((b_1X_0-a_1Y_0)(b_2X_0-a_2Y_0)\), retain short dual modes indexed by \(s\in[-S,S]^h\cap\mathbb Z^h\) with \(2S<\min_i b_i\). The results are upper bounds on the number of modes and hence on their total Gaussian weight. [Native kernel basis and Fourier probes](keybreak-narrow-smooth-probes.md) · [Cartesian periods](keybreak-top-residue-conditioning.md)

## Exact conductors

For the integer basis matrix \(A\), solve \(A^{\mathsf T}v_s=s\) by taking the last two coordinates of \(v_s\) to be zero and using triangular back substitution. The resulting lift is linear in \(s\). If the last nonzero coordinate is \(s_{j-1}\), then \(v_s\) is supported before \(j\) and \(v_{s,j-1}=s_{j-1}/B\). The periodic phase \(e(\langle v_s,c\rangle)\) factors through the raw evaluation residues modulo \(b_i^j\). Indeed, for an evaluation difference vanishing in both residues, subtract integral multiples of the shifted kernel vectors to clear the first \(j\) coefficients in order. At each step the next coefficient is divisible by \(B\), by reducing the two residual evaluations at their respective primes. The subtracted vectors pair integrally with \(v_s\), and the remaining coefficient vector pairs to zero. Both evaluation residues can vary independently by CRT applied to the leading coefficient. Thus the phase factors as a constant times \(e(\alpha_1(s)z_1+\alpha_2(s)z_2)\) on raw values \(z_i\), with rational \(\alpha_i(s)\) modulo one. [Prefix residues and the full affine image](keybreak-top-residue-conditioning.md#a-fixed-prefix-up-to-nearly-half-the-degree)

For distinct short modes \(s,s'\) let \(j\) be one plus their last differing index. Testing the vector with entry one at coefficient index \(j-1\) gives phase \(e((s_{j-1}-s'_{j-1})/B)\), of order \(B\). In coordinate \(i\) this test vector changes the raw residue by \(2G_i a_i^{d-j}b_i^{j-1}\), so its coordinate phase has order at most \(b_i\). The two orders are coprime, hence each is exactly \(b_i\). It follows that \(\alpha_i(s)-\alpha_i(s')\), and also \(\beta_i(s)-\beta_i(s')\) for \(\beta_i(s)=m_i\alpha_i(s)\), have exact reduced denominator \(b_i^j\) in **each** coordinate. Each map \(s\mapsto\beta_i(s)\) is therefore injective into \(b_i^{-h}\mathbb Z/\mathbb Z\).

## An upper bound for small heights

Work in one coordinate, suppress its subscript, and set \(L=X_i/m_i\) for the raw height \(X_i\). Use
\[
\mathcal T(\beta)=\min_{q\ge1,\ (a,q)=1}q(1+L\|\beta-a/q\|),\qquad M=2S+1.
\]
All quantities here are for the periodic raw phase. If \(s\ne0\) has depth \(j\), an exact approximant has denominator \(b^j\), and a nonexact one has circular distance at least \(1/(qb^j)\). Consequently
\[
\mathcal T(\beta(s))\ge \min(b^j,1+L/b^j)\ge \min(b,1+L/b^h). \tag{1}
\]
For the native marginal height \(X_i\asymp\sigma |G_i|b_i^{d-1}\), the ratio \(L/b_i^h\asymp\sigma b_i/(2|\Delta|)\) includes the full period. At \(\sigma=V^{2-\epsilon}\) with \(0<\epsilon<1\) and \(|\Delta|\ll V^2\), (1) is \(\gg V^{1-\epsilon}\) for every nonzero mode.

For \(T\ge1\), pick one minimizing approximant for each mode with \(\mathcal T\le T\), and let \(u=\min(h,\lfloor\log_b T\rfloor)\). It suffices to consider \(q\le b^h\), since the exact approximant is available. Group by \(v=v_b(q)\in\{0,\ldots,u\}\) and set
\[
k_v=\max\bigl(\{0\}\cup\{0\le k\le h:2T^2 b^k<L b^v\}\bigr).
\]
If two modes in a group share their suffix after the first \(k_v\) coordinates, their frequency difference has denominator dividing \(b^{k_v}\). The rational difference of their approximants has denominator dividing \(\ell=\operatorname{lcm}(q,q')\). The two differences are within \((T/L)(1/q+1/q')\). Unless they coincide modulo one, their separation is at least \(1/(b^{k_v}\ell)\), which contradicts the strict inequality defining \(k_v\) because
\[
\ell(1/q+1/q')=(q+q')/\gcd(q,q')\le 2T/b^v.
\]
When the differences coincide, their common frequency has denominator dividing \(b^v\), by the exact conductor identity. Hence the suffix and the first \(\min(v,k_v)\) entries determine the mode within its group. This yields the count
\[
\#\{s:\mathcal T(\beta(s))\le T\}
\le \min\left(M^h,\ \sum_{v=0}^{u}M^{h-k_v+\min(v,k_v)}\right). \tag{2}
\]
The \(k_v=0\) case retains all the coordinates, regardless of the strict inequality. Grouping denominators by their prime valuation lets the common denominator factor improve the allowable prefix length by the same amount as the extra free coordinates.

Another bound uses only the one-dimensional grid and the short-mode conductors. At most \(M^u\) modes have an exact approximant with \(q\le T\). For the remaining modes and any candidate \(q\le T\), put \(g=(q,b^h)\). If the approximant is nonexact then \(q\beta\) must be a nonzero grid point with \(\|q\beta\|\le (T-q)/L\), or else the exact fraction \(\beta\) already has denominator at most \(T\). Each such grid point has \(g\) preimages. Summing their bound \(2g\lfloor(T-q)b^h/(gL)\rfloor\) over \(q\) gives
\[
\#\{s:\mathcal T(\beta(s))\le T\}\le M^u+T^2b^h/L. \tag{3}
\]
One can use the better of (2), (3) and the exclusion (1), separately in either coordinate.

## Top-scale consequences

In a fixed top band let \(X=V^d\), \(d\to\infty\), and take the usual short truncation \(M=V^{\epsilon+o(1)}\) at \(\sigma=V^{2-\epsilon}\). Suppose \(m_i=X^{o(1)}\), \(L_i=X^{1+o(1)}\), and the number of valuation groups is \(X^{o(1)}\). For \(T=X^t\) with fixed \(t\ge0\), the number in (2) is at most
\[
X^{\epsilon\min(1,2t)+o(1)}.
\]
Indeed for \(t<1/2\), ignoring rounding, \(k_v/d=\min(1,1-2t+v/d)+o(1)\), so the fraction of free coordinates is at most \(\max(2t,v/d)+o(1)=2t+o(1)\). For \(t\ge1/2\) use all \(h\) coordinates. A box of heights \(\mathcal T_i\le X^{t_i}\) has the smaller of the two coordinate bounds. The conclusion also holds on any fixed compatible semismooth divisor branch \(n_i=p u_i\) with \(p=X^{o(1)}\) coprime to \(b_i\). For \(g=(m_i,p)\) the new progression has period \(m_i/g\), progression phase \((p/g)\beta_i\), and scale \(Lg/p\). The new phase still has every exact difference conductor. A subpower number of branches can be summed when the Fourier estimate has fixed power slack. [Progressions after dividing by a semismooth cofactor](keybreak-smooth-minor-arc-probes.md)

To apply a height bound to the full Gaussian phase, include the linear factor \(e(-\langle v_s,x_z\rangle)\) from the real minimum-norm lift \(x_z\). In the nonthin top geometry its raw frequency shift \(\delta_i\) satisfies \(X_i|\delta_i|\ll \vartheta\sigma\|v_s\|=X^{o(1)}\), where \(\vartheta\) is the angle loss between the evaluation rows. This uses the marginal width \(X_i\) and conditional width \(\asymp X_i/\vartheta\). The two heights before and after the shift differ by a factor at most \(1+X_i|\delta_i|\) in either direction, by the triangle inequality applied to every approximant. Thus fixed-power thresholds can absorb the shift. [Short lift and its Euclidean norm](keybreak-narrow-smooth-probes.md#a-family-of-modes-with-vanishing-main-terms)

For example, the minor-arc probe with certified power heights \(X^{t_i}\) gives a normalized two-coordinate bound \(X^{-(\min(t_1,\eta_0)+\min(t_2,\eta_0))/2+o(1)}\) with a fixed cap \(\eta_0<1/2\). A height lower bound of one can use the trivial bound in that coordinate. For \(\epsilon<1/2\) choose \(\epsilon<\eta_0<1/2\). Grouping into sufficiently fine fixed bins, the count above gives power-saving absolute summation over modes with either height at least \(X^\gamma\), for any fixed \(\gamma>0\). If both \(t_i\) are below the cap, the count exponent is at most \(\epsilon(t_1+t_2)\). If only one is capped, the exponent of count minus savings is bounded by the larger of \(-\eta_0/2\) and \((2\epsilon-1)\eta_0\). If both are capped it is at most \(\epsilon-\eta_0\). The binning can use the next higher endpoint in (2) and the lower endpoint in the Fourier estimate. This leaves the modes with both heights below \(X^\gamma\). The lower bound (1) supplies a scale in \(V\) for them, but the fixed-power Fourier error does not by itself control the sum on that scale. [Fourier savings on one or both coordinates](keybreak-smooth-minor-arc-probes.md#gaussian-insertion-and-the-weighted-mode-count)

Exact rational checks used the marks \((2,7),(3,11)\), \((4,7),(5,11)\), and \((4,11),(8,13)\), with \(G(X_0,Y_0)=101X_0-3Y_0\), \(h\in\{3,4\}\), and \(S=2\). For each mode the two frequencies were reconstructed by testing leading-coefficient CRT lifts of the residue pairs \((1,0)\) and \((0,1)\). The resulting phases agreed on every coefficient basis vector. Exact minimization over denominators up to each tested height gave 234 coordinate, scale, and threshold checks of (1)–(3), including injectivity within the valuation groups.
