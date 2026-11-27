# Prime multipliers and the two-mark residue phases

Prescribing \(F(r,Q)=kN\) for a random odd prime \(k\) mixes the residues at the rational-value primes in the ideal Cartesian phase law. Each divided coordinate becomes uniform over residues coprime to \(2G(P_i)\), up to the prime equidistribution and phase-normalization errors. The two-coordinate support retains an exact determinant congruence. Its density can go to zero by a fixed power, even though both marginal support densities are \(V^{-o(1)}\). The pinned unconditional construction already varies the prescribed multiple of \(N\); here the multiplier is prime and the calculation concerns the phase law of (G.21). [KeyBreak, §A.2, (B.6), and Lemma G.5](https://crypto.sjtu.edu.cn/factoring.pdf#page=110)

## The affine support at fixed multiplier

Let \(N\) be odd, \(R=(r,Q)\) primitive, and \(G(X,Y)=QX-rY\). Choose an integral linear form \(J\) with \(J(R)=1\). The coordinates \((G,J)\) are unimodular. Fix a degree \(d'\ge2\) and a homogeneous parity form that is irreducible modulo two. Let \(P_1,P_2\) be primitive marks and put
\[
g_i=G(P_i)\ne0,\qquad \Delta=|\det(P_1,P_2)|>0,\qquad (N,g_1g_2)=1.
\]
The index \(q\) is either one or an odd prime with \(q\nmid NQk\). In the latter case require \(P_i\equiv b_i(s,1)\pmod q\), with \(q\nmid b_i g_i\). Thus the common root is admissible and \(q\mid\Delta\). Let \(\ell=\Delta/q\) and \(m_i=2|g_i|\ell\). These formulas include \(q^2\mid\Delta\).

Choose an integral degree-\(d'\) form \(L\) with \(L(R)=1\) and \(L(s,1)\equiv0\pmod q\) when a root is imposed. For instance, take \(L=(J+cG)^{d'}\) with \(c\) solving the one linear congruence modulo \(q\). Choose any base form \(F_*\) of the prescribed parity, with \(F_*(R)=N\) and this same root constraint. Such a base exists because a term \(2c'GY^{d'-1}\) adjusts the root without changing the anchor or parity. Then \(F_*+(k-1)NL\) is an integral reference with the correct anchor, parity and root. These requirements characterize the affine support independently of the particular reference used. Indeed, a homogeneous form vanishing at \(R\) is divisible by \(G\) integrally, and if the form is even its quotient by \(G\) is even as well. This follows either in \((G,J)\) coordinates or by Gauss's lemma and reduction modulo two.

Modulo \(\Delta\), there is a unit \(u\) with \(P_2\equiv uP_1\). To see this, send \(P_1\) to \((1,0)\) by a unimodular change. The first coordinate of the transformed \(P_2\) is a unit modulo its second coordinate \(\pm\Delta\) by primitivity. The integral evaluation image of degree-\(d'-1\) forms then consists exactly of pairs \((x_1,x_2)\) with \(x_2\equiv u^{d'-1}x_1\pmod\Delta\), by using the first two monomials in these coordinates. Imposing the root on a difference \(2GS\) is equivalent to \(q\mid S(P_i)\) for each mark. Dividing by \(q\) reduces the relation modulus to \(\ell\).

Consequently, in the finite residue group \(\mathcal A=(\mathbb Z/m_1)\times(\mathbb Z/m_2)\), the divided supports are the cosets
\[
\mathbf z_*+(k-1)\mathbf h+\mathcal H,\qquad
h_i=NL(P_i)/q,\qquad
\mathcal H=\{(2g_1 t,2g_2 u^{d'-1}t):t\bmod\ell\}.
\tag{1}
\]
The phase group \(\mathcal H\) has order \(\ell\), and each coordinate projection is a bijection onto the lifts of its base residue modulo \(2|g_i|\). The root event is determined by either evaluation modulo \(q\), since \(b_i\) is a unit there. [KeyBreak, Lemmas G.4–G.5](https://crypto.sjtu.edu.cn/factoring.pdf#page=109)

## Marginal support and exact joint loss

Modulo \(|g_i|\), any supported coordinate satisfies
\[
z_i\equiv q^{-1} kN J(P_i)^{d'}\pmod{|g_i|}.
\tag{2}
\]
Here \(J(P_i)\) is a unit modulo \(|g_i|\) by primitivity in the unimodular coordinates. Also \(z_i\) is odd. If \(g_i\) is odd, (2) and oddness determine the base class modulo \(2|g_i|\), by CRT. If \(g_i\) is even, write the reference polynomial as \(kN J^{d'}+GH\). The parity of \(H\) is fixed because \(kN\) is odd and the prescribed parity form is fixed. Thus the base class modulo \(2|g_i|\) is an affine map of \(k\) with unit slope and shift a multiple of \(g_i\). This map permutes the units modulo \(2|g_i|\). It follows in both cases that uniform unit \(k\) modulo \(2|g_i|\), followed by a uniform phase of (1), gives exactly the uniform marginal on
\[
\{z_i\bmod m_i:(z_i,2g_i)=1\}.
\]
Its relative size is \(\phi(2|g_i|)/(2|g_i|)\). When \(\log M=O(\log V)\) and \(|g_i|=O(MV)\), this is \(V^{-o(1)}\) by the usual totient lower bound, and it need not be bounded below by a fixed constant.

In fact two odd multipliers give the same joint phase coset in (1) exactly when they agree modulo
\[
\mathcal M=2|g_1g_2|.
\tag{3}
\]
To check this, write \(T=k-k'\), which is even. Coset equality requires \(2g_i\mid Th_i\) for both \(i\), and
\[
T\frac{g_1h_2-u^{d'-1}g_2h_1}{2g_1g_2}\equiv0\pmod\ell .
\tag{4}
\]
For a prime \(p\) dividing both \(g_i\), write \(L=J^{d'}+GH\). In the numerator before multiplication by \(N/q\), the \(GH\) terms contribute \(g_1g_2[H(P_2)-u^{d'-1}H(P_1)]\), divisible by \(p^{v_p(\Delta)+1}\). The \(J^{d'}\) terms can be written as
\[
\begin{aligned}
&g_1J(P_2)[J(P_2)^{d'-1}-(uJ(P_1))^{d'-1}]\\
&\quad +u^{d'-1}J(P_1)^{d'-1}[g_1J(P_2)-g_2J(P_1)].
\end{aligned}
\]
The first term has valuation at least \(v_p(\Delta)+1\). The bracket in the second term is the signed determinant of the marks, and its multiplier is a unit at \(p\). Hence the numerator of (4), before the factor \(T\), has valuation exactly \(v_p(\Delta)\). Since \(p\nmid Nq\), (4) requires \(v_p(T)\ge v_p(2)+v_p(g_1)+v_p(g_2)\). This covers the shared prime two as well. If \(p\) divides just one \(g_i\), then \(p\nmid\Delta\) by the same determinant identity and the unit \(J(P_i)\), so the base divisibility alone gives the required exponent. At other odd primes, (4) is automatic from \(h_2\equiv u^{d'}h_1\pmod\ell\) and \(g_2\equiv ug_1\pmod\Delta\). If both \(g_i\) are odd, the factor of two is supplied by the even \(T\). This proves (3).

Thus uniform unit \(k\) modulo \(\mathcal M\) followed by a uniform phase gives the uniform joint law on \(\phi(\mathcal M)\ell\) residue pairs. Their fraction of all residue pairs modulo \((m_1,m_2)\) is \(\phi(\mathcal M)/(4|g_1g_2|\ell)\). In particular any supported pair still satisfies
\[
z_2\equiv u^{d'}z_1\pmod\ell .
\]
At primes dividing \(2g_1g_2\), each coordinate has valuation zero if that prime divides its own period. An odd prime dividing \(\ell\) and one \(g_i\) divides both \(g_i\). At other primes of \(\ell\), the two capped valuations agree by the displayed congruence, and each coordinate is uniform in the phase modulo the corresponding prime power. Hence the common gcd law of (G.22) keeps its geometric valuation factors after averaging. More precisely, if \(\ell_\perp\) is \(\ell\) with the prime factors of \(2g_1g_2\) removed, the common capped content has mass \(\phi(\ell_\perp/a)/\ell_\perp\) at each \(a\mid\ell_\perp\). Mixing the base residues leaves this common content in place. [KeyBreak, (G.21)–(G.22)](https://crypto.sjtu.edu.cn/factoring.pdf#page=110)

## Prime law, root event, and phase normalization

For \(k\) uniform among primes in \([W,2W]\), Dirichlet GRH gives relative \(1+O(W^{-1/2}\mathcal M\log^{O(1)}(W\mathcal M))\) uniformity on the units modulo \(\mathcal M\), when this error tends to zero. This follows by subtracting the prime progression estimate at the endpoints and normalizing by the total dyadic prime count. Marginal uniformity alone needs only the two separate moduli \(2|g_i|\). With \(W=M^C\) and a top width \(V\le M^{v_0+o(1)}\), the joint conclusion follows from \(C>4(1+v_0)\), since \(\mathcal M=O(M^2V^2)\). Mere domination of the periods by \(W\) gives no such GRH relative error estimate. Excluding the \(O(\log N)\) possible prime divisors of \(N\) is negligible under the same strict power margin. [Lee, GRH prime-counting estimates for general moduli](https://academic.oup.com/qjmath/article/74/4/1505/7240642)

With independent Gaussian coefficients and \(\sigma/q\to\infty\), the probability of the admissible root is \((1+o(1))/q\) uniformly in \(k\), by solving for the single constant coefficient modulo \(q\). Conditioning on this root therefore perturbs the prime-residue mixture by a uniform relative \(1+o(1)\) factor. A finite Gaussian sampler with global total variation error \(\varepsilon\) costs \(O(q\varepsilon)\) upon conditioning. The excluded anchor slope still cannot be a root since its value is \(kNQ^{-d'}\not\equiv0\pmod q\). [Single-root comparison and conditional sampler error](keybreak-root-congruence-scope.md)

In the ideal Gaussian image, each coset in (1) is a Cartesian progression of steps \(m_1,m_2\). In Mahalanobis coordinates its tiles have radius at most \((m_1/T_1+m_2/T_2)/(2\sqrt{\det C_\rho})\), where \(T_i\) are the marginal Gaussian scales and \(C_\rho\) is the correlation matrix. If this radius is \(o(1)\), each coset mass is \((1+o(1))\) times its continuous volume normalizer, uniformly in the translate and center. The separate-period geometry in (G.23) supplies this condition at the original top scales. This justifies the ideal uniform phase average above. For the actual narrower coefficient law, flatness of the phase is a further estimate. For example, at distinct prime denominators one can obtain it directly when \(\sigma/\Delta\to\infty\): one evaluation of the perturbation modulo \(\Delta\) has an invertible last coefficient \(b_i^{d'-1}\), and the common root restricts its residue modulo \(q\). In a wider determinant range, the affine-support calculation alone gives the base marginal modulo \(2|g_i|\). An arbitrary conditional phase choice could force a coordinate to vanish at a large prime of \(\ell_\perp\), despite the mixed base residue. [Rectangular Gaussian mass estimate](keybreak-gaussian-variation.md) · [KeyBreak, (G.23)](https://crypto.sjtu.edu.cn/factoring.pdf#page=110)

## Height, parity, content and derivative

Keep the old radix \(M=\lfloor N^{1/d}\rfloor\) and \(3M/4<Q\le M\), \(0<r<Q\). Choose \(d'=d+L_0\) with a fixed even \(L_0\ge C\) to retain odd degree. The centered-base-\(Q\) construction applies to the target \(kN\): at each step choose the next coefficient in \([-Q/2,Q/2]\) using invertibility of \(r\) modulo \(Q\). The last coefficient has absolute value at most \(kN/Q^{d'}+d'Q/2\). Since \(N<(M+1)^d\) and \(k\le2M^C\), the first term is \(O((4/3)^{d'}M^{C-L_0})\) when \(d/M=o(1)\). The resulting height after the binary parity correction is \(O(d'2^{d'}M)\), uniformly in \(k\). Recomputing the radix as \(\lfloor N^{1/d'}\rfloor\) would lose the added radix positions, so the degree comparison here uses the old \(M\). The height contribution of \(V^{d'}\) versus \(V^d\) is \(L_0\log V\), and the raw bound \(d'\log V_0/\log N\to v_0<1/2\) still holds if it held before. [KeyBreak, centered digits and parity correction, §A.2](https://crypto.sjtu.edu.cn/factoring.pdf#page=31)

The parity correction keeps the chosen irreducible binary form, since \(kN\) is odd and the anchor is primitive. In particular the primitive part is irreducible, its leading coefficient is nonzero, and all primitive-mark values are odd. If the full sampled coefficient cap is below both \(k\) and \(N\), then the content divides \(kN\) but is coprime to \(k\). Hence it divides \(N\); content above one gives a proper factor. This cap is compatible with the prime mixing scale: for \(\sigma=M^{\chi v_0+o(1)}\) and polynomial bit-length padding, it is \(M^{1+\chi v_0+o(1)}\), so require \(C>1+\chi v_0\). A nonunit leading coefficient similarly yields a proper gcd. The original root \(m_N=rQ^{-1}\bmod N\) is still a root because \(F(r,Q)=kN\). Modulo \(N\), varying the constant coordinate of the perturbation varies \(F'(m_N)\) with unit slope \(2Q\). If its bounded coefficient interval has length less than \(N\), at most one supported coordinate gives a full-gcd derivative rejection. It has Gaussian mass \(O(1/\sigma)\) for each \(k\), plus the finite sampler error. Under an additional prescribed child root the same argument gives \(O(q/\sigma)\) plus the conditional sampler error. These are setup bounds on the original field law. [KeyBreak, §H.1](https://crypto.sjtu.edu.cn/factoring.pdf#page=126)
