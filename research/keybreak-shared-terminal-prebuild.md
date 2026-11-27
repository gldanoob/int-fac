# Shared terminal tables in the single-input KeyBreak cost model

A full terminal prebuild lowers the height-free terminal-only infimum from \((64/9)^{1/3}=1.9229994271\ldots\) to \(((92+26\sqrt{13})/27)^{1/3}=1.9018836119\ldots\). Asymmetric smoothness cutoffs and reuse of one table suffice for this gain. With the physical field height and the full private screening charge, the infimum remains \(C_*=2.1546302152991767\ldots\). These are comparisons of charged cost models for one integer from scratch. The height-free model grants a field-height saving beyond the existing construction. [Terminal table construction](keybreak-late-rational-eligibility.md#a-shared-exact-table) · [Exact joint floor](keybreak-sparse-dependency.md#exact-limiting-coefficient)

## Table work and field-tagged coverage

Write \(D=(\log N/\log\log N)^{1/3}\) and \(H=D\log\log N\). A work coefficient \(c\) means \(\exp((c+o(1))H)\). Use degree \(d\sim\delta D\), a terminal box of coordinate scale \(v\), rational cutoff \(r\), and algebraic cutoff \(a\). On the \(DH\) scale, the ordinary rational and algebraic heights are \(1/\delta\) and \(A+\delta v\), respectively. The smoothness losses in the model satisfy
\[
s_R\ge\frac{1}{3\delta r},\qquad s_A\ge\frac{A+\delta v}{3a}.
\]
Dividing by one incoming prime at a fixed \(H\)-scale changes neither leading height. The table reads the \(\exp((2v+o(1))H)\) points of the box once. Its rational environment is shared by \(\exp((f+o(1))H)\) fields, so there are \(\exp((2v-s_R+f+o(1))H)\) algebraic tests on the retained rationally eligible points. The column exponent is \(c=\max(r,a+f)\), with each retained field charged for its own algebraic base. The current sparse solve ledger charges \(2c\). Thus the full-sweep budget obeys
\[
C\ge\max\{2v,\ 2v-s_R+f,\ 2c\}.
\]
This comparison grants table lookup and the subexponential cost of the individual terminal smoothness tests on the \(H\) scale. Other positive work charges may be omitted in a lower relaxation. [Terminal rational table](keybreak-late-rational-eligibility.md#a-shared-exact-table) · [Field-labelled column count, KeyBreak (E.27)](https://crypto.sjtu.edu.cn/factoring.pdf#page=95) · [Sparse solve cost](keybreak-sparse-dependency.md)

For a prescribed incoming algebraic label \((F,q,s)\), let \(q\) have scale \(y\ge a\). The original root-lattice mean ledger, conditional on the root in field \(F\), gives
\[
\mu=\exp((2v-y-s_R-s_A+o(1))H).
\]
The first moment gives coverage probability at most \(\min(1,\mu)\). A deficit \(\kappa=y+s_R+s_A-2v>0\) therefore makes coverage exponentially rare in the same field. Under a matching normalized incoming law with the source's polynomial \(L^2\) bound, the covered incoming mass is at most \(D^{O(1)}\exp(({-\kappa/2}+o(1))H)\) by Cauchy–Schwarz. A prebuild serving prescribed tags with non-exponentially small probability under that law needs \(2v\ge y+s_R+s_A\). Discharging the ideal parity of a tag in \(F\) requires a table entry in \(F\). [KeyBreak (G.46)–(G.55)](https://crypto.sjtu.edu.cn/factoring.pdf#page=119) · [Field-labelled column count (E.27)](https://crypto.sjtu.edu.cn/factoring.pdf#page=95)

Choosing the field earlier can change the request law. For a fixed numerical pair \((q,s)\), an unconditioned field also needs the root event, which has probability of order \(1/q\). If the root may vary and only \(q\) is fixed, summing over root events removes that factor, while the exponential deficit in \(\mu\) remains in the first-moment bound. Independent coefficients at fixed rational environment \(g\) amplify a proved conditional per-field success probability \(\alpha_g\) to \(1-(1-\alpha_g)^J\) for \(J\) trials. After averaging over \(g\), the specified request's failure probability is \(\mathbb E_g[(1-\alpha_g)^J]\), which requires control beyond the band average. A proof that screens for an exceptionally good field before producing the parent would need a lower bound on the probability of a compatible completed tree and a charge for discovering and using that field. [KeyBreak root probabilities (G.20)](https://crypto.sjtu.edu.cn/factoring.pdf#page=109)

Now grant flexible rows assembled from any of the eligible points and fields. The modeled total supply has coefficient \(2v-s_R-s_A+f\). A collection intended to provide a row population at the full charged column scale needs
\[
2v-s_R-s_A+f\ge c\ge a+f,
\]
and hence \(2v\ge a+s_R+s_A\), the same necessary inequality as the prescribed-tag ledger after relaxing \(y\) to \(a\). This use of the column bound assumes a full row population across the charged bases. A smaller public pool intended to span only a targeted quotient, or field selection that charges fewer bases than it samples, requires a different rank or supply estimate. Any use of a public pool in KeyBreak's final sign argument still needs a dependence involving a nonempty private product. [KeyBreak Theorem E.5 and §H.8](https://crypto.sjtu.edu.cn/factoring.pdf#page=140)

## Height-free terminal optimum

Grant \(A=1/\delta\) and omit all private screening work. For either version of the supply bound above, feasibility implies \(2-\delta/(3a)>0\). Replacing \(v\) by \(C/2\) in the supply inequality relaxes it, as its surplus increases in \(v\). The sparse solve charge gives \(r,a\le C/2\). Raising \(r\) to \(C/2\) reduces the rational loss in the relaxed supply constraint. Put \(a=tC/2\) for \(0<t\le1\). Minimizing over \(\delta>0\) via AM–GM gives
\[
\begin{aligned}
C&\ge a+\frac{1/a+1/r}{3\delta}+\frac{\delta C}{6a}\\
 &\ge \frac{tC}{2}+\frac{2\sqrt{2}}{3}\sqrt{\frac{1+t}{t^2 C}},\qquad
C^3\ge \frac{8(1+t)}{9t^2(1-t/2)^2}.
\end{aligned}
\]
The logarithmic derivative of the last expression has the sign of \(3t^2+2t-4\). Its minimum occurs at \(t=(\sqrt{13}-1)/3\), where the expression is \((92+26\sqrt{13})/27\). Symmetric cutoffs give \(t=1\) and \(C^3\ge64/9\).

The relaxed optimum takes \(r=v=.9509418059\ldots\), \(a=.8259092118\ldots\), and \(\delta=\sqrt{2(1+t)/C}=1.4017532353\ldots\), with \(y=a\) in the fixed-tag limiting ledger. Here \(s_R=.2500651883\ldots\) and \(s_A=a\). Taking \(f=0\) gives equality in the scan and solve budgets. Every \(0\le f\le r-a=.1250325942\ldots\) also keeps \(c=r\) and leaves the field tests below the scan since \(f<s_R\). Strict positive supply or geometric margins can be introduced with arbitrarily small extra slack in these relaxed inequalities. The exact value equals the familiar heuristic MNFS coefficient, while this calculation concerns the specified terminal ledger. [MNFS comparison](cogentic-mnfs-sign-map.md)

## Physical field height and full private screening

Restore the field and private constraints, with positive private coefficient \(u\):
\[
A\ge\frac1\delta+\frac{3u^2}{4},\qquad
C\ge c+p(u),\qquad p(u)=\frac4{9u^2}+\frac{2u}{3}.
\]
To rule out every smaller budget, use \(C=C_*\) in the relaxed constraints. A smaller proposed budget has strict slack in \(r\le C-p(u)\). After dropping the field-test upper bound, raising \(r\) to \(a\) if needed improves the relaxed supply without increasing \(c\). We can therefore take \(a\le r\le C-p(u)<C/2\), using \(p(u)\ge(4/3)^{1/3}>1.10>C_*/2\). As before, put \(v=C/2\) in the relaxed supply. Multiplying the resulting inequality by \(6a\) and applying AM–GM to \(2(1+a/r)/\delta+C\delta\) gives
\[
G(a,r,u):=6a(C-a)-\tfrac32 u^2-2\sqrt{2C(1+a/r)}\ge0.
\]

Let \(u_*\) be the isolated root in the exact floor proof and put \(b_*=C-p(u_*)\). The defining identities are \(6b_*(C-b_*)=\tfrac32u_*^2+4\sqrt C\) and \(6(C-2b_*)p'(u_*)=-3u_*\). Convexity of \(p\) gives \(r-b_*\le-p'(u_*)(u-u_*)\). Expanding the quadratic and applying the slope identity yields
\[
G(r,r,u)\le-6(r-b_*)^2-\tfrac32(u-u_*)^2.
\]
This inequality is strict if \(r<C-p(u)\). [Exact stationary identities and isolation](keybreak-sparse-dependency.md#exact-limiting-coefficient)

Write \(d_0=r-a\ge0\). For \(x=d_0/(2r)\le1/2\), the identity \(1-\sqrt{1-x}=x/(1+\sqrt{1-x})\) gives \(1-\sqrt{1-x}\le3x/5\). It follows that
\[
G(a,r,u)-G(r,r,u)\le d_0 L(r)-6d_0^2,
\qquad L(r)=12r-6C+\frac{6\sqrt C}{5r}.
\]
Any feasible \(r\) exceeds \(.3\), since \(6rC\ge2\sqrt{2C}\) implies \(r\ge\sqrt2/(3\sqrt C)>.3\). The exact root intervals imply \(2.15463<C<2.15464\), \(\sqrt C<1.468\), and \(.90988<b_*<.90990\). These bounds give \(L(.3)<3.6-6(2.15463)+1.2(1.468)/.3<0\) and \(L(b_*)<12(.90990)-6(2.15463)+1.2(1.468)/.90988<0\). By convexity, \(L<0\) on \([.3,b_*]\). For \(r\ge b_*\), the reciprocal term decreases, so \(L(r)\le L(b_*)+12(r-b_*)\). Consequently
\[
d_0L(r)-6d_0^2\le 6(r-b_*)^2-6(d_0-(r-b_*))^2+d_0L(b_*).
\]
In either range the symmetric deficit bounds the possible gain from asymmetry. The result is strict when \(a<r\) or \(r<C-p(u)\). The only feasible equality has \(a=r=b_*\) and \(u=u_*\). Every feasible budget is therefore at least \(C_*\).

At that equality, the symmetric one-field relaxed ledger uses \(v=C_*/2\), \(\delta=2/\sqrt{C_*}\), and \(y=a=r=b_*\). Its table scan equals \(C_*\) because the terminal mean is saturated. The algebraic tests and sparse solve are below \(C_*\). The same limiting parameters occur in the original finite schedules, where strict margins are handled separately. A cheaper single-input factoring procedure would require a different cost or supply constraint, such as a rank bound for a public pool below the full charged column count. [Finite schedules and limiting margins](keybreak-sparse-dependency.md#exact-limiting-coefficient)
