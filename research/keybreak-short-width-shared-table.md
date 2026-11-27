# Terminal tables and asymmetric cutoffs at short width

At width \(\theta=2/3\), the shared terminal-table ledger has infimum in \([2.07254,2.07255)\) for both prescribed algebraic tags and a full flexible row population. This improves on the symmetric coefficient \(C_*=2.07377842496623257501\ldots\) within the charged ledger. Asymmetric cutoffs with independent terminal searches still have infimum \(C_*\), including the branch with a rational incoming label and a larger algebraic cutoff. The table comparison grants the stated scan and lookup costs and the modeled coverage or row supply. A single-input factoring bound would require those guarantees for an implemented relation collector. [Shared table model](keybreak-shared-terminal-prebuild.md) · [Per-request model](keybreak-asymmetric-terminal-budget.md) · [Short-width stationary floor](keybreak-lattice-limit.md)

Use the private and field-height bounds
\[
p(u)=\frac{8}{27u^2}+\frac{2u}{3},\qquad A\ge\frac1\delta+\frac{3u^2}{4}.
\]
The comparison \(p(u)>C_*/2\) fails at \(u=1\), where \(p(1)=26/27<C_*/2\).

## Full shared scan

Let \(r,a\) be the rational and algebraic cutoffs, \(v\) the terminal coordinate scale, and \(f\) the exponent for the number of charged fields. Write \(c=\max(r,a+f)\) for the charged column exponent. The short-width shared-table ledger requires
\[
\begin{gathered}
s_R\ge 1/(3\delta r),\qquad s_A\ge (A+\delta v)/(3a),\\
C\ge\max(2v,2v-s_R+f,2c,c+p(u)).
\end{gathered}
\]
Prescribed algebraic tags require \(2v\ge y+s_R+s_A\) with tag scale \(y\ge a\). A full flexible row population requires \(2v-s_R-s_A+f\ge c\). Because \(c\ge a+f\), either mode requires \(2v\ge a+s_R+s_A\).

For a lower bound, omit the field-test budget and put \(R=\min(C/2,C-p(u))\). Both cutoffs are at most \(R\). Raising \(r\) to \(R\) improves the relaxed supply inequality. The supply inequality forces \(2-\delta/(3a)>0\), so raising \(v\) to \(C/2\) also improves it. Use the smallest allowed \(A\). Multiplying by \(6a\) and minimizing over \(\delta>0\) then gives the necessary envelope
\[
0<a\le R,\qquad
G(a,R,u)=6a(C-a)-\tfrac32u^2-2\sqrt{2C(1+a/R)}\ge0.
\]
The minimizing degree coefficient is \(\delta=\sqrt{2(1+a/R)/C}\). In the prescribed algebraic-tag relaxation with \(y=a\) the envelope is sufficient as well, by taking \(f=0\), \(r=R\), \(v=C/2\), and both losses at their lower bounds. A full flexible row population also needs its field-test budget.

At the symmetric stationary point \((b_*,b_*,u_*)\), decreasing \(a\) has first-order gain \(12b_*-6C_*+\sqrt{C_*}/b_*\) in \(G\). The root enclosure gives \(.9320<b_*<.9321\), so this gain exceeds \(12(.9320)-6(2.074)+1.44/.9321>0\). The table gain occurs even with both cutoffs below \(C_*/2\). [Root enclosure](keybreak-lattice-limit.md)

For \(C=2.07254\), write \(L=6a(C-a)-3u^2/2\). Feasibility implies \(L\ge0\) and \(L^2\ge8C(1+a/R)\). It also implies \(u>1/3\) because \(p(u)\le C<8/3\), and \(u\le C\) because \(L\le3(C^2-u^2)/2\). The exact rational checker processes 421 rectangles while covering \([1/3,C]\times[0,C/2]\). On each rectangle it bounds \(R\) from above and \(L\) from above using monotonicity of \(6a(C-a)\) on \([0,C/2]\). It rejects by the squared necessary inequality when those bounds suffice. Otherwise, where \(R_0=C-p(u)>0\) throughout, it bounds
\[
F=L^2-8C(1+a/R_0)
\]
by its value at the rectangle center plus the coordinate half-widths times upper bounds on the absolute partial derivatives. Those derivatives are \(12L(C-2a)-8C/R_0\) and \(-6uL+8CaR_0'/R_0^2\). A negative upper bound rejects the rectangle because \(R\le R_0\). All comparisons use exact fractions. The original feasible sets are monotone in the budget, so the rejection also applies below \(2.07254\). [Rational box and witness replay](../experiments/keybreak-short-width-shared-table.py)

For the upper bound, take the exact decimal parameters
\[
\begin{gathered}
C=2.07255,\quad u=.6625787,\quad r=.9559124,\quad a=.909207,\\
\delta=1.372166,\quad v=1.036274,\quad y=.9092075,\quad f=r-a=.0467054.
\end{gathered}
\]
Set \(A=1/\delta+3u^2/4\) and use equality for both smoothness losses. Then \(c=r\). The private slack exceeds \(4.54\cdot10^{-8}\), the scan slack is \(2\cdot10^{-6}\), the field-test slack exceeds \(.2074\), and the sparse solve slack is \(.1607252\). The prescribed algebraic mean slack exceeds \(4.43\cdot10^{-6}\). The full flexible row supply slack exceeds \(4.93\cdot10^{-6}\) because \(c-f=a\). With just one field, \(f=0\) also works for the prescribed algebraic tags. The strict margins allow an increase of \(\theta\) above \(2/3\) within this ledger. A field-tagged covering or rank theorem would be needed to use these margins, including for the extra fields in the flexible-row witness. [Strict rational margins](../experiments/keybreak-short-width-shared-table.py)

## Independent terminal requests

Let \(b=\max(a,r)\), \(s=s_R+s_A\), and retain \(2v\ge y+s\), \(C\ge b+s\), and \(C\ge b+p(u)\). Eliminating \(v\) gives
\[
(3a-\delta/2)s\ge A+\delta y/2+a/(\delta r),\qquad 3a-\delta/2>0.
\]
To exclude every smaller ceiling, enlarge the budget to \(C=C_*\). This leaves \(b+p(u)<C\). If \(y\ge b\), raise both cutoffs to \(b\) and replace \(y\) by \(b\). This relaxes the original inequalities and gives \(6b(C-b)\ge3u^2/2+4\sqrt C\). If the incoming label is algebraic and \(a<b=r\), replace \(y\) by \(a\). The lower bound \((A+a(\delta/2+1/(\delta b)))/(3a-\delta/2)\) for \(s\) decreases with \(a\), so the same symmetric bound follows at \(a=b\).

The remaining case is a rational incoming label with \(r<b=a\). Put \(t=r/b\le1\) and \(z=b(C-b)\). Replacing \(y\) by \(r\), substituting \(s\le C-b\), and minimizing over \(\delta\) gives
\[
6z\ge\tfrac32u^2+2\sqrt{2(1+1/t)(C-b+bt)}.
\]
If \(b\le C/2\), then
\[
(1+1/t)(C-b+bt)-2C=(1-t)((C-b)/t-b)\ge0.
\]
Thus the symmetric terminal bound follows again. Together with the strict private budget it contradicts the stationary supporting inequality at \(C_*\). In detail, convexity of \(p\) gives \(b-b_*<-p'(u_*)(u-u_*)\), where \(b_*=C_*-p(u_*)\). Expand \(6b(C-b)-3u^2/2-4\sqrt C\) at \((b_*,u_*)\). Its constant term vanishes, and the positive coefficient \(6(C-2b_*)\) permits using the strict bound on \(b-b_*\). The stationary slope identity cancels the linear terms and leaves a strictly negative bound. [Stationary identities and certificate](keybreak-lattice-limit.md)

If \(b>C/2\), then \(p(u)<C/2\). Since \(p\) decreases up through \(u=.7\) and \(p(.7)>1.07>C/2\), this forces \(u>.7\). The product under the square root is minimized at \(t=\sqrt{(C-b)/b}\) and equals \(C+2\sqrt z\) there. Thus feasibility would require
\[
\tfrac32u^2\le \phi(z):=6z-2\sqrt{2(C+2\sqrt z)},\qquad z\le C^2/4.
\]
Feasibility also gives \(z\ge\sqrt{2C}/3>2/3\). On that range,
\[
\phi'(z)=6-\frac{\sqrt2}{\sqrt z\sqrt{C+2\sqrt z}}>0.
\]
Here \(\phi'(z)>6-2\sqrt2>0\), since \(\sqrt z>1/2\) and \(\sqrt{C+2\sqrt z}>1\). It follows that \(\phi(z)\le\phi(C^2/4)=3C^2/2-4\sqrt C<.693\), using \(C<2.074\) and \(\sqrt C>1.44\). This contradicts \(3u^2/2>.735\).

The symmetric limiting values attain the budget of the relaxed per-request model. Take \(a=r=y=b_*\), \(v=C_*/2\), \(\delta=2/\sqrt{C_*}\), and \(s=C_*-b_*\). The stationary value equation gives equality for the two losses combined with the minimum \(A\), and both \(2v=y+s\) and \(C_*=b_*+p(u_*)\) hold. This also retains the full triangular prebuild obstruction when the last eliminated prefix has pivot-label exponent at least \(b\). Such a step charges \(y+s\ge b+s\) whether it searches independently or scans its entire box. [Full triangular prebuild assumption](keybreak-asymmetric-terminal-budget.md#full-prebuilds-and-selective-reconciliation)

## Scope of the shared-table bound

A shared scan serving only prescribed rational tags with \(y\ge r<a\) gives a separate relaxation with \(2v\ge r+s_R+s_A\). Its reduced inequality is \(6a(C-r)\ge3u^2/2+2\sqrt{2C(1+a/r)}\). The parameters \(C=1.900,u=.823,a=.913,r=.428,\delta=1.816,v=.9495,y=.429,f=0\) have private slack above \(.00088\), scan slack \(.001\), and rational-tag mean slack above \(.025\). The same parameters have a full-row deficit above \(.458\). Moving all final requests to the rational side would need a compatible descent and a proof that the table responses yield enough relations for the charged bases. [Rational-tag witness replay](../experiments/keybreak-short-width-shared-table.py)
