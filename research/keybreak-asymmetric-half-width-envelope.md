# Asymmetric shared terminal table at half-width private cost

Consider the scalar system
\[
0<a\le r,\quad C\ge r+p(u),\quad C\ge 2r,\quad
6a(C-a)\ge \tfrac34u^2+2\sqrt{2C(1+a/r)},
\qquad p(u)=\frac{2}{9u^2}+\frac{2u}{3}.
\]
Here \(u>0\), and \(r=\max(r,a)\) is the charged base size. A certified enclosure for the infimum is
\[
1.9697976<C_{\inf}\le1.9697978.
\]
This is about \(0.0141847\) below the symmetric half-width coefficient \(1.9839824118\ldots\). The constraints concern the proposed terminal-table ledger; the calculation does not price any intermediate levels not covered by that ledger. [Shared table reduction](keybreak-shared-terminal-prebuild.md) · [Symmetric half-width coefficient](keybreak-single-root-width-one-limit.md)

## Rational feasible point

Take the exact decimals
\[
(C,u,a,r)=(1.9697978,\ .62557045,\ .86226917,\ .98489885).
\]
Here \(a<r\), \(C-r-p(u)>1.46\cdot10^{-7}\), and \(C-2r=10^{-7}\). Put \(L=6a(C-a)-3u^2/4\). Direct rational checks give \(L>0\) and \(L^2-8C(1+a/r)>4.82\cdot10^{-6}\), proving strict terminal feasibility. The minimizing degree parameter in the preceding elimination is \(\sqrt{2(1+a/r)/C}\).

## Rational exclusion certificate

At fixed \(C\), increasing \(r\) helps the terminal inequality, so the optimal allowed value for each \(u\) is \(R(u)=\min(C/2,C-p(u))\), provided it is positive and \(a\le R(u)\). Any feasible system remains feasible if \(C\) increases with \(a,r,u\) fixed. Indeed terminal feasibility gives \(6aC>2\sqrt{2C(1+a/r)}\); hence the derivative of \(6a(C-a)-2\sqrt{2C(1+a/r)}\) in \(C\) is positive there and remains so for higher \(C\).

Fix \(C=1.9697976\). Since \(2/(9u^2)\le C\) and \(2u/3\le C\), all feasible points belong to \([1/3,3]\times[0,C/2]\) in \((u,a)\). Feasibility requires \(L\ge0\) and
\[
F(u,a)=L^2-8C(1+a/R(u))\ge0 .
\]
The following bisection certificate uses exact fractions and visits 47,497 closed rectangles including the initial rectangle. It suffices to store the current rectangle endpoints. For \(U=[u_l,u_h]\), \(A=[a_l,a_h]\) define
\[
R_u^0=C-\frac{2}{9u_h^2}-\frac{2u_l}{3},\quad
R_l=\min(C/2,C-2/(9u_l^2)-2u_h/3),\quad R_u=\min(C/2,R_u^0),
\]
and \(L_l=L(u_h,a_l)\), \(L_u=L(u_l,a_h)\), where \(L(u,a)=6a(C-a)-3u^2/4\). These enclose \(R,L\) by monotonicity of the separate terms on the search rectangle.

1. Reject if \(R_u\le0\) or \(a_l>R_u\). Reject also if \(L_u\le0\) or \(L_u^2<8C(1+a_l/R_u)\).
2. If \(R_l>0\), compute \(F\) at the center. Set
   \[
   \begin{aligned}
   D_a&=\max\bigl(|12L_l(C-2a_l)-8C/R_l|,\
     |12L_u(C-2a_l)-8C/R_u|,\ 8C/R_l\bigr),\\
   D_u&=3u_h\max(L_u,|L_l|)
     +8Ca_h\max(|p'(u_l)|,|p'(u_h)|)/R_l^2 .
   \end{aligned}
   \]
   If \(R_u^0<C/2,\ L_l\ge0,\ -p'(u_h)\ge0\), replace \(D_u\) by
   \[
   \max\left(
      |-3u_hL_u+8Ca_l(-p'(u_h))/R_u^2|,\
      |-3u_lL_l+8Ca_h(-p'(u_l))/R_l^2|
   \right).
   \]
   Reject if \(F\) at the center plus \(D_u(u_h-u_l)/2+D_a(a_h-a_l)/2\) is negative.
3. Bisect the larger side if neither test rejects, using the \(a\)-side at equality. Repeat on both halves.

For step 2 the derivative formulas are \(F_a=12L(C-2a)-8C/R\) and \(F_u=-3uL+8CaR'/R^2\). The displayed bounds follow by enclosing each term, using \(0\le C-2a\le C-2a_l\) and the increasing derivative \(p'\). They apply piecewise at the cap \(R=C/2\) and hence give a Lipschitz bound across it. The tighter signed bound uses \(R'=-p'\) throughout its branch. The exact comparisons reject every rectangle. Strictness of \(C_{\inf}>1.9697976\) follows by compactness: in a bounded feasible sequence approaching this \(C\), \(u,a,r\) have convergent subsequences, with \(u\) bounded away from zero by the private bound and \(0<\sqrt{2}/(3\sqrt C)\le a\le r\) by the terminal bound. Its limit would be feasible at the excluded value.

This certificate compares the two scalar models. It supplies no transition or relation-count proof for the asymmetric terminal table.


## Transition across the rational cutoff

The terminal-only gain in this calculation cannot be used by adding further complete tables under the existing full-population charges. For \(a<r\), a chain from large parents to the algebraic base must have a step with incoming exponent \(y\ge r\) and outgoing exponent \(z\le r\). At this step geometric supply requires \(2v\ge y+s_R+s_A\), with \(s_R\ge1/(3\delta r)\) and \(s_A\ge(A+\delta v)/(3z)\). A table costs at least \(2v\); a search charged to the full population costs at least \(r+s_R+s_A\). The checked crossing inequality for either case gives \(2A+2/\delta+\delta C\le6r(C-r)\). Substituting the balanced field height \(A\ge1/\delta+3\chi u^2/8\) and applying AM–GM restores \(3\chi u^2/4+4\sqrt C\le6r(C-r)\). Together with the private charge this gives the symmetric model's floor of \(1.9839824118\ldots\) at \(\chi=1\). A table serving the last level alone still satisfies the numerical witness above. An improvement via this route would need a different charge at the crossing, with a proof of the number or cost of requests it serves. [Existing Lean crossing lemma](../formal/cogentic/Cogentic/RandomizedCutoffCrossing.lean) · [Symmetric width-one envelope](keybreak-single-root-width-one-limit.md)
