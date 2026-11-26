# Projective quadratic charts with rational evaluation labels

A rational Möbius chart changes the natural rational label of a mark without changing its field element. This can make a rational squareclass match available where evaluation of the affine pullback gives no match. The quadratic local square kernel and the rational matching algorithm still give a complete finite decision on the supplied chart libraries. [Compatible charts](cogentic-compatible-quadratic-charts.md) · [Rational root matching](cogentic-rational-root-matching.md)

## Pullback and evaluation

Let `P` be monic irreducible quadratic, let `α` be a root, and let `m` be a simple root of `P` modulo odd `N`. For integers `u,v,w,z` with `uz−vw ≠ 0`, take

\[
 \beta=\frac{u\alpha+v}{w\alpha+z},\qquad
 m_\beta=\frac{um+v}{wm+z}.
\]

Require `wm+z` to be a unit modulo `N`. Rational matrix entries can be cleared by one common denominator before this test. The signed mark on the chart and its exact rational label are

\[
 \gamma=a-b\beta=\frac{az-bv+(aw-bu)\alpha}{w\alpha+z},
 \qquad e=a-bm_\beta .
\]

Require the label to be a unit modulo `N`. The branch map sends the mark to the same residue as its rational label. A proper gcd of the branch denominator or of the label numerator with `N` is a factor certificate before any square calculation.

Compute signed local square kernels in the original quadratic field on the pulled-back rational elements. When several charts share that field and branch, combine their occurrences before computing its kernel. Keep the original rational labels for matching. Suppose a product of selected signed marks is `A/D`, where `A,D` are algebraic integers and the reduction of `D` is a unit. If `ρ²=A/D`, then `(Dρ)²=AD` is integral, so `Dρ` is integral. Its reduction is defined in the simple original chart by the same trace-denominator argument as for any integral quadratic element. Divide the result by the unit reduction of `D`. This requires a unit value of `D` on the chosen branch. Its field norm need not be a unit.

The pullback, coefficient arithmetic, local quadratic kernel, root reduction and rational matching each take polynomial bit time in the explicit data. Products of marks add their operand heights, and the numerator and denominator of every rational label have polynomial bit length in the chart and mark data. A list of fixed chart libraries can be tested against its own exact labels one library at a time.

## An exact split using the natural projective label

Take `N=65` and two charts based on monic irreducible quadratics.

| Field polynomial | Base | Mark | Label | Root |
| --- | ---: | --- | ---: | --- |
| \(X^2+21X+43\) | 1 | \(57-X\) | 56 | \(X+10\) |
| \(Q=X^2+27X+7\) | 2 | \(-\beta\) | \(7/2\) | \((X+10)/2\) |

In the second field, put

\[
 \beta=\frac{345X-788}{4(9-X)}=\frac{7X-93}{4}\pmod Q.
\]

The defining polynomials both take the value 65 at their base arguments. Their derivatives there are 23 and 31. The projective matrix has determinant 9,268 and the norm of \(9-X\) in the second field is 331. All these integers and the evaluated denominators are units modulo 65. The two displayed squares follow by subtracting the marked value from the root square and obtaining, respectively, the defining polynomial and \(Q/4\).

At the second base the projective argument is \(-7/2\), while evaluating the affine pullback there gives \(-79/4\). These give congruent labels for the same nonintegral algebraic element. On these supplied singleton pools, matching the affine labels 56 and \(79/4\) gives zero kernel since their squareclasses are independent. The fields are real, so the signed local kernels add no sign-only relation. The projective labels satisfy \(56\cdot(7/2)=14^2\). The reduced roots are 11 and 6, and the normalized ratio is \(66/14=14\pmod{65}\). Its difference gcd gives 13.

Every quadratic Möbius generator is rational-affine in the original generator after field reduction. Thus this example enlarges the matching domain through a structured choice of labels for an unchanged algebraic mark. An affine model already permitting arbitrary congruent rational labels can express the same certificate.
