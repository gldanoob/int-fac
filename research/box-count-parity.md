# Factoring from parity of a count in a box

A coordinate bound changes what one bit can recover. The parity of the number of ordered positive triples in an axis-aligned integer box with $X^2+Y^2+Z^2\le T$ suffices for deterministic complete factoring with polynomial overhead. There is also a width-one slice of the usual reduced-form count that suffices at parity precision. Both deductions use the interval of nontrivial square roots of one from the upstream project. [Upstream quadratic-congruence reduction](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/quadratic-congruence-factor-recovery.md)

Strip powers of two, test primality and replace perfect powers by their bases. On a residual odd composite $n$ with at least two distinct prime divisors, CRT gives $2^{\omega(n)}$ roots of one modulo $n$. Pairing $x$ with $n-x$ and excluding $x=1$ leaves $2^{\omega(n)-1}-1$ roots in $[2,\lfloor n/2\rfloor]$. This is odd. Bisect the interval, query one half, and keep the half with odd parity. The final root has a proper gcd with $n$ after subtracting one, since its CRT signs are mixed. This uses $O(\log n)$ interval-parity queries per split.

## A shell between two balls

Set $A=n^2+1$, $H=A^2$, $L=nA/2$ and $C=AH^2+L^2$. All constants are integral. For the current interval $I$ take the box of points
$$
(X,Y,Z)=(nH+x,\ H-y,\ L-t),\quad x\in I,\quad 0\le y\le n^2,\quad 0\le t\le n.
$$
All coordinates are positive. The difference between counts at thresholds $C+2A-1$ and $C+A-1$ counts precisely the roots in $I$. In fact
$$
X^2+Y^2+Z^2-C=2H(nx-y)+E,\qquad E=x^2+y^2-nAt+t^2.
$$
Here $-H<E<H$ by the displayed coordinate ranges and $H>2A$. A value in $[A,2A)$ therefore forces $y=nx$. It then equals $A(x^2-nt)+t^2$, with $0\le t^2<A$. Membership is equivalent to $x^2-nt=1$. For each root the unique $t=(x^2-1)/n$ lies in the prescribed range. Every parameter has $O(\log n)$ bits, so the parity of two cumulative box counts suffices per bisection. The shell covers $n^2+1$ individual squared norms. Summing unrestricted single-index counts has a different cost and also omits the coordinate bounds.

## A slice of reduced forms

At discriminant $-4(n^2-1)$, restrict a reduced form $(a,b,c)$ to $a=n$ and $2\min I\le b\le2\max I$. The discriminant forces $b$ even. Writing $b=2x$ gives $c=n+(x^2-1)/n$. Each root in the interval gives exactly one reduced form with $0<2x<n\le c$. It is primitive because $(2x,n)=1$. Thus the parity of this slice works for both unweighted and primitive counts. [Tulsyan, reduced-form counting convention in §5](https://hexagonmath.org/pdf/2611.00115v2#page=5)

The polynomial bound measures the work beyond the parity calls. A faster evaluator for these clipped counts would transfer to factoring. The published generic bounded-product construction supplies the benchmark-scale approach to such counts. [Tulsyan, §§3–4](https://hexagonmath.org/pdf/2611.00115v2#page=4)

[ThreeSquareShell.lean](../formal/ThreeSquareShell.lean) proves the shell equivalence over integers for all odd $n\ge3$ and the stated coordinate bounds. The [GP check](../experiments/hurwitz-box.gp) counts the actual box points using integer square roots and enumerates the form slice separately. It tests all 52 odd moduli through 105 and verifies a proper split on each of the 21 that have at least two distinct prime divisors.
