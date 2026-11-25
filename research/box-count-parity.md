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

## Two planar disks suffice

The factoring bisection also works with two-dimensional Euclidean disks. One version intersects each disk with a single half-plane. Another uses the same nonnegative quadrant for every query, with only the integer center and squared radius varying. Both are unconditional reductions. A full disk with an integer center has odd lattice-point count by central reflection.

Let $1\le l\le h\le\lfloor n/2\rfloor$, put $s=4n^2+1$, $A=s^2+1$, and use the integer coordinate $t=y-sx$. Consider
$$
F(x,y)=x^2+y^2-nAt=A(x^2-nt)+2sxt+t^2 .
$$
A sublevel $F\le T$ is a disk with integer center $(-snA/2,nA/2)$ and squared radius $T+(snA/2)^2+(nA/2)^2$.

**One straight cut.** Intersect both disks with $nt\le(l+h)x-lh-1$. Subtract the counts at $T=2A-1$ and $T=A-1$, taking the outer count minus the inner count. If $F<2A$, then $t\ge0$ since $t\le-1$ gives $F\ge nA$. The cut implies $x>0$, so $F<2A$ gives $x^2-nt\le1$. Combining the inequalities gives $(x-l)(x-h)\le0$. Thus $x\in[l,h]$, and the cut also gives $t<n$. On this range $0\le 2sxt+t^2<A$. The shell therefore contains exactly the points with $x^2-nt=1$. Conversely, each root in $[l,h]$ gives the unique $t=(x^2-1)/n$ and satisfies the cut.

**Fixed quadrant.** Instead require $x\ge l$ and $y\le sh+n$. Here again $F<2A$ forces $t\ge0$. Since $s>n$, this implies $x\le h$. For fixed $x$, the quadratic in $y$ decreases as $y$ increases up to $sh+n<nA/2$. Already $F(x,sx+n)=A(x^2-n^2)+2sxn+n^2<A$ for $l\le x\le h$. Thus points in the shell have $0\le t<n$ and again correspond exactly to the roots. Every root gives a point in the quadrant because $t<n$. Translation and reflection by $(x,y)\mapsto(x-l,sh+n-y)$ put the quadrant at the origin. This transformation preserves the lattice and ordinary disks. All coordinates of the center and the squared radius have $O(\log n)$ bits. Applying the interval bisection above uses $O(\log n)$ disk-parity queries per split.

For $n=105$ and $[l,h]=[2,52]$ the two half-plane disk counts are 201 and 198. Their difference counts the three roots 29, 34 and 41. The [planar regression](../experiments/hurwitz-box.gp) computes both disk geometries with integer square roots and checks every one of the 62,196 intervals on all odd moduli from 3 through 143. This planar reduction is a paper proof. The Lean theorem below concerns the three-dimensional shell.

**Cost of listing the integer hull.** Har-Peled's algorithm charges the number of output vertices times the logarithm of the diameter. Already the inner disk with the straight cut for $l=2$ and $h=\lfloor n/2\rfloor$ has $\Omega(\sqrt n)$ vertices in its integer hull. Every feasible point satisfies $nt\ge x^2$ by the inner sublevel bound. For each integer $j$ in the middle half of $[l,h]$, $(x,t)=(j,\lceil j^2/n\rceil)$ is feasible for large $n$: the cut has slack $(j-l)(h-j)\ge n$ and the remainder $2sxt+t^2$ is less than $A$. A vertex minimizing $nt-2jx$ must have $(x-j)^2<n$ by comparison with this feasible point. Taking $j$ more than $2\sqrt n$ apart forces distinct minimizing vertices. The shear $(x,t)\mapsto(x,y)$ preserves vertex count. Thus explicitly listing the hull takes exponential time in the bit length on these caps. Counting their parity without listing the vertices remains open here. Barvinok's fixed-dimensional polynomial bound takes a rational polyhedron as input. [Har-Peled, Theorem 3.11](https://arxiv.org/html/2601.00392v1) · [Barvinok's polyhedral counting theorem](https://doi.org/10.1287/moor.19.4.769)

Sardari’s Theorem 1.8 concerns existence of a point on a circle with prescribed coordinate congruences. Substituting $x_i=a_i+qz_i$ expresses that problem with a rational center. The paper proves NP-completeness using an unconditional randomized reduction, or under GRH and Cramér’s conjecture. The deterministic quadrant result above uses parity of a disk count. [Sardari, Theorem 1.8](https://arxiv.org/pdf/1703.02709#page=5)

## A slice of reduced forms

At discriminant $-4(n^2-1)$, restrict a reduced form $(a,b,c)$ to $a=n$ and $2\min I\le b\le2\max I$. The discriminant forces $b$ even. Writing $b=2x$ gives $c=n+(x^2-1)/n$. Each root in the interval gives exactly one reduced form with $0<2x<n\le c$. It is primitive because $(2x,n)=1$. Thus the parity of this slice works for both unweighted and primitive counts. [Tulsyan, reduced-form counting convention in §5](https://hexagonmath.org/pdf/2611.00115v2#page=5)

The polynomial bound measures the work beyond the parity calls. A faster evaluator for these clipped counts would transfer to factoring. The published generic bounded-product construction supplies the benchmark-scale approach to such counts. [Tulsyan, §§3–4](https://hexagonmath.org/pdf/2611.00115v2#page=4)

[ThreeSquareShell.lean](../formal/ThreeSquareShell.lean) proves the shell equivalence over integers for all odd $n\ge3$ and the stated coordinate bounds. The [GP check](../experiments/hurwitz-box.gp) counts the actual box points using integer square roots and enumerates the form slice separately. It tests all 52 odd moduli through 105 and verifies a proper split on each of the 21 that have at least two distinct prime divisors.
