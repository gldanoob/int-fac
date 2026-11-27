# A support bound for short factored-denominator proposals

Let $X<N$. A unit $z\bmod N$ whose least positive square residue $u$ is at most $X$ is covered by the short rational box if it has a representation
$$
z\equiv h/t\pmod N,\qquad
0<|h|\le H_0,\quad 1\le t\le T,\quad (h,t)=1,\quad (t,N)=1.
$$
Assume $H_0\le X$ and $T\le\sqrt X$. The number of covered roots $z$, and hence also the number of their square residues $u$, is at most
$$
N^{o(1)}O\left(\sqrt X+\frac{TH_0X}{N}
                         +\frac{T^2X^{3/2}}{N}\right).
$$
The bound is for support, regardless of the proposal probabilities. It allows either sign of $h$ and of the winding integer $(h^2-t^2u)/N$. [Factored-denominator proposal](keybreak-factored-denominator-proposal.md) · [Related short-vector count](keybreak-short-vector-exception.md)

## Proof

For each admissible $(t,h)$, the integer $u$ in $[1,X]$ is unique when it exists. Write
$$
h^2=kN+t^2u.
$$
If $k=0$, coprimality forces $t=1$, giving at most $2\sqrt X$ pairs. Otherwise $h$ belongs to a unit square-root class of $kN$ modulo $t^2$. The number of such classes is at most $2^{\omega(t)+1}=N^{o(1)}$, uniformly in $t$, by CRT and the two-root bound at odd prime powers and four-root bound at powers of two.

For $|h|\le t\sqrt X$, there are $O(t^2X/N)$ choices of nonzero $k$. Each class has $O(1+\sqrt X/t)$ representatives in that full interval. Since $T\le\sqrt X$, the resulting bound at fixed $t$ is $N^{o(1)}O(tX^{3/2}/N)$.

For the remaining heights, split $t\sqrt X\le |h|\le H_0$ into dyadic pieces $Y\le |h|<2Y$. In a piece there are $O(Y^2/N)$ nonzero winding integers. For each $k$ and sign, the possible $h$ form an interval of length at most $t^2X/(2Y)$, by the difference of squares. There are $O(1+X/Y)=O(X/Y)$ integers in each root class there, since $Y\le H_0\le X$. Summing the resulting bound $N^{o(1)}O(YX/N)$ over the pieces gives $N^{o(1)}O(H_0X/N)$ at fixed $t$. These counts use the actual number of nonzero integers in a bounded interval, so no additive $1$ is needed for $k$ when its magnitude bound is less than 1. Summation over $t$ proves the result. Allowing $H_0\le XN^{o(1)}$ or $T\le\sqrt X N^{o(1)}$ still gives the same worst-case exponent, since the absorptions of $1$ in the two root-class counts then lose only $N^{o(1)}$.

## Consequences for the protocol

If $X=N^{a+o(1)}$ with $0<a<2/3$, the covered residues form at most an $N^{-\kappa+o(1)}$ fraction of $[1,X]$, where $\kappa=\min(a/2,1-3a/2)>0$. For odd $N$ and $a>1/2$, the same power-saving fraction holds among the unit roots with square residues in $[1,X]$. The latter set has size $X\phi(N)/N+O(N^{1/2+o(1)})$ by complete quadratic sums and inclusion–exclusion for units, with no denominator restriction. [Quadratic completion and root count](keybreak-primitive-denominator-discrepancy.md)

Factoring the denominator into two or more sampled components does not change this support bound. If a multistep proposal ultimately outputs a rational representative in the same numerator and denominator ranges, its support is covered too. A nonprimitive representation with a denominator coprime to $N$ reduces to a primitive one by cancelling its rational gcd, which only decreases both heights. These statements leave open protocols that generate useful larger rational representatives or that obtain a modular square without a final representative in the short box.

A different homogeneous binary quadratic numerator alone cannot replace the square through a rational-function identity. Let $Q(H,T)$ be a nonzero homogeneous quadratic over $\mathbb Q$ and suppose $Q(H,T)/T^2$ is a square in $\mathbb Q(H,T)$. Multiplying by the square $T^2$ makes $Q$ a rational-function square. In a coprime fraction for its root, unique factorization forces the denominator to be constant. The root is therefore polynomial, and homogeneity forces it to be a rational linear form. This excludes a nondegenerate binary quadratic in an identity of that kind. It does not exclude arithmetic restrictions on the sampled pairs that make a nondegenerate form a square modulo $N$.
