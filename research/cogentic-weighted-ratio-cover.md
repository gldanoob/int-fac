# Cost of weighted windows for a public ratio interval

Let $N=pQ$ with $p$ prime. Suppose the public ratio interval $I\subset[1,4]$ of length $\lambda>0$ contains $Q/p$. A list of weighted gap windows covering every real ratio in $I$ has cost at least $\Omega(N^{1/5}\lambda^{3/5})$ when $\lambda\ge N^{-1/8}$. An explicit list attains this bound up to logarithmic factors. At $\lambda\asymp 1$ this gives the fifth-root scale. A shorter public interval saves a factor of $\lambda^{3/5}$ in this range. These estimates concern the geometric coverage promise. Given an actual factorization $N=pQ$, the triple $(p,Q,0)$ already covers its ratio with a single integer in its sum window, namely $2N$. [Batched weighted gap search](cogentic-hasse-window-factor-gap.md)

## Lower bound with integer windows

For the triple $(a,b,D)$, use $x=Q/p$ and $y=\tfrac12\log x$. Its coverage condition is

\[
 |aQ-bp|=2\sqrt{abN}\,|\sinh(y-y_0)|\le D,
 \qquad y_0=\tfrac12\log(b/a).
\]

Write $r=\operatorname{arsinh}(D/(2\sqrt{abN}))$ for the radius. The real length of the sum interval searched by the algorithm is

\[
 L=\sqrt{4abN+D^2}-2\sqrt{abN}
  =2\sqrt{abN}(\cosh r-1)\ge\sqrt{abN}\,r^2.
\]

Its integer count $W=\max(0,\lfloor\sqrt{4abN+D^2}\rfloor-\lceil 2\sqrt{abN}\rceil+1)$ satisfies $L-1\le W\le L+1$, including when it is empty. Translation to the exponent interval preserves $W$. If there are $K$ triples, then

\[
 \sum_i W_i+K \;\ge\; \sum_i L_i.
\]

Let $J=\tfrac12\log I$, whose length is between $\lambda/8$ and $\lambda/2$. A window of radius at least $|J|$ already contributes $L\gg\sqrt N\lambda^2$. Otherwise every covering window meeting $J$ has center in the interval obtained by extending $J$ by $|J|$ on either side. The ratios of those centers lie in a fixed compact positive range and in an interval of length $O(\lambda)$, by the bounded derivative of $\exp(2y)$ there.

Keep the largest radius at each distinct center and write the center as a reduced fraction $b_i'/a_i'$. Put $h_i=\sqrt{a_i'b_i'}$. The original weight $\sqrt{a_ib_i}$ is at least $h_i$. Among the centers of height at most $H$, the denominators are $O(H)$ and any two distinct reduced fractions are separated by $\gg H^{-2}$. The count is at most $1+C\lambda H^2$ for an absolute $C$. In increasing height order this gives $h_1\ge1$ and $h_j\ge\sqrt{(j-1)/(C\lambda)}$ for $j\ge2$. Hence $\sum_i h_i^{-1}\ll 1+\sqrt{\lambda K}$. Coverage gives $\sum_i r_i\ge |J|/2$, so Cauchy–Schwarz yields

\[
 \sum_i W_i+K \gg \frac{\sqrt N\,\lambda^2}{1+\sqrt{\lambda K}}.
\]

The same inequality follows from the single wide window in the first case. For $T=K+\sqrt{\sum_i W_i}\ge1$, the left side is at most $2T^2$, and the denominator on the right is at most $1+\sqrt{\lambda T}$. Considering $\lambda T\le1$ and $\lambda T\ge1$ gives

\[
 T\gg\min\bigl(N^{1/4}\lambda,\ N^{1/5}\lambda^{3/5}\bigr).
\]

For $\lambda\ge N^{-1/8}$ the latter expression is the smaller. The bound in this range also holds for covering every $x=N/m^2\in I$ with $m$ a positive integer. There are $\gg\sqrt N\lambda$ such integers for sufficiently large $N$, since the derivative of $\sqrt{N/x}$ has magnitude between $\sqrt N/16$ and $\sqrt N/2$ on $[1,4]$. Each window covers at most $1+O(\sqrt N r_i)$ integers because $m=\sqrt N\exp(-y)$. If $K$ is a sufficiently small constant times $\sqrt N\lambda$, this count forces $\sum_i r_i\gg\lambda$ after retaining the largest radius at each center. For larger $K$ the desired bound follows from the list size alone. This integer-grid version still requires coverage at $m$ regardless of divisibility.

## Constructing a matching list

Take an integer $2\le A\le\sqrt N$ and set $D=\lceil\sqrt N/A\rceil$. For every $x\in I$, pigeonholing $0,x,\ldots,Ax$ modulo one gives $1\le a\le A$ and $|ax-b|\le1/A$. Reducing $b/a$ preserves the inequality. The resulting triple covers the ratio since $p=\sqrt{N/x}\le\sqrt N$ and $p|ax-b|\le\sqrt N/A$.

In each dyadic denominator band $U\le a<2U$, include all reduced fractions $b/a$ with $a\le A$ in $I$ extended by $1/(UA)$ at each end. The extensions retain every fraction needed by the approximation argument. The centers remain in $[1/2,9/2]$. The minimum separation is at least $1/(4U^2)$, so the band has $O(1+\lambda U^2+U/A)=O(1+\lambda U^2)$ entries. For each entry,

\[
 L=\frac{D^2}{\sqrt{4abN+D^2}+2\sqrt{abN}}
  \ll\frac{\sqrt N}{UA^2}.
\]

Summing over the bands gives

\[
 K\ll \lambda A^2+\log(2A),\qquad
 \sum_i W_i\ll K+\sqrt N\left(\frac{\lambda}{A}+\frac{1}{A^2}\right).
\]

For rational public endpoints, enumerate a band by traversing the fractions of denominator at most $M=\min(2U-1,A)$ in its extended interval. Each has denominator at least $U$ or can be discarded, and the same spacing bound counts all visited fractions. To start, bracket the left endpoint by successive integer fractions, then take mediants, preserving a strictly lower left bracket and a weakly upper right bracket. Group consecutive updates to the same side by taking the largest multiple of the opposite numerator and denominator permitted by the bracket inequality and the denominator bound. Both constraints are linear in the multiple. Each pair of opposite updates at least doubles the denominator sum. The brackets are adjacent in the order-$M$ sequence when their denominator sum exceeds $M$, since any fraction strictly between a pair of determinant one has denominator at least the sum. For adjacent $u/v<w/z$, the successor of $w/z$ is $(kw-u)/(kz-v)$ with $k=\lfloor(M+v)/z\rfloor$. The successor has determinant one with $w/z$ and their denominator sum exceeds $M$. Thus initialization takes logarithmically many arithmetic operations per band and traversal takes one per visited fraction.

Choose $A$ within a constant factor of $N^{1/10}\lambda^{-1/5}$. For $\lambda\ge N^{-1/8}$, one has $\lambda A\gg1$ and the list and window bounds give search work $\widetilde O(N^{1/5}\lambda^{3/5})$ including enumeration. Soft notation allows polynomial factors in the bit lengths of $N$ and the public endpoints. This construction uses the public ratio interval as additional information. Uniform one-third work would require arithmetic information beyond covering a fixed balanced ratio interval.

For $N^{-1/2}\le\lambda\le N^{-1/8}$, the same list construction with $A\asymp N^{1/12}\lambda^{-1/3}$ gives $\widetilde O(N^{1/6}\lambda^{1/3})$ work. Here $\lambda A\ll1$, so the $1/A^2$ term dominates the window-length estimate. This is an upper bound for every interval in the smaller range. The lower bound above can be smaller there.
