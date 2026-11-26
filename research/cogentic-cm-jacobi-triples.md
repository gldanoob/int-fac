# Short Jacobi triples separate marked CM twists

Assume Dirichlet RH. For every sufficiently large semiprime $N=pq$ with distinct primes $p,q\equiv3\pmod8$, an input-only polynomial-bit-time search gives a proper divisor or a rational congruent-number curve with a marked point whose two-primary projection has different labels at $p$ and $q$. If the odd part of $p+1$ or of $q+1$ is $B$-smooth, a public odd multiplier and the two rational torsion coordinates give a deterministic split in $\widetilde O((B+1)\operatorname{poly}(\log N))$ bit work. The smoothness promise concerns one explicit group size, and the local character separation holds on the entire residue-class family. [Fixed-curve separation and varying odd-order supply](cogentic-elliptic-local-halves.md)

## A polynomial-size search for a distinguishing triple

Write $L=\log N$, $b=\operatorname{bitlength}(N)$, and $T=b^4$. Search integers through $T$ and compute their gcds with $N$. A nonunit gives a proper divisor since $T<N$ for all sufficiently large $N$. If the scan gives no divisor, write $\chi(n)=(n/N)$; all signs in the interval are $+1$ or $-1$. This is a nonprincipal quadratic Dirichlet character of conductor $pq$ because the factors are distinct.

Use the first estimate in Granville–Soundararajan's Theorem 2 with $Y=L^2(\log T)^2(\log\log N)^{12}$. Since $T\le N$ and $Y>\sqrt T$ for large $N$, it gives
\[
 \left|\sum_{n\le T}\chi(n)\right|\le(1+o(1))\Psi(T,Y).
\]
In fact each integer at most $T$ has at most one prime factor exceeding $Y$, so
\[
 \frac{\Psi(T,Y)}{T}=1-\frac1T\sum_{Y<r\le T,\ r\ {m prime}}\lfloor T/r\rfloor
       =1-\log2+o(1).
\]
The last step is the reciprocal prime sum, since $\log Y/\log T\to1/2$ and $\pi(T)=o(T)$. As $1-\log2<1/3$, more than $\lceil T/3\rceil$ integers have negative Jacobi sign. If no triple of consecutive signs has exactly two negatives, two adjacent negatives would force every sign in the interval negative, contrary to $\chi(1)=1$. Two negatives at distance two would likewise be forbidden. Thus the negatives would be separated by at least three, contradicting their count. The scan therefore finds $2\le t<T$ for which exactly two of $\chi(t-1),\chi(t),\chi(t+1)$ are negative. This uses an unshifted character sum and a combinatorial count. [Granville–Soundararajan, Theorem 2](https://arxiv.org/pdf/math/9903196#page=4)

## Reading the torsion label

For this $t$ set $d=t(t^2-1)$ and take
\[
 E_d\colon y^2=x(x-d)(x+d),\qquad R=(dt,d^2).
\]
The integer equality $d^3t(t^2-1)=d^4$ gives the point. The gcd checks make $d$ a unit. For either prime $r\mid N$, the sum of the quadratic characters of $x(x^2-d^2)$ cancels in pairs $x,-x$, since $r\equiv3\pmod4$. Thus $\#E_d(\mathbb F_r)=r+1$. At $r\equiv3\pmod8$ this group has two-part of size four, exactly its rational two-torsion. Label this subgroup by the basis $T_0=(0,0)$ and $T_+=(d,0)$, using $O$ for the zero label.

Represent Legendre signs by binary bits, with negative mapped to one. The two square-class homomorphisms are the coordinates $x$ and $x-d$, using the derivative product at their zero roots. They are homomorphisms by the chord-and-tangent identity, and hence kill the odd part. Their values on $T_0,T_+$ are $(-1,-d)$ and $(d,2)$, respectively, modulo squares. Write $(a,c_-,c_+)$ for the bits of $t,t-1,t+1$ at $r$, and $e=a+c_-+c_+$. The matrix on $T_0,T_+$ and the column of $R$ are
\[
 C_r=\begin{pmatrix}1&e\\1+e&1\end{pmatrix},\qquad
 v_r=\binom{c_-+c_+}{a+c_+}.
\]
Since $C_r$ is invertible, $C_r^{-1}v_r$ is the coefficient vector of the two-primary projection of $R$. The four fibers of this value are
\[
 \{000,111\},\quad\{001,011\},\quad\{010,110\},\quad\{100,101\},
\]
with respective labels $00,01,10,11$. Two local bit triples that differ in exactly two entries cannot lie in the same fiber. Their bits differ precisely at the negative Jacobi signs, so the selected parameter gives distinct torsion labels at $p,q$. [Elementary square-class homomorphism](cogentic-elliptic-cycle-density.md#independent-directions)

## Extracting a divisor under the stated smoothness promise

Take the odd scalar
\[
 U=\prod_{3\le\ell\le B,\ \ell\ {m prime}}\ell^{\lfloor\log_\ell(2N)\rfloor}.
\]
Every odd prime power of either local group size is at most $2N$. If $(r+1)_{\rm odd}$ is $B$-smooth at one prime $r\mid N$, the point $[U]R$ there is the torsion point whose label was just computed. The procedure does not need to know which label or prime it is. At the opposite prime, the two square classes of $[U]R$ are still those of $R$, since $U$ is odd. The point there therefore cannot be the same labeled torsion point, including when its odd part survives.

Compute $[U]R$ by checked modular doubling and addition. A one-sided infinity or exceptional denominator during the computation gives a proper gcd. When the resulting point is affine at both primes, test its abscissa against $0,d,-d$ by gcd. At the prime with the smooth odd part one of these abscissas is attained. Equality with that abscissa would force the same torsion point at the other prime, since a two-torsion abscissa has ordinate zero. Thus its gcd splits. The case of a zero label is the infinity test. The three public affine torsion abscissas and infinity suffice. A sieve and the largest prime powers construct $U$ at the cost stated above, using an integer product tree or applying the prime-power multipliers in succession. The initial scan and the chart data have polynomial bit size. Taking $\log B=O((\log N)^{1/3}(\log\log N)^{2/3})$ gives the one-third bound on this promise. [Checked modular group law](../experiments/cogentic-elliptic-cycle-split.py)

The fixed Gaussian norm-one construction already splits the same smooth-input class. At both primes its group has order $r+1$ and two-adic height two. A short prime $\ell\equiv1\bmod4$ with opposite Legendre signs yields a Gaussian ratio $\pi/\bar\pi$ of different local two-heights. Its powers at $U,2U,4U$ expose a one-sided identity under the same smoothness promise. The elliptic construction gives a rational marked point and extracts the divisor through its labeled torsion projection. [Gaussian norm-one comparator](cogentic-cm-torus.md#which-prime-bases-split-the-input)

For $N=209=11\cdot19$, the triple centered at $t=6$ has exactly two negative Jacobi values. With $d=210$ and $U=3$, the reduced outputs are $(10,0)$ modulo $11$ and $(5,14)$ modulo $19$. The first is $T_-=(-d,0)$, and the affine abscissa modulo $209$ is $43$, so $\gcd(43+d,209)=11$. This example has a surviving odd part on the second prime. The finite check verified 1,648 direct torsion projections against the bit table.
