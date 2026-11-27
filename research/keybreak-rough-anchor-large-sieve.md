# The rational large sieve with rough composite anchor denominators

The rational count in KeyBreak G.3 permits a positive family of composite anchor denominators whose small prime factors are excluded. This gives a way to test alternative anchor laws without imposing a prime coordinate. It addresses the existing *linear* rational calculation; smooth quadratic rational values require an additional estimate. [KeyBreak G.3](https://crypto.sjtu.edu.cn/factoring.pdf#page=107) · [Quadratic rational obstruction](keybreak-quadratic-mark-geometry.md#the-remaining-rational-smoothness-condition)

## Conductor sum

Let \(\mathcal Q\subset[3M/4,M]\) be a set of integers all of whose prime factors exceed \(R\ge1\). Fix a modulus \(\ell\) coprime to each \(Q\in\mathcal Q\). In the ratio congruence \(u\equiv vb\bmod Q\ell\), use the same finite numerator and denominator populations for every \(Q\). All their elements are units modulo every \(Q\ell\). Write \(c_n\) for their product convolution supported on \(n\le T\), and \(E=\sum|c_n|^2\). Use the unweighted populations or real nonnegative weights, so the absolute character sum for the ratio equals that of the product convolution. Subtract from the ratio count its characters principal in the \(Q\)-component; write the remainder as \(H_Q(v)\). Then
\[
 \sum_{Q\in\mathcal Q}\sum_{v\bmod Q\ell}^{*}|H_Q(v)|^2
 \ll (M+T/R)E .
\]

Indeed, decompose the CRT characters as \(\chi\bmod Q\) and \(\psi\bmod\ell\), with \(\chi\) nonprincipal. Its primitive conductor is \(d\mid Q\), \(d>R\). The induced and primitive character give the same value on the support of \(c_n\), including after multiplication by \(\psi(n)\). Parseval gives weight \(1/(\phi(Q)\phi(\ell))\). For each fixed \(d\),
\[
 \sum_{\substack{Q\in\mathcal Q\\d\mid Q}}\frac1{\phi(Q)}
 \le \frac1{\phi(d)}\sum_{3M/(4d)\le j\le M/d}\frac1{\phi(j)}
 \ll \frac1{\phi(d)} .
\]
The last sum is bounded uniformly by using \(j/\phi(j)=\sum_{e\mid j}\mu^2(e)/\phi(e)\), since \(\sum_{e\ge1}\mu^2(e)/(e\phi(e))<\infty\). On a dyad \(D\le d<2D\), this is \(O(d/(D\phi(d)))\). The classical primitive multiplicative large sieve applied to the fixed sequence \(c_n\psi(n)\) gives \(O((D+T/D)E)\). Summing these dyads and then averaging over the \(\phi(\ell)\) twists gives the claim. The twists themselves may be imprimitive. Coprimality of the support with the full \(Q\) is essential to the conductor reduction.

## Normalization on an interval of roots

Suppose \(|\mathcal Q|\gg M/\log M\), take \(Q\) uniformly, and then draw \(r\) uniformly among its units in \((M/2,3M/4]\). The count of these units is \(\asymp\phi(Q)\) by inclusion-exclusion with error \(O(2^{\omega(Q)})\). For each fixed \(Q\) and prime \(\ell\), the map \((r,s)\mapsto r-Qs\bmod Q\ell\) is injective as \(s\) ranges over roots modulo \(\ell\). Restrict it to the admissible units. For a linear interior box with \(E=|\mathcal A||\mathcal B|\asymp\rho M V^2/\log V\) and \(T\ll M V^2\), use reference size \(m_Q\asymp E/(\ell\phi(Q))\). Multiplicity one for \(c_n\) is the same smooth-numerator and prime-denominator argument used in G.3. The principal component still requires the source's progression and cell estimates at \(\ell\), and its normalization is now \(1/\phi(Q)\).

Averaging over the admitted roots as in G.13, the nonprincipal relative second moment is
\[
 \ll \frac{\log M\,\log V}{\rho}
       \left(\frac{\ell}{V^2}+\frac{\ell}{R}\right).
\]
For the root and denominator averages, the multiplier on the previous squared sum is bounded by \(\sup_Q 1/(|\mathcal Q|\,\ell\,\#r\,m_Q^2)\ll \ell\log M/E^2\). The same cell proof costs the original \(K^4\) for a \(K\)-by-\(K\) partition with the source cell bounds. When \(R\) is a fixed power of \(M\), \(\phi(Q)\asymp M\) uniformly. There is then a common comparable reference just as for prime \(Q\). An example satisfying the unit hypothesis at an interior level takes \(R\) above every numerator prime factor, every prime denominator, and every prescribed root modulus at that level. In a semismooth band the additional exceptional numerator prime must likewise be excluded from all \(Q\). These are estimates averaged over roots. A fixed root, another numerator law, or a bound for the full nonlinear construction does not follow from this conductor sum.
