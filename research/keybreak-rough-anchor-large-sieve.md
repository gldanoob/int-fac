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

## Removing the roughness condition for linear interior counts

For the linear interior, Dirichlet GRH also permits the full interval of anchor denominators. Here \(x\asymp MV\), \(T\ll MV^2\), \(V\le M^{v_*}\) for fixed \(2v_*<1\), \(\rho=M^{-o(1)}\) is the ordinary rational smooth density, and \(\ell\) is a prescribed prime. Use \(Q\asymp M\) uniform in a set of size \(\gg M/\operatorname{polylog}M\), then sample \(r\) uniformly among the units in the fixed interval at that \(Q\). The bound for \(\ell\nmid Q\) in G.13–G.14 has the original \(\ell/V^2\) scale up to polynomial logarithms, under the original strict principal-term margins. The following argument permits numerator and denominator elements divisible by factors of \(Q\); character zeros implement the required unit restriction. We state this extension for ordinary smooth interior numerators only.

For conductor \(d>R=M^\theta\) choose fixed \(2v_*<\theta<1\) and write \(Q=dj\). For each fixed \(j\), expand the extra condition \((n,j)=1\) in the induced character sum by Möbius inversion. Cauchy costs \(\tau(j)\) and leaves sequences \(c_{et}\psi(et)\) for \(e\mid j\), of squared norm at most \(E\); the factor \(\chi^*(e)\) is bounded by one. On \(d\asymp D_0\) use \(1/\phi(dj)\le1/(\phi(d)\phi(j))\) and apply the primitive large sieve over \(d\) to each fixed sequence. The contribution is at most
\[
 (D_0+T/D_0)E\sum_{j\asymp M/D_0}\frac{\tau(j)^2}{\phi(j)}.
\]
The last sum is polynomial in \(\log M\), since \(\tau(j)^2\le d_4(j)\), \(\sum_{j\le z}d_4(j)\ll z(1+\log z)^3\), and \(j/\phi(j)\ll\log\log(3M)\). Summing dyads gives \((M+T/R)E\operatorname{polylog}M\). Keeping the complementary quotient \(j\) fixed before the sieve prevents any unbounded divisor weight on its conductor. The twist average costs one as above. [Primitive multiplicative large sieve, Theorem 19.16](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf)

For \(1<d\le R\), the induced \(Q\)-character times the \(\ell\)-twist is nonprincipal since \((Q,\ell)=1\). The pinned smooth-character estimate on the numerator interval and the GRH prime-character estimate on the denominator interval bound the squared product by \(T M^{O(\epsilon)}\). These apply to the full imprimitive characters. Per conductor there are at most \(\phi(d)\) characters and the sum of their Parseval weights over its possible moduli is \(O(1/\phi(d))\) per character as above. Thus the small part is \(\ll R T M^{O(\epsilon)}\), smaller than \(M E\) for sufficiently small fixed \(\epsilon\). This comparison holds for the whole populations. When applying the same argument to cells, their smaller principal thresholds and the number of cells cost \(M^{o(1)}\); the fixed small-conductor margin absorbs this entirely. For the high-conductor large sieve use the actual cell energy and the original \(K^4\) bookkeeping.

For completeness, the ordinary smooth numerator population \(\mathcal A_Q\) in a dyadic interval or source cell, restricted by \((n,Q)=1\), has size \((1+o(1))|\mathcal A|\phi(Q)/Q\) uniformly. To see this using the pinned B.26–B.29, apply inclusion-exclusion to prime divisors up to \(z=(\log M)^4\), truncated at neighboring even and odd orders of size \(C\log\log M\). Every retained divisor \(e\) satisfies \(\log e=O((\log\log M)^2)\). Apply B.26 to the scaled interval, whose relative length is unchanged, and B.27–B.28 to compare its density with that on the full cell. In the interior scales \(u\asymp d\), \(1-\beta=O(\log d/\log B)\), and \(\log M\) is polynomial in \(d\). The divisor count is \((|\mathcal A|/e)(1+o((\log\log M)^{-2}))\) uniformly: the errors include \(O(1/u+\log(u+1)/\log B+(1-\beta)\log e+(\log e)^2/(\log x\log B))\). The absolute sum of the reciprocal divisor coefficients is \(O(\log z)\), and the truncated Euler-product tail is smaller than every fixed negative power of \(\log\log M\) by the factorial bound. The main fraction is at least a constant times \(1/\log\log M\). For \(q>z\) dividing \(Q\) with \(q\le B\), the scaled interval estimate and saddle ratio give relative mass \(O(q^{-\beta})\); larger primes cannot divide a smooth numerator. Their total is negligible even relative to that main fraction. The analogous ordinary Euler-product tail is also negligible. [Smooth-number estimates in the pinned source, Appendix B.4](https://crypto.sjtu.edu.cn/factoring.pdf#page=45)

The principal term for \(\ell\nmid Q\) is
\[
 \frac1{\phi(Q)}\sum_{b\in\mathcal B,\ (b,Q\ell)=1}
 \#\{u\in\mathcal A_Q:u\equiv vb\bmod\ell\}.
\]
Here \(\ell>B\), so the ordinary smooth numerators are already units modulo \(\ell\). Nonprincipal \(\ell\)-characters times the principal character modulo \(Q\) satisfy G.7, with the extra \(Q^\epsilon\) absorbed by the strict original power margin. The denominator interval loses at most \(\omega(Q)+1\) primes. The ratio \(|\mathcal A_Q|/\phi(Q)\) restores the original common normalization within bounded factors, including for the cell upper bounds. Primes \(b\mid Q\) could not have occurred at a rationally eligible point anyway, since then \(b\mid rb-Qa\) and \(b>B\).

Finally the exceptional denominators with \(\ell\mid Q\) have probability \(\ll (\operatorname{polylog} M)/\ell\) when nonempty. For fixed \(Q,r\), the raw root boxes satisfy \(\max_s R_s\ll(1+V/\ell)V/\log V\) and \(\sum_s R_s\ll V^2/\log V\), excluding \(b=\ell\). Hence their contribution to the normalized root-averaged second moment is \(\ll\operatorname{polylog}(M)(1/\ell+1/V)/\rho^2\). This is negligible on levels with a strict margin in \(\min(\log\ell,\log V)-2\log(1/\rho)\) compared with the required error scales. This last calculation covers the exceptional contribution to the rational count; any use of an inverse of \(Q\bmod\ell\) elsewhere must treat these labels separately.
