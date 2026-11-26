# Multiquadratic models from one unfactored input

For an odd composite \(N\) and \(r\ge1\) with \(d=2^r\) polynomial in \(\log N\), a deterministic construction either finds a proper divisor of \(N\) or supplies a real multiquadratic field of degree \(d\) with a certified evaluation modulo \(N\). The construction takes time polynomial in \(d\) and \(\log N\). Its radicands are on the square-root scale in \(N\), and its explicit monic models have large marks on one-third-scale boxes. [Exact replay](../experiments/cogentic-multiquadratic-model.py) · [Square kernel on the supplied field](cogentic-multiquadratic-square-kernel.md)

## Independent radicals with known roots

Take the first \(r\) odd primes \(q_i\), returning any that divides \(N\). Put \(M=\prod_i q_i^2\), \(k=N\bmod M\), and \(T=\lfloor\sqrt{kN}\rfloor\). Here \(\gcd(N,M)=1\) and \(1\le k<M\). For each \(i\), use the Chinese remainder theorem to choose the unique \(u_i\in[T+M,T+2M)\) satisfying
\[
u_i\equiv N+q_i\pmod{q_i^2},\qquad
u_i\equiv0\pmod{q_j^2}\quad(j\ne i).
\]
If \(\gcd(u_i,N)\) is proper, return the divisor. If it equals \(N\), replace \(u_i\) by \(u_i+M\), which preserves the CRT residues and is a unit modulo \(N\).

Set \(D_i=u_i^2-kN\). Since \(kN\equiv N^2\pmod M\), one has \(D_i\equiv 2Nq_i \pmod{q_i^2}\) and \(D_i\equiv -N^2\pmod{q_j^2}\) for \(j\ne i\). The private odd valuations imply independence of the \([D_i]\) in the rational squareclass group. The field is \(K=\mathbb Q(\sqrt{D_1},\ldots,\sqrt{D_r})\), and evaluation on its integral radical order sends \(\sqrt{D_i}\) to \(u_i\bmod N\). Put \(s=\sqrt{kN}\). Every \(D_i\) lies strictly between \((M-1)(2s+M-1)\) and \(3M(2s+3M)\). In particular \(D_i=O(M^{3/2}\sqrt N+M^2)\) and \(\log M=O(r^2)\) by Bertrand's postulate.

The same evaluation is available for all integral elements of \(K\) given in the rational tensor basis. Write \(\eta_S=\prod_{i\in S}\sqrt{D_i}\) and \(D_S=\prod_{i\in S}D_i\). Distinct monomials are orthogonal under the trace pairing, with \(\operatorname{Tr}(\eta_S^2)=dD_S\). An integral element \(z\) has tensor coefficient \(\operatorname{Tr}(z\eta_S)/(dD_S)\) at \(\eta_S\), and the numerator is integral. Every denominator \(dD_S\) is a unit modulo \(N\). Thus the reduction of the radical order with these denominators inverted already evaluates all integral elements. This also applies to the exact field roots of products of integral marks, since such roots are integral.

## Monic defining polynomial with a simple modular root

For any integer \(t\ge5\), the element \(\theta(t)=\sum_{i=1}^r t^{i-1}\sqrt{D_i}\) is primitive. Its conjugates are all the signed variants of the sum, and they are distinct by linear independence of the radical monomials. Compute its monic minimal polynomial \(f_t\) by successively multiplying the two shifts of the preceding polynomial by \(\pm t^{i-1}\sqrt{D_i}\). The coefficients are integral at each step by invariance under the sign change. If \(m_t=\sum_i t^{i-1}u_i\bmod N\), then \(f_t(m_t)=0\bmod N\), and the derivative is
\[
 f_t'(m_t)\equiv
 \prod_{\varnothing\ne S\subseteq\{1,\ldots,r\}}
  2\sum_{i\in S}t^{i-1}u_i\pmod N.
\]

Put \(B=(d-1)(r-1)+1\). Test for prime divisors through \(B\), then try \(B\) consecutive integers starting at 5. For any prime divisor \(p\mid N\) remaining after trial division, each factor of the derivative is a nonzero polynomial modulo \(p\) of degree at most \(r-1\). The \(B\) choices are distinct modulo \(p\), so one avoids all the derivative zeros there. The gcd of that derivative with \(N\) is either one or a proper divisor. Candidates with gcd \(N\) can be skipped. Both the search and the polynomial reconstruction use polynomial bit time in \(d,\log N\). For reconstruction, all roots have polynomial bit length as a size bound, so elementary symmetric coefficient bounds also give polynomial bit lengths.

## Limits on mark sizes

The CRT bounds imply \(\max_i\sqrt{D_i}/\min_i\sqrt{D_i}<3M/(M-1)\le27/8\). In any sign conjugate of \(\theta(t)\), the total absolute value of the lower powers is at most \((27/8)/(t-1)\) times the smallest possible magnitude of the leading term, taken with \(\min_i\sqrt{D_i}\). For \(t\ge5\), every conjugate therefore has magnitude at least \(\min_i\sqrt{D_i}/8\gg N^{1/4}\). Given any fixed positive constant \(C\), marks \(a-b\theta\) with \(|a|\le \exp(CW)\), \(b\ge1\), and \(W=(\log N)^{1/3}(\log\log N)^{2/3}\) consequently have absolute norm at least \((cN^{1/4})^d\) for an absolute \(c>0\) and all sufficiently large \(N\). This exceeds the usual one-third-schedule norm scale \(\exp(O((\log N)^{2/3}(\log\log N)^{1/3}))\).

More generally any primitive generator in the supplied integral radical order has defining polynomial coefficient height \(\gg N^{1/4}\). If it is \(\sum_S a_S\eta_S\) with integers \(a_S\), the mean of the squares of its real conjugates is \(\sum_S a_S^2D_S\) by orthogonality. A nonconstant monomial contributes at least \(\min_iD_i\). The maximum root magnitude thus bounds the monic coefficient height from below via the usual Cauchy bound. The mark norm lower bound above concerns \(\theta(t)\). The order-based coefficient bound leaves possible primitive generators outside the supplied radical order open.

One can also exhibit fields whose height is large in every monic presentation. Replace the first private prime by a squarefree block \(Q\) of distinct odd primes, disjoint from the other markers, and replace its CRT offset by \(+Q\) modulo \(Q^2\). Each \(q\mid Q\) then has valuation one in \(D_1\). By accumulating small primes until their product exceeds \(N^\epsilon\) for fixed \(\epsilon>0\), one obtains \(N^\epsilon\le Q\le N^\epsilon(\log N)^{O(1)}\) with polynomial bit work, returning a divisor if a marker divides \(N\). The elementary bound that the product of primes up to \(x\) grows exponentially in \(x\) suffices. The discriminant of the quadratic subfield is divisible by \(Q\). If a monic polynomial of degree \(d\) and coefficient height \(H\) presents \(K\), the relative discriminant formula and Vandermonde bound give \(Q^{d/2}\le |\operatorname{Disc}(K)|\le d^d(\sqrt{d+1}H)^{2d-2}\). Thus \(H\ge Q^{1/4}/\sqrt{d(d+1)}\). This block construction supplies examples with a field-level height obstruction.

## Exact check

Run `/usr/bin/python3 -B experiments/cogentic-multiquadratic-model.py` with Sage's Python modules installed. The degree-16 model for \(10403\) and the degree-32 model for \(10007^2\cdot10009\) both used \(t=5\). The replay verified private valuations, radical and polynomial roots modulo the entire input, polynomial irreducibility, derivative formula and invertibility, and the dominance bound on the conjugates. It found the factors 7 and 103 on the respective inputs 77 and \(101^2\cdot103\).
