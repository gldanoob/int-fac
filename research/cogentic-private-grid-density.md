# An obstruction on a one-third-scale grid

For every fixed \(0<c<1/\sqrt{12}\) there are infinitely many composite inputs \(N\) on the automatic raw monic schedule for which every ordinary primitive unit mark with nonzero numerator has an odd prime-ideal valuation private to that mark. This holds throughout the box

\[
 |a|,b\le \exp(cW),\qquad b>0,\qquad W=(\log N)^{1/3}(\log\log N)^{2/3}.
\]

Both derivatives are units, and every grid mark has unit value modulo \(N\). The inputs can have at least three distinct prime factors, with smallest prime factor larger than \(\exp(CW)\) for any fixed \(C\) once \(N\) is sufficiently large in the family. Thus the raw ordinary-mark route gives no productive simultaneous square on this box. The result is specific to this pair, this range of constants and ordinary marks. Larger boxes, other fields, and independent unit corrections remain available. [Raw pair](cogentic-monic-pair.md) · [Earlier fixed-slope CRT construction](cogentic-monic-productive-signs.md)

## A fixed progression of bases

Use the earlier scheduled family with arbitrary large odd prime \(d\), \(j\) the least positive integer with \(2^j/j>d^3\), and \(M=2^{d^2j}\). Vary \(m\) in the interval from \((1-1/(4d))M\) to \((1-1/(8d))M\), so \(N=m^d+2\) has scheduled degree \(d\) and polynomials \(F=X^d+2,\ G=F+(X-m)X^d\). Use \(L_d=d\log M\), \(W_d=L_d^{1/3}(\log L_d)^{2/3}\), and the fixed \(A=\lfloor\exp(cW_d)\rfloor\). This covers the stated box because \(\log N\le L_d\). We have \(d\sim(L_d/\log L_d)^{1/3}\), \(\log M\sim L_d^{2/3}(\log L_d)^{1/3}\), and \(\log M\log d/W_d^2\to1/3\).

Put \(y=2A^2,\ Z=2^{\lfloor d^2/1000\rfloor}\). For each nonzero primitive slope as above, write

\[
 F_{ab}=a^d+2b^d,\qquad C_{ab}=ba^d,\quad B_{ab}=a^d(a+b)+2b^{d+1},
 \qquad G_{ab}=B_{ab}-mC_{ab}.
\]

Choose distinct primes \(p,q\in(Z,2Z)\), neither 1 modulo \(d\), avoiding all \(F_{ab}\) and \(B_{ab}^d+2C_{ab}^d\). Each excluded integer is nonzero since \(-2\) is not a rational \(d\)-th power. Their product has logarithm \(O(A^2d^2\log(2A))=o(Z/\log Z)\). The prime number theorem and Brun–Titchmarsh leave \(\gg Z/\log Z\) primes in the interval outside the one excluded residue class. As in the [roughness construction](cogentic-monic-productive-signs.md#excluding-the-remaining-small-prime-factors), prescribe \(m\bmod p^2q^2\) so \(v_p(N)=v_q(N)=1\). Require \(m\) odd. There are \(K=M^{1-o(1)}\) consecutive indices in this progression of step \(2p^2q^2\).

The same roughness sieve leaves a fraction at least \(d^{-O(1)}\) of these indices with no prime divisor of \(N\) through \(Z\). To see that its estimates still apply, the number of forbidden residues modulo an odd prime \(\ell\le d\) is one, since \(d\) is prime. At other primes the bound is one unless \(\ell\equiv1\bmod d\), when it is at most \(d\). The excluded densities are all at most \(1/2\) and their sum is \(O(\log d)\), with the same bound \(20\log d\) for large \(d\). The odd Bonferroni truncation and CRT rounding estimate from the linked proof apply since \(K\ge\exp(2d^2\log d)\). The fixed primes \(p,q\) exceed \(Z\); parity already excludes 2. The cofactor \(N/(pq)>1\) is coprime to \(pq\).

## Counting columns that could survive

Uniformly over the fixed grid, \(M/3\le |G_{ab}|\le M^{1+c+o(1)}\). Indeed \(1\le |C_{ab}|\le A^{d+1}=M^{c+o(1)}\), \(|B_{ab}|\le4A^{d+1}=o(M)\), and \(m\sim M\). If \(a\) is odd then \(G_{ab}\) is odd. If \(a\) is even then \(b\) is odd and \(v_2(G_{ab})=1\). Write \(g=|G_{ab}|/2^{v_2(G_{ab})}\). Neither fixed prime divides \(g\) by the choices above. Also \(B_{ab},C_{ab}\) have no common odd prime: reduction at an odd divisor of \(a\) gives \(2b^{d+1}\), and at an odd divisor of \(b\) it gives \(a^{d+1}\). Hence an odd integer \(u\) dividing \(g\) must be coprime to \(2p^2q^2 C_{ab}\). For any prescribed odd \(u\), divisibility is impossible or selects a single class of progression indices modulo \(u\). Its fraction is at most \(1/u+1/K\).

If all prime valuations of \(g\) beyond \(y\) are even, write \(g=u s^2\) where \(u\) is the full \(y\)-smooth part. Choose fixed \(\kappa<1\) close to one and set \(D=M^\kappa\).

- If \(u<D\), the square divisor satisfies \(s\gg M^{(1-\kappa)/2}\) and \(s\le M^{(1+c)/2+o(1)}\). Summing \(1/s^2+1/K\) over these integers costs \(O(M^{-(1-\kappa)/2})+M^{-(1-c)/2+o(1)}\).
- If \(u\ge D\), it has a \(y\)-smooth divisor in \([D/y,D]\), by taking prime factors with multiplicity until the product first reaches \(D/y\). For \(\lambda=(1-\epsilon)\log d/\log y\) with fixed \(0<\epsilon<1\), the fraction of indices is at most
\[
 (D/y)^{-\lambda}\prod_{\ell\le y,\ \ell\ {\rm prime}}(1-\ell^{-1+\lambda})^{-1}+D/K .
\]
Here \(\lambda=o(1)\), and the logarithm of the Euler product is \(O(d^{1-\epsilon}\log\log(3y))=o(W_d)\), using the reciprocal prime sum and \(y^\lambda=d^{1-\epsilon}\). This gives at most \(\exp(-((1-\epsilon)\kappa/(6c)+o(1))W_d)\).

There are \(O(A^2)\) marks. Since \(12c^2<1\), take \(\kappa\) sufficiently near one and \(\epsilon>0\) sufficiently small that \((1-\epsilon)\kappa/(6c)>2c\). A union bound leaves at most an \(\exp(-\Omega(W_d))\) fraction of progression indices with even large-prime valuations at **any** nonzero slope. No independence between marks is used.

## Unit marks and trivial signs

On the rough indices, a nonunit mark would require a prime \(\ell>Z\) dividing both \(N\) and \(a-bm\). Such a prime divides \(F_{ab}\). Neither prescribed prime qualifies. For each remaining prime divisor of \(F_{ab}\), at most one class of indices modulo \(\ell\) gives this congruence, since \(\ell>b\). There are \(O(A^2d\log(2A))\) prime candidates counted with repetition. The fraction lost is \(O(A^2d\log(2A)(1/Z+1/K))\). This and the previous loss are \(o(d^{-C'})\) for any fixed \(C'>0\), so at least one rough index survives. Its derivative gcds are one because a common prime divisor would divide \(d\), \(m\), or \(d^d-2\); the latter has absolute value below \(Z\).

For every nonzero slope there is now a rational prime \(\ell>2A^2\) of odd valuation in \(|G_{ab}|\). Some prime ideal above it must have odd valuation in the principal ideal of the mark. That ideal cannot divide a second primitive direction: it would force \(\ell\mid ab'-a'b\), whose nonzero absolute value is at most \(2A^2\). This argument includes singular and index primes. Thus each nonzero direction must have even exponent in a field-square product. The zero direction has norm 2 and must have even exponent as well. Allowing repeated or nonprimitive marks only contributes a shared rational scalar from their contents, all of whose prime divisors are at most \(A\). Its norm in the even-degree field does not change the parity condition at two. Squareness in the odd-degree field forces the remaining scalar to be a rational square. Both roots then reduce to the same half-product up to a global sign, so every difference gcd is trivial.

The exact replay constructs a 1,375-bit example at grid height 40 with prescribed divisors 65,539 and 65,543. It selects its base using small-prime and unit checks, then verifies the nonsquare residual at each of 1,958 nonzero primitive slopes. It does not factor the large residuals. [Replay](../experiments/cogentic-private-grid-density.py)
