# Unit signs in a real quadratic reduction cycle

Let \(N>1\) be odd and nonsquare and put \(\mathcal O=\mathbb Z[\pi]\), \(\pi=\sqrt N\). A change of transporter for the same oriented reduced ideal supplies at most one relative CRT sign bit. The bit is absent exactly when an element of \(\mathcal O\) has norm \(-1\), \(2\), or \(-2\). There are infinitely many odd squarefree composites with a four-step principal period for which this unit sign is trivial.

## The stabilizer of a fixed reduced ideal

Use proper invertible ideals and narrow equivalence by totally positive scalars. Fix a reduced ideal \(J\) of norm \(A\) prime to \(N\), and write \(I^2=\lambda J\) with \(\lambda\) totally positive and \(t=\operatorname{Nm}(I)\) prime to \(N\). A norm is the positive index for integral ideals and the signed field norm for elements. Reducing through \(\rho(a+b\pi)=a\bmod N\) gives \(z=\rho(A\lambda/t)\) and \(z^2=A\bmod N\), since \(\operatorname{Nm}(\lambda)=t^2/A\). The reduction extends to the localization at rational integers prime to \(N\); invertible ideals with norms prime to \(N\) become the unit ideal there.

The stabilizer of \(J\) consists of order units because \(J\) is invertible. The positively chosen norm-one Pell generator \(\epsilon=a+b\pi>1\) generates the totally positive units. Including an optional global sign makes the stabilizer for positive norm \(\{\pm\epsilon^j:j\in\mathbb Z\}\). Its sign image is therefore
\[
H=\langle-1,\rho(\epsilon)\rangle
\subseteq U_2:=\{u\in(\mathbb Z/N)^\times:u^2=1\},
\qquad |H/\{\pm1\}|\le2.
\]
In particular, full returns to the same oriented reduced ideal move \(z\) inside \(zH\). For \(k\) distinct odd prime divisors of \(N\), \(U_2/\{\pm1\}\) has rank \(k-1\). When \(k=2\) and \(\rho(\epsilon)\) is mixed, one parity bit of the unit exponent gives all relative signs. For \(k\ge3\) the unit orbit alone is smaller than the relative sign space. Distinct reduced ideals can have the same norm, and the stabilizer argument applies to a fixed ideal. [Lenstra, §§1 and 3](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/01lenstra.pdf#page=2) · [Schoof, Proposition 4.3 and reduction cycles](https://reneschoof.github.io/mcpaper.pdf#page=20)

## Exact criterion for the unit bit

Suppose \(a\equiv s\bmod N\) for \(s\in\{1,-1\}\). If \(a\) is odd then \(b\) is even, and the consecutive integers \((a+s)/2\) and \((a-s)/2\) are coprime. Their product is \(N(b/2)^2\), and \(N\) divides the second. They are therefore \(x^2\) and \(Ny^2\), respectively. Hence
\[
x^2-Ny^2=s,\qquad \epsilon=(x+y\pi)^2.
\]
The case \(s=1\) contradicts the minimality of the positive norm-one generator. The case \(s=-1\) supplies a norm-\(-1\) unit.

If \(a\) is even then \(b\) is odd, and the odd integers \(a+s\) and \(a-s\) are coprime, with product \(Nb^2\). The second is divisible by \(N\). Writing them as \(x^2\) and \(Ny^2\) gives
\[
x^2-Ny^2=2s,\qquad \epsilon=(x+y\pi)^2/2.
\]
These factorizations use all prime-power divisors of \(N\) on the same side and apply to nonsquare \(N\) with repeated prime factors.

Conversely, if \(\alpha\in\mathcal O\) has norm \(-1\), its square is a totally positive norm-one unit and is an odd power of \(\epsilon\). An even power would make \(\alpha=\pm\epsilon^j\) for an integer \(j\), contrary to its norm. Its square reduces to \(-1\). If \(\alpha=x+y\pi\) has norm \(2s\), then \(x,y\) are odd, so \(\alpha^2/2\in\mathcal O\) is a totally positive norm-one unit reducing to \(s\). Again its exponent is odd, since an even exponent would put \(\sqrt2\) in \(\mathbb Q(\sqrt N)\). It follows that \(\rho(\epsilon)\) has trivial relative sign precisely in these three cases. Otherwise \(\gcd(a-1,N)\) is a proper divisor. A supplied arbitrary unit \(\epsilon^j\) inherits the generator's relative bit exactly when \(j\) is odd.

## Short periods with and without a split

For odd \(m\ge3\), let \(N=m^2-2\). The element \(m+\pi\) has norm \(2\). Direct continued-fraction recurrence gives
\[
\sqrt{m^2-2}=[m-1;\overline{1,m-2,1,2m-2}],\qquad
\epsilon=m^2-1+m\sqrt{m^2-2}.
\]
Thus \(R_+=\log\epsilon=\log N+O(1)\), while \(\rho(\epsilon)=1\). The four convergent norms in the first period are \(-(2m-3),2,-(2m-3),1\). The repeated norm has numerators \(m-1\) and \(m^2-m-1\), which are negatives modulo \(N\), and \(\gcd(2m-3,N)=1\) by \(4N-(2m-3)(2m+3)=1\). Thus comparisons of equal norms among these convergents also give only global signs.

The progression \(m\equiv22837\bmod28322\) enforces odd \(m\), \(m\equiv3\bmod49\), and \(m\equiv6\bmod289\). It gives valuations exactly one at \(7\) and \(17\) in \(N\). Infinitely many values in this progression are squarefree, as can be seen directly by sieving prime squares. Among the first \(X\) parameters of the progression, CRT gives the product of the local surviving densities up to a fixed prime cutoff \(P\). That product is bounded below by a positive constant independent of \(P\), since outside \(2,7,17\) a prime square excludes at most two residues. Larger prime squares rule out at most \(O(X/P)+O(\pi_{\rm primes}(28322X+22837))=O(X/P)+o(X)\) parameters by summing the two-residue bound. Choose \(P\) large and then \(X\) large. These composite squarefree \(N\) have \(N\equiv3\bmod4\), so the order is maximal. This is a short-regulator family with trivial unit signs in the fundamental discriminant \(4N\).

For any fixed trial-division cutoff, the same construction can avoid every prime below it. There are infinitely many odd primes at which \(2\) is a square, since an odd \(m\) divisible by any proposed finite list gives \(m^2-2>1\) with an odd divisor prime outside the list. Choose two of these primes above the cutoff, prescribe valuation one at both, and impose \(m\equiv0\) at the small odd primes. The prime-square sieve applies to the resulting fixed progression.

For even \(m\ge4\), \(N=m^2-1\) instead has fundamental norm-one unit \(m+\sqrt N\) and \(R_+=\tfrac12\log N+O(1)\). Its residue is \(+1\) on \(m-1\) and \(-1\) on \(m+1\). The factors are odd and coprime. Both families have explicit polynomial-bit Pell units. [Lenstra, continued fractions and the \(m^2-1\) example](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/01lenstra.pdf#page=7)

## Obtaining a transporter or a unit residue

If a positive transporter \(\lambda\) is known, multiplying by a suitable \(\epsilon^j\) balances its two real embeddings. For \(q=\operatorname{Nm}(\lambda)\), choose \(j\) with \(|\log(\lambda\epsilon^j/\sqrt q)|\le R_+/2\). Both embeddings of \(A\lambda\epsilon^j/t\) then have size at most \(\sqrt A\,e^{R_+/2}\). Constraining \(j\) to a specified parity replaces \(R_+/2\) by \(R_+\). This controls the size of representatives after the ideal equivalence is supplied. Reduction can leave different reduced ideals in the same narrow class, and aligning them is a distinct computation in the cycle. [Schoof, §§4–5](https://reneschoof.github.io/mcpaper.pdf#page=24)

The dense Pell unit has \(a=\cosh R_+\) and \(b=\sinh R_+/\sqrt N\). Writing \(a\) in binary takes \(\Theta(R_+)\) bits. Recovering these integers by direct exponentiation of a numerical regulator and rounding can be certified using absolute regulator error \(O(e^{-R_+})\) with a sufficiently small constant, since the derivatives are of order \(e^{R_+}\). These costs concern the dense representation and that rounding method.

To obtain only the residue, a direct continued-fraction period traversal can propagate the convergent recurrence modulo \(N\). If \(\ell\) is the period length, the positive Pell solution uses \(\ell\) or \(2\ell\) steps according to its parity. The step data for the square root use \(O(\log N)\)-bit integers, giving \(O(\ell\,\mathrm{poly}(\log N))\) bit work for this traversal. Lenstra's period bounds give \(\Omega(R_+/\log N)\) and \(O(R_+)\) steps for that method. He also gives a rigorous infrastructure bound \((\sqrt{R_+}+\log N)\mathrm{poly}(\log N)\) for finding a compact power product for the fundamental Pell solution. A supplied power product can be read modulo \(N\) in polynomial time by the cited modular arithmetic for compact representations. [Period bounds](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/01lenstra.pdf#page=7) · [Compact arithmetic and infrastructure, §§5–6](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/01lenstra.pdf#page=11)

## Narrow class twists supply the remaining relative signs

The square-root classes in the narrow ideal group account for signs modulo \(H\). For a narrow two-torsion class with a representative \(T\) prime to \(N\), choose a totally positive \(\beta\) with \(T^2=(\beta)\). Its tag \([\rho(\beta)/\operatorname{Nm}(T)]\) lies in \(U_2/H\) and is independent of the generator and representative. Changing the generator multiplies by a norm-one unit. Rescaling by a totally positive \(\lambda\) that is locally a unit at \(N\) contributes \(\rho(\lambda^2/\operatorname{Nm}(\lambda))=1\). Product of ideals gives the homomorphism, and twisting \(I\) by \(T\) shifts its output root by the tag.

Such prime-to-\(N\) representatives exist in each narrow class. For an invertible ideal \(L\), choose a generator of \(L^{-1}\) locally at each rational prime dividing \(N\), and match those generators modulo \(pL^{-1}\) by CRT on the lattice \(L^{-1}\). The chosen multiplier generates \(L^{-1}\) locally at all those primes. Adding a large positive rational lattice multiple preserving the congruences makes the multiplier totally positive. Its product with \(L\) is integral and prime to \(N\).

For a unitary divisor \(d\) with \(de=N\), \(\gcd(d,e)=1\), take
\[
J_d=(d,\pi),\quad J_d^2=(d),\quad
T_d=\tfrac{d+\pi}{d}J_d=(d-e,\pi+e),\quad T_d^2=(d+e+2\pi).
\]
The two embeddings of the last generator are \((\sqrt d+\sqrt e)^2\) and \((\sqrt d-\sqrt e)^2\), both positive. The norm \(\operatorname{Nm}(T_d)=|d-e|\) is prime to \(N\). The tag \((d+e)/|d-e|\) gives opposite signs on \(d\) and \(e\), up to global sign. These classes surject onto \(U_2/H\). This complements the within-ideal unit orbit at the algebraic level. Sampling the narrow square-root fiber with factored norms and transporting to a common reduced ideal with a proved bit budget remain separate requirements. [Imaginary-quadratic sign calculation](keybreak-reduced-form-root-signs.md)
