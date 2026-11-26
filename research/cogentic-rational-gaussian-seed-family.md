# Four coprime blocks from a public Gaussian seed polynomial

The fixed [Gaussian seed marks](cogentic-gaussian-smooth-seed-charts.md) give two independent sign reductions on an increasing degree-eight polynomial family. Their joint signs separate four explicit, pairwise coprime blocks. The polynomial parameter can be recovered directly from a public input, and the family has \(\Theta(X^{1/8})\) distinct values up to \(X\). The four blocks already have quadratic formulas in that parameter.

## Rational parameters and the unit conditions

Use \(k=11300+118650j\) for integers \(j\ge0\), and set

\[
 D=\frac{k^2-15}{5},\qquad
 S=\frac{10k^2-76k+150}{5},\qquad
 T=\frac{38k^2-300k+570}{5},\qquad
 N=4S^4+D^4 .
\]

These are positive integers. The identity \(T^2-15S^2=-56D^2\) is the rational parametrization of the Pell conic through \((38,10)\). It follows by intersecting the conic with \(t=38+k(s-10)\) and reversing the sign of the second point's \(t\) coordinate. Take \(r=2S^2/D^2\), which gives a Gaussian evaluation branch since \(r^2+1=N/D^4\).

To verify the denominators, a common odd prime divisor of \(5D\) and \(5S\) must divide \(75-19k\) and \(k^2-15\), hence divides \(75^2-15\cdot19^2=210\). The progression has \(k\equiv2\pmod3\), \(k\equiv2\pmod7\), and \(k\equiv0\pmod{50}\). Thus \(D\) is odd and coprime to \(S\), including at 5 since \(D\equiv2\pmod5\). In particular \(D,S\) are units modulo \(N\). A prime dividing both \(T\) and \(N\) must divide \(4\cdot56^2+15^2=113^2\), from the conic identity and the definition of \(N\). But \(k\equiv0\pmod{113}\) gives \(r\equiv200\) and \(N\equiv-D^4\not\equiv0\pmod{113}\). Hence \(T\) is a unit. The chart denominator \(r-1\) is a unit too, since \(r\equiv1\) at a divisor of \(N\) would give \(r^2+1\equiv2\) there. The three rational chart labels are units because their two matched products are \((2T/D)^2\) and \((2S/D)^2\).

## Exact sign blocks

The fixed Gaussian seed identities and the same projective charts now give

\[
 R_1=\frac{D^2+30S^2}{2TD}\pmod N,\qquad
 R_2=\frac{D^2+2S^2}{2SD}\pmod N .
\]

The field roots are unchanged. Only the arguments and rational labels use the rational chart evaluation. Subtracting and adding the displayed denominators gives four polynomial identities. With

\[
 A=k^2-8k+17,\quad B=13k^2-96k+181,\quad
 C=\frac{17k^2-120k+225}{25},\quad
 E=\frac{181k^2-1440k+2925}{25},
\]

they are

\[
\begin{array}{c|cc}
 & \text{numerator minus denominator} & \text{numerator plus denominator}\\\
 R_1 & 9AB & 25CE\\
 R_2 & AE & BC
\end{array}
\qquad N=ABCE .
\]

All four blocks are integers greater than one since \(25\mid k\). The identities show \(R_1^2=R_2^2=1\pmod N\). The factors 9 and 25 are units since \(N\equiv2\pmod3\) and \(N\equiv1\pmod5\). Every pair among \(A,B,C,E\) is separated by at least one sign partition. If two separated blocks shared a prime, it would divide both the numerator minus denominator and the numerator plus denominator of the corresponding ratio. That would contradict the unit denominator and oddness of \(N\). The blocks therefore are pairwise coprime. Refining by the two sign gcds recovers exactly these four blocks, each of which may itself be composite.

Each quadratic block is increasing for \(k\ge11300\). The resulting increasing polynomial in \(j\) has positive leading coefficient and degree eight. Binary search recovers \(j\) if the public input belongs to the family, with polynomial bit cost in \(\log N\). This is an explicit polynomial family of factored inputs. It gives no supply of these comparisons for arbitrary moduli.

Run `gp -fq experiments/cogentic-rational-gaussian-seed-family.gp` to check the polynomial identities, two one-variable inputs and one primitive two-variable input.

## A denser family from primitive parameters

Homogenize each quadratic formula for \(D,S,T,A,B,C,E\) at a pair \((k,\ell)\). This replaces every linear term in \(k\) by a term in \(k\ell\), and every constant term by its multiple of \(\ell^2\). Use positive coprime parameters with

\[
 11300\le k/\ell\le11400,qquad
 k\equiv11300\pmod{118650},\qquad
 \ell\equiv1\pmod{118650}.
\]

The four sign identities homogenize, and all blocks are positive integers greater than one. The same unit proof works. A prime common to the raw forms \(5D,5S\) cannot divide \(\ell\) by coprimality of the parameters. Otherwise substitute \(k/\ell\) at that prime and apply the same resultant 210. The residue conditions ensure that 2, 3 and 7 are excluded, and \(D\equiv2\pmod5\) even after division by 5. They also give \(r\equiv200\pmod{113}\) since \(\ell\equiv1\) there. Thus the two signs still separate four coprime blocks.

The number of such primitive pairs with \(K\le\ell\le2K\) is \(\Theta(K^2)\). For the count, use Möbius inversion over common divisors of \(k,\ell\), all coprime to the fixed progression modulus \(M=118650\). For a divisor \(q\le2K\), imposing it gives one lattice coset modulo \(Mq\) with the sector area as its main count divided by \((Mq)^2\) and error \(O(K/q+1)\). Summing the errors gives \(O(K\log(2K))\), and the density factor from the coprimality sum is \(\prod_{p\nmid M}(1-p^{-2})>0\). The resulting integers have \(N\asymp K^8\).

For a fixed \(N\), the number of ordered representations \(N=(2S^2)^2+(D^2)^2\) is at most \(4\tau(N)\), by the ordinary sum-of-two-squares formula. Each such representation determines positive \(S,D\), and the conic identity then determines positive \(T\). The slope

\[
 \frac{k}{\ell}=\frac{-T-38D}{S-10D}
\]

is uniquely determined since \(S-10D=(300\ell^2-76k\ell)/5\ne0\) in the sector. A positive primitive pair is recovered uniquely from its slope. Hence the multiplicity is \(N^{o(1)}\), and there are at least \(X^{1/4-o(1)}\) distinct inputs at most \(X\) with four certified sign blocks. This count uses supplied parameters. The one-variable recognizer above does not recover an arbitrary primitive pair from \(N\) in polynomial bit time.
