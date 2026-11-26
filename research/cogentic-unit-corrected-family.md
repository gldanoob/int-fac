# Splitting a rough polynomial family by unit-corrected field squares

Two nonisomorphic real quadratic fields can split the same input from one primitive mark even when neither sign of that mark is a square in either field. The correction uses explicit norm-minus-one units in their power orders. The inputs form an increasing degree-six polynomial family with coprime balanced factors. The parameter and the split can be recovered in polynomial bit time from the input alone. [Half ideals and the earlier split at 371](cogentic-half-ideal-relations.md) · [PARI replay and recognizer](../experiments/cogentic-unit-corrected-family.gp)

For every odd \(u\ge3\), set
\[
 h=(u-1)/2,\quad j=(u^3+1)/2,\quad A=j-uh,\quad B=j+uh,\quad N=AB .
\]
Both factors exceed one, are odd, and are asymptotic to \(u^3/2\). Indeed \(j\) and \(uh\) have opposite parities. A common divisor of \(A,B\) divides both \(u^3+1\) and \(u(u-1)\), whose gcd divides two. Thus the two factors are coprime. Expanding gives \(4N=u^6-u^4+4u^3-u^2+1\), increasing for \(u\ge3\). For \(u\ge5\) this lies strictly between \((u-1)^6\) and \(u^6\), since \(u^6-(u-1)^6\ge u^5\). The value \(u=3\) is covered by the same pair of candidates, the integer floor sixth root of \(4N\) and its successor. Checking the polynomial identity recognizes all and only members.

## The two square comparisons

Set \(m=(N-h^2)/u\), \(l=m+h\), \(k=m+j\). The first is integral because \(4N\equiv4h^2\equiv1\pmod u\). In the two power orders use
\[
 F(X)=X^2+X-k^2,\qquad G(X)=X^2-X-l^2 .
\]
Then \(G(m)=-N\) and \(F(m)=-(u^2+1)N\), using \(j^2-u^2h^2=N\). Both orders therefore admit the map \(X\mapsto m\bmod N\). The discriminants \(4k^2+1,4l^2+1\) lie between consecutive squares. The fields are nonisomorphic as well. The inequalities \(A\ge u^3/3\), \(B\ge u^3/2\) give \(m\ge u^5/6-u/4>j\), so \(l<k<2l\). Now
\[
 (4k^2+1)(4l^2+1)=(4kl+1)^2+4(k-l)^2<(4kl+2)^2.
\]
The discriminant product is a nonsquare.

With roots \(\alpha,\beta\) of the respective polynomials use the primitive marks \(-\alpha,-\beta\). Their norms are \(-k^2,-l^2\), so neither sign is a square in its quadratic field. Define \(U=2k-1-2\alpha\) and \(V=2l+1-2\beta\). They are integral units of norm \(-1\), by their quadratic equations, and satisfy
\[
 (k-\alpha)^2=(-\alpha)U,\qquad
 ((l-\beta)V)^2=(-\beta)V^3 .
\]
At \(m\) the units evaluate to \(u^3\) and \(u\). Thus the corrected squares agree modulo \(N\), and their two explicit roots evaluate to \(j\) and \(uh\). They are units since \(A,B\) are odd and coprime. Their difference and sum give exactly \(A,B\). The case \(u=3\) yields \(187=11\cdot17\). The program recovers the parameter and computes the divisors from the two field roots.

## How large can the least prime factor be?

For some absolute \(\delta>0\), at least \(X^{1/6-o(1)}\) distinct members up to \(X\) have every prime factor greater than \(N^\delta\). This statement allows composite blocks \(A,B\). To prove it, restrict \(t\le u\le2t\) to \(u\equiv1\) modulo a fixed multiple of 4 and of all primes up to 13. Such inputs avoid all these primes since the defining polynomial takes \(N(1)=1\). At any larger prime let \(\rho(p)\) count roots of \(4N(u)\bmod p\), so \(\rho(p)\le6\). For any squarefree \(d\) supported there, CRT gives the count of parameters with \(d\mid N(u)\) as \(T\rho(d)/d+O(\rho(d))\), where \(T\asymp t\) is the size of the fixed progression and \(\rho(d)=\prod_{p\mid d}\rho(p)\).

The fundamental lemma of the combinatorial sieve applies with dimension at most six. Indeed \((1-\rho(p)/p)^{-1}\le(1-1/p)^{-6}(1+O(p^{-2}))\), so Mertens' product estimate gives the required interval bound. Fix the sieve parameter \(s\) large enough that the relative fundamental-lemma error is below one half, and take \(y=t^{1/(2s)}\). The additive remainder is \(O(\sum_{d\le y^s}6^{\omega(d)})\le t^{1/2+o(1)}\), since \(6^{\omega(d)}=d^{o(1)}\). The Euler product is \(\gg(\log y)^{-6}\), giving \(\gg t/(\log t)^6\) retained parameters. Their values are distinct and \(N\asymp t^6\), so \(y>N^\delta\) holds for any fixed \(0<\delta<1/(12s)\) and sufficiently large \(t\). Choosing a dyadic parameter interval below the requested cutoff proves the count. [Lagarias, fundamental lemma of the combinatorial sieve](https://websites.umich.edu/~lagarias/675notes/Estimate5-2015.pdf)

Load the replay with `gp -fq experiments/cogentic-unit-corrected-family.gp`. In an interactive GP session, `unit_family_split(187)` returns the parameter and the two coprime factors after the script is loaded. The exact replay checks 250 parameters, their neighboring integers, and one 3,071-bit input. A general method for finding productive unit corrections on an arbitrary input remains open.
