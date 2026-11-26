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

## Constructing the two marked orders for an arbitrary input

The same power-order units can be built for any odd \(N\) coprime to 15. More generally take an integer parameter \(t\) for which \(t,t-1,t+1,t^2+1\) are units modulo \(N\). Testing these four gcds separately can itself produce a divisor. In \(\mathbb Z/N\mathbb Z\), define
\[
 a=\frac{t(t-1)}{t+1},\quad b=\frac{t-1}{t(t+1)},\quad
 m=-\frac{(t^2+1)^2}{4t(t^2-1)},\qquad
 x=(a+1)/2,\quad y=(b-1)/2 .
\]
Then \(x^2=-ma\), \(y^2=-mb\), \(a/b=t^2\), and \(x/y=-t\). Lift \(m\) to an integer. Take \(l\equiv m+y\) in \([2N,3N)\) and take \(k\equiv m+x\) in \((l,l+N]\). This ensures \(l<k<2l\), so the earlier discriminant argument still gives two different real quadratic fields. The equations for \(x,y\) give \(F(m)\equiv G(m)\equiv0\pmod N\). Evaluation on the two power orders needs no condition on the derivatives. The field units \(U,V\) reduce to \(a,b\); each of the original signed singleton marks still has negative norm.

Multiplying the field roots \(k-\alpha,l-\beta\) by independent integer powers of \(U,V\) gives exactly the ratio coset
\[
           -t\langle a,b\rangle=-t\langle t^2,b\rangle .
\]
Its elements that square to one are the globally aligned square comparisons. A nonglobal sign splits the input. This gives a concrete family of group elements for the [general unit-alignment criterion](cogentic-monic-unit-corrections.md#criterion-once-base-corrections-are-available). At \(t=2\), which works for every odd input coprime to 15, the ratios are precisely \(-2^v3^w\) with \(v+w\) odd: the two powers give \((v,w)=(1+i+j,-i+j)\) for \((i,j)\in\mathbb Z^2\). For \(341\), taking \(i=j=2\) gives the ratio \(-32\) and the split \(11\cdot31\). After loading the GP script, use `unit_parameter_chart(N,t)` to build the orders and `unit_parameter_match(N,t,i,j)` to test the two powers. The replay checks 492 eligible charts and distinguishes a parameter gcd from the square comparison in separate fixtures.

Any fixed finite menu of eligible integer parameters has infinitely many semiprimes on which every globally aligned comparison in these generated units gives a global sign. Discard parameters identically ineligible and take \(M\) divisible by 8 and the odd prime factors of every nonzero numerator and denominator in the parameter, its eligibility tests and the two rational unit values. Choose distinct large primes \(p,q\equiv-1\pmod M\) by Dirichlet's theorem. Every positive supported prime is a square modulo both: for 2 use the residue modulo 8, and for odd primes apply quadratic reciprocity at the residue \(-1\). Both \(p,q\) are 3 modulo 4. Hence every signed rational word in the fixed factors has matching quadratic characters at \(p,q\). On an involution these characters distinguish \(+1\) from \(-1\) at both primes, so only the two global signs can occur. This argument also applies when words from different fixed charts are combined. It leaves open input-dependent parameter selection and comparisons that share a root at just one factor of the input.
