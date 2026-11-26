# Real ranks and square classes of the planted norm-two units

The [planted norm-two pair](cogentic-planted-norm-two.md) admits an even coefficient perturbation that puts a real root of each polynomial next to each planted cut. A constant perturbation proves that the \(r-1\) planted unit ratios are multiplicatively independent. A perturbation using the derivative of the cut polynomial also makes their real signatures independent modulo two. For the latter pair the planted marks alone yield only trivial square-root gcds.

## Bumps preserving the planted values

Use the planted construction's parameters \(h,m,r=\lfloor h/2\rfloor\), cuts \(t_j=2j\) and \(P(X)=\prod_{j=0}^{r-1}(X-t_j)\). The monic degree-\(h\) quotient \(Q\) has even nonleading coefficients and \(Q(m)=T\) for the odd representative \(0<T<2N\). Replace \(Q\) in the two defining polynomials by \(Q+C(X-m)H(X)\), with \(H=1\) or \(P'\). Explicitly, take
\[
 \begin{aligned}
 F_s &= 2+P\bigl(Q+(X-m)(CH+4s)\bigr),\\
 G_s &= 2+P\bigl(Q+(X-m)(CH+4s+X^h)\bigr),\qquad s=0,1,2.
 \end{aligned}
\]
Set \(\epsilon=(8h)^{-h}\), \(M=(64h)^{4h}\) and \(C=2M+8/\epsilon\). The bump has degree at most \(r<h\) in the quotient and even coefficients. Both polynomials retain the same degrees, Eisenstein conditions at two, and evaluations \(2\) at each cut and \(2+P(m)T\) at \(m\). As in the parent construction, changing \(s\) adds \(4sP(m)\) to both derivatives at \(m\). Since \(P(m)\) is a unit modulo \(N\), testing the three shifts yields either a proper gcd or a pair with both derivatives units modulo \(N\). The estimates below also allow adding the bump to an already selected pair and testing three further shifts, since the total constant shift in the quotient is at most 16.

For a bound on the unperturbed quotient, the final radix coefficient has absolute value at most \(2(m+2)^h/m^{h-1}+m+2\), using \(m^h\le N<(m+2)^h\) and the floor in signed radix extraction. Every coefficient of \(Q\) therefore has absolute value at most \(m8^h\). For \(x\) in \(I=[-1/2,t_{r-1}+1/2]\), we have \(|x|\le h\), \(m-x\ge1/2\) and \(m/(m-x)\le 4h\). The last estimate follows by considering \(m\ge2h\) and \(m<2h\). Consequently
\[
 \left|\frac{Q(x)}{x-m}\right|+16+|x|^h
 \le 4h(h+1)8^h h^h+16+h^h < M .
\]
The coefficient 1-norms of \(P\) and \(P'\) are at most \((1+2r)^r\) and \(r(1+2r)^r\). The modified pair thus has logarithmic height at most \(\log m+O(h\log h)\), preserving the scheduled one-third norm scale. The bump is explicit and has \(O(h\log h)\) bits.

At \(|x-t_j|\le\epsilon\), \(P'\) has the sign of \(P'(t_j)\) and \(|P'(x)|\ge1\). For \(r=1\) this is immediate. For \(r\ge2\) use \(|P'(t_j)|=2^{r-1}j!(r-1-j)!\ge2\) and \(\sup_I|P''|\le r(r-1)(2r)^{r-2}\), so variation in the interval is less than one. In either bump, at the two endpoints \(t_j\pm\epsilon\) the quotient multiplying \(P\) in \(F_s\) and \(G_s\) has the sign of \(-H(x)\) and magnitude greater than \(2/\epsilon\). Indeed its magnitude is at least \((m-x)(C|H(x)|-M)\). Since all other cuts are more than one away, \(|P(t_j\pm\epsilon)|\ge\epsilon\). At the endpoint where \(P\) has the sign of \(H\), the defining polynomial is therefore negative. It is positive at \(t_j\) itself. This brackets a distinct real root \(\alpha_j\) for each cut in each field. For \(H=1\) the root lies to the right or left according to the sign of \(P'(t_j)\). For \(H=P'\) each bracketed root lies in \((t_j,t_j+\epsilon)\).

## Multiplicative rank and signatures

For either field let \(\alpha\) be its defining root and \(a_j=t_j-\alpha\). Each \(a_j\) has norm 2 and generates the same prime ideal above 2. Indeed the reduction of the defining polynomial modulo 2 is a power of \(X\), so any prime above 2 contains \(\alpha\) and all \(a_j\). Each principal ideal \((a_j)\) has norm 2, hence is itself that prime. The ratios \(a_i/a_j\) are units, and the parent construction gives them in the power order.

Take the \(r-1\) units \(a_i/a_{r-1}\) for \(i<r-1\). Evaluate their log absolute values in the \(r-1\) embeddings at the roots \(\alpha_j\) with \(j<r-1\). The diagonal entries are at most \(\log\epsilon\). Every off-diagonal entry has absolute value at most \(\log(2r)\), since its numerator and denominator distances both lie in \([1,2r]\). The matrix is strictly diagonally dominant because \(-\log\epsilon>(r-2)\log(2r)\). Hence it is invertible and the planted units generate a free abelian group of rank \(r-1\). This includes rank zero when there is a single cut.

For signatures, use \(u_j=a_{j+1}/a_j\) for \(0\le j<r-1\), an equivalent basis. At a real root \(x\), the sign of \(u_j\) is negative exactly when \(x\in(t_j,t_{j+1})\).

- With \(H=1\) both quotients are strictly negative throughout \(I\). A root in a gap must have \(P(x)>0\), and each such gap has a bracketed root. The gaps with this sign are those with \(j\equiv r-1\pmod 2\). Any real embeddings outside the full cut range give every \(u_j\) positive. Thus the ratio signature rank over \(\mathbb F_2\), including all real embeddings, is exactly \(\lfloor(r-1)/2\rfloor\). The log rank leaves the square classes of the remaining totally positive ratios undecided.
- With \(H=P'\), the embedding at \(\alpha_j\) gives the \(j\)th negative-sign coordinate and every other coordinate positive for \(0\le j<r-1\). The embedding at \(\alpha_{r-1}>t_{r-1}\) gives every ratio positive. Including the unit \(-1\) therefore gives \(r\) independent signature columns. Thus \(-1,u_0,\ldots,u_{r-2}\) have independent square classes in each field. The two fields have the same signature rows at the bracketed roots.

## Consequences for correction products

Use the derivative bump. Any signed planted product has the expression
\[
 (-1)^\eta\prod_{i=0}^{r-1}a_i^{e_i}
   =(-1)^\eta a_0^{S}\prod_{j=0}^{r-2}u_j^{E_j},
 \qquad S=\sum_i e_i,\qquad E_j=\sum_{i>j}e_i .
\]
If this is a square, the valuation of the common prime above two forces \(S\) even. Then the signature at the last marked embedding forces \(\eta=0\bmod2\), and the other marked embeddings force every \(E_j\) even. Equivalently every \(e_i\) is even. Conversely these parities give an explicit square root. This proves that \(-1\) and the \(r\) planted elements have independent square classes in each field. When the same signed mark product is used in both fields, the canonical half-products reduce to the same unit modulo \(N\), and the only square roots in either field are the two signs of its canonical root. Thus the difference gcd is either \(N\) or \(1\).

More generally, correct the same signed mark product by \(\prod_j u_j^{c_j}\) in the first field and \(\prod_j u_j^{d_j}\) in the second. Let \(\rho(v)\) denote the common reduction modulo \(N\) of a planted unit product with exponent vector \(v\). Each square condition requires \(S\) even, \(\eta\) even, and respectively \(E+c\) and \(E+d\) even coordinatewise. In particular \(w=(c-d)/2\) is an integer vector. Equality of the two corrected residue values is exactly \(\rho(w)^2=1\). The two canonical square roots have residue ratio \(\rho(w)\), so their difference gcd is
\[
                    \gcd\bigl(N,\rho(w)-1\bigr).
\]
A proper divisor is obtained exactly when this quotient is a square root of unity other than \(1\) and \(-1\) modulo \(N\). For odd \(N\), every prime power dividing \(N\) divides exactly one of \(\rho(w)-1\) or \(\rho(w)+1\). Conversely, given any such \(\rho(w)\) from the planted unit subgroup, the unit corrections with \(c=2w,d=0\) on the empty mark product recover it. Thus correction products from this subgroup reduce precisely to finding a nontrivial square root of unity in its already-known modular image. For example, at \(N=85,h=4,m=3\) the adjacent unit has image \(57\), so \(57^8=16\pmod{85}\) is such a root. Using \(u_0^{16}\) as the correction in the first field gives the factor \(\gcd(85,16-1)=5\). A uniform deterministic procedure for finding such a root and the effect of units outside the subgroup remain open.

Run `python3 -B experiments/cogentic-planted-unit-signatures.py` to verify the endpoint signs, signature rows, coefficient parity and derivative-shift tests using exact rational arithmetic. [Replay](../experiments/cogentic-planted-unit-signatures.py)
