# Evaluation at the common root of a monic pair

The [monic Eisenstein pair](cogentic-monic-pair.md) can be made to admit evaluation from both rings of integers to $\mathbb Z/N\mathbb Z$ using at most six gcds and a common linear perturbation. The same calculation can return a proper divisor. Evaluation of an explicitly supplied algebraic integer needs only exact arithmetic in the power basis. [Finite replay](../experiments/cogentic-monic-index.py)

## A constant-size choice of pair

For odd $N\ge9$, let $F,G,m,d$ be the scheduled construction with $F(m)=G(m)=N$ and $G-F=(X-m)X^d$. For $t=0,1,2$ put

$$F_t=F+4t(X-m),\qquad G_t=G+4t(X-m).$$

The degrees, leading coefficients, evaluation at $m$, and difference $G_t-F_t$ are preserved. The perturbation changes only nonleading coefficients by multiples of four, so both polynomials are still Eisenstein at two. For each $t$, compute both derivative gcds $\gcd(F_t'(m),N)$ and $\gcd(G_t'(m),N)$. If a gcd is strictly between $1$ and $N$, return it. If both gcds are one, accept the pair. Otherwise at least one gcd equals $N$. For each of $F,G$, at most one $t$ can yield a derivative zero modulo $N$, because the derivatives differ by $4(t-t')$, a unit modulo odd $N$ for distinct choices. There are three choices for two polynomials, so after any rejected choices the procedure must accept a pair or return a divisor. The gcd argument includes every prime-power modulus.

The height bound becomes $10m$ in place of $2m$. With $L=\log N$, $W=L^{1/3}(\log L)^{2/3}$, and $V=L^{2/3}(\log L)^{1/3}$, the resulting homogeneous norms for $|a|,|b|\le A\le\exp(cW)$ remain at most $\exp((1+c+o(1))V)$, since each degree is $(1+o(1))(L/\log L)^{1/3}$ and $\log m=(1+o(1))V$. Horner evaluation of the derivatives modulo $N$, the gcds, and the coefficient changes take $L^{O(1)}=\exp(o(W))$ bit operations.

## Clearing denominators at a simple root

Let $P$ be monic irreducible of degree $e$ with $P(m)\equiv0\pmod N$. Write $P(\alpha)=0$, $K=\mathbb Q(\alpha)$, $A_0=\mathbb Z[\alpha]$, and $D=P'(\alpha)$. Assume $\gcd(P'(m),N)=1$. For any $\beta\in\mathcal O_K$,

$$D\beta\in A_0.$$

Here is a proof that also specifies the integral numerator. For $v\in K$, let $\lambda(v)$ be the coefficient of $\alpha^{e-1}$ in the reduced power-basis representative of $v$. Lagrange interpolation at the distinct roots of $P$ gives $\lambda(v)=\operatorname{Tr}_{K/\mathbb Q}(v/D)$. Indeed, the leading coefficient of the interpolation polynomial for $v$ is the sum of its values at those roots divided by the corresponding derivatives. Thus

$$\lambda(\alpha^j D\beta)=\operatorname{Tr}_{K/\mathbb Q}(\alpha^j\beta)\in\mathbb Z\qquad(0\le j< e).$$

For $v=\sum_{i=0}^{e-1}v_i\alpha^i$, the expression $\lambda(\alpha^jv)$ equals $v_{e-1-j}$ plus an integer linear combination of $v_i$ with $i>e-1-j$. This follows by reducing powers of $\alpha$ using the monic integer polynomial $P$. Starting at $j=0$ and descending through the coefficients shows integrality of all $v_i$ for $v=D\beta$. Equivalently, the trace dual of $A_0$ is $D^{-1}A_0$.

Let $\varepsilon\colon A_0\to\mathbb Z/N\mathbb Z$ send $\alpha$ to $m$. Set

$$\bar\varepsilon(\beta)=\varepsilon(D\beta)\,P'(m)^{-1}\pmod N.$$

This is the unique ring homomorphism on $\mathcal O_K$ extending $\varepsilon$. Additivity follows from the formula. Multiplicativity follows by applying $\varepsilon$ to $(D\beta)(D\gamma)=D(D\beta\gamma)$ in $A_0$. Any extension must satisfy $P'(m)\bar\varepsilon(\beta)=\varepsilon(D\beta)$, which proves uniqueness. Equivalently, $A_0[D^{-1}]=\mathcal O_K[D^{-1}]$ and the power-order map extends to this localization.

To compute the numerator from an explicit rational power-basis representative $B(X)/h$ with $B\in\mathbb Z[X]$ and $h>0$, compute $C=\operatorname{rem}_P(P'B)$ over $\mathbb Z[X]$. Each coefficient of $C$ is divisible by $h$ by the trace argument. Check this divisibility and divide over $\mathbb Z$ before Horner evaluation. The inverse in the evaluation formula is the inverse of $P'(m)$. If the explicit representative has $S$ bits, using a common denominator increases total size by at most a polynomial in $S+e$. Polynomial multiplication and monic reduction use a polynomial number of integer operations and intermediate bit lengths $O(S+e\log(eH))$ when $S$ bounds the coefficient and denominator bits in the common-denominator form and $H\ge2$ is the height of $P$. For example, each of the fewer than $e$ descending reduction steps can increase the coefficient size by a factor at most $1+H$. Modulus operations use $O(L)$-bit inputs. Evaluation therefore costs $(S+L)^{O(1)}$ on the scheduled pair.

The global discriminant $\Delta_P$ can also be computed in $L^{O(1)}$ bit operations by an integer resultant. Its bit length is $O(e\log(eH))=O(L)$ by the Sylvester determinant bound. The identity $\Delta_P=[\mathcal O_K:A_0]^2\operatorname{disc}(K)$ makes $\gcd(\Delta_P,N)=1$ a sufficient global test. The derivative criterion takes place at the chosen root, so it permits index or discriminant primes at other roots modulo primes dividing $N$. It needs neither the order index nor a factorization of a discriminant.

## Application to products of marks

In the two fields, form $q_i=\pm\prod_{(a,b)\in S}(a-b\alpha_i)$ using the same sign and the same finite list $S$. Each $q_i$ lies in its power order. Any exact field square root $\beta_i^2=q_i$ is integral, by transitivity of integrality applied to the monic polynomial $T^2-q_i$. The evaluations above give two residues whose squares equal $\pm\prod_{(a,b)\in S}(a-bm)\pmod N$. If all the mark values are units modulo $N$, the residues are units as well. A proper difference gcd certifies a divisor in the usual way.

If the list has $R$ marks with $|a|,|b|\le A$, successive multiplication of a reduced representative by $a-bX$ and reduction by $P$ multiplies its coefficient bound by at most $(H+2)\max(1,A)$, since only one power of degree $e$ needs reducing. Its final coefficient bit lengths are therefore $O(R\log((H+2)\max(1,A)))=O(RV)$ on the scheduled grid. For $R\le\exp(O(W))$, both the explicit product size and its construction cost are $\exp(O(W))$. Evaluation of supplied square roots of comparable explicit size stays at that scale. This argument concerns finite products of integral marks. A negative exponent in a compact input requires its own treatment of denominators or a unit test in the target localization.

The local criterion also applies to a primitive mark at a known rational prime $p$ dividing its homogeneous norm. Then $b$ is a unit modulo $p$. If $r=a/b\bmod p$ is a simple root of $P$, the power-order prime $(p,\alpha-r)$ extends uniquely to a degree-one unramified prime of $\mathcal O_K$. In detail, localization at $D$ identifies the two orders there. Over $\mathbb Z_p$, the simple factor $X-r$ modulo $p$ lifts by Hensel's lemma and splits off a copy of $\mathbb Z_p$. Any prime ideal dividing $a-b\alpha$ lies over this same power-order prime at $p$, so the exponent at the lifted prime equals the rational valuation of the homogeneous norm at $p$. This permits local relation accounting at simple mark roots even when $p$ divides $\Delta_P$.

## Exact examples

- For $N=2385$, the scheduled raw quadratic is $F=X^2+2X+82$ with $m=47$. The integer $\beta=(\alpha+1)/9$ satisfies $\beta^2=-1$. Any extension would have $9\bar\varepsilon(\beta)=48\bmod 2385$, which is impossible because $9$ divides $2385$ and fails to divide $48$. The derivative gcd returns $3$.
- For $N=145$, the raw cubic derivative at $m=11$ is $145$, giving the full gcd. The shared shift $t=1$ supplies unit derivatives in both fields.
- For $N=895$ and $m=29$, the unperturbed cubic is $P=X^3-28X^2+54$, with $P'(m)=899$. Its discriminant is $4662900$ and its power-order index is $15$. For $\beta=(\alpha^2-\alpha+3)/15$, the monic characteristic polynomial is $T^3-51T^2+33T-5$. Multiplying by $D$ and reducing gives $51\alpha^2-22\alpha-90$. The correct evaluation is $42163/899\equiv472\pmod{895}$ using the inverse of $899$. The original denominator $15$ is a nonunit modulo $895$.
- For $N=11$ and $m=3$, the raw cubic $P=X^3-2X^2+2$ has $P'(m)=15$ and discriminant $-44$. Evaluation from the ring of integers works even when the global discriminant gcd is the entire modulus.

The perturbation changes the norm values, so the existence and discovery of simultaneous smooth relations must be established for the accepted pair. Neither this evaluation map nor an ideal parity dependency guarantees a field square. A square in both fields can yield the same sign at all primes dividing $N$, which also needs a separate argument for uniform splitting.
