# A reciprocal quartic search for a multiple of the fourth cyclotomic value

At index four, under the same uniform zero-free hypothesis as the general splitting theorem, a deterministic scan with **$O(H^2)$ candidate polynomials per height-$H$ round** suffices for any supplied positive multiple of $p^2+1$. Try the trial divisors in the usual round and the polynomials
$$
       X^4+aX^3+bX^2+s aX+s^2,\qquad s=A^2,\quad A\ge1,
$$
whose coefficients have absolute value at most $H$. To see sufficiency, specialize the cyclic-field construction to $k=4$. The projection polynomial $(X^4-1)/\Phi_4(X)$ is $X^2-1$. In the cyclic quartic field the resulting element has the form $\gamma=A\sigma^2(\alpha)/\alpha$, where the positive integer $A$ clears denominators. Its product with its opposite conjugate is $A^2=s$. Its degree is four: a generator of degree at most two would be fixed by $\sigma^2$, giving $\gamma^2=A^2$ and a rational element incapable of mixed reduction. The four conjugates thus pair with equal product $s$, giving the displayed coefficients. The earlier proof bounds their height and proves that the odd part of the supplied multiple distinguishes two primes. For each $A\le H^{1/4}$ there are $O(1+H/A^2)$ choices of $a$ and $O(H)$ of $b$, yielding the count. [Field construction, projective power and mixed signs](cyclotomic-order-multiples.md#choosing-a-field-in-which-the-primes-behave-differently)

### Exact-input classification

For the exact input $M=p^2+1$, the search uses its odd part $e=(p^2+1)/2$. Consider the full box through degree four on a balanced ordered pair of primes, $N=pq$. For fixed $H$ the limiting miss probability is determined entirely by three quadratic characters at $p$ for each relevant reciprocal quartic. In this classification $s$ may be any nonzero integer.

* At $p$, a unit in a quadratic, cubic, or reducible quartic quotient has projective order dividing $p(p^6-1)$ for $p>4$. Since $\gcd(e,p(p^6-1))=1$, its $e$th power is nonscalar. In an irreducible quartic write $\alpha$ for the root and $u=\alpha^{1+p^2}$. A scalar $\alpha^e$ forces $u$ to be a square in $\mathbb F_p$. Opposite Frobenius conjugates then have product $u$, so the coefficients $a,b,c,d$ satisfy $c=au$ and $d=u^2$ modulo $p$.
* If $p>H^3+H^2$, $c^2-da^2=0$ follows over the integers. For $a\ne0$, $s=c/a$ has integer square $d$ and is therefore integral. For $a=0$ we have $c=0$, and negation permutes the roots of the even irreducible quartic without a fixed point. It commutes with the Frobenius four-cycle and thus equals its square. This gives $u=-\alpha^2\notin\mathbb F_p$. There are no scalar inert cases with $a=0$.
* For the resulting reciprocal quartic set
$$
       D_1=a^2-4(b-2s),\qquad D_2=(b+2s)^2-4sa^2 .
$$
  Write it as $(X^2-uX+s)(X^2-vX+s)$ with $u,v$ the roots of $T^2+aT+b-2s$. Irreducibility modulo a prime outside the discriminants is equivalent to $(D_1/p)=(D_2/p)=-1$. Indeed the base quadratic must be irreducible, and $u^2-4s$ must be a nonsquare over $\mathbb F_{p^2}$, equivalently its norm $D_2$ is a nonsquare in $\mathbb F_p$. At an inert prime the opposite-root involution $\alpha\mapsto s/\alpha$ is Frobenius squared. Thus $\alpha^e$ is scalar exactly when $(s/p)=+1$.

On the cofactor side the gcd estimate in the prime-index argument applies unchanged with $\Phi_4(p)$ and $q(q^{12}-1)$. It uses only two fixed squarefree polynomials. Outside a vanishing fraction of pairs any scalar $X^e$ at $q$ comes from an integer scalar identity $X^g\bmod f$ for a divisor $g$ of $e$: take $g=\gcd(e,q(q^{12}-1))$ and bound the coefficients of the reduction by $(1+4H)^g$. If a relevant irreducible quartic admits such an identity, each ratio of two distinct roots is a root of unity of degree at most $4\cdot3=12$. Every prime dividing $e$ is one modulo four. Hence the ratio orders can involve only 5 and 13, each with exponent at most one, by the cyclotomic degree formula. It suffices to test whether $X^{65}$ is scalar over the rationals. If it is, the rational projective order divides 65 and both primes preserve it outside a finite set, so this polynomial can be omitted. A zero constant term either gives a pure nilpotent at both primes or precludes scalarity at both. Thus, asymptotically, the entire box misses exactly when all remaining triples of signs avoid the single hit pattern $(+,-,-)$. [Gcd tail and coefficient bound](prime-index-miss-density.md#uniformity-in-the-extra-multiplier-and-the-box)

### Finite probabilities

| Height | $p\equiv1\pmod4$ | $p\equiv3\pmod4$ | Both branches |
|---:|---:|---:|---:|
| 1 | $27/64$ | $3/4$ | $75/128$ |
| 2 | $15/64$ | $9/64$ | $3/16$ |
| 3 | $45/1024$ | $9/128$ | $117/2048$ |
| 4 | $19/1024$ | $1/128$ | $27/2048$ |
| 5 | $351/32768$ | $9/4096$ | $423/65536$ |

The probabilities are exact rational limits. Generate all $s,a,b$ with $s^2,|sa|,|a|,|b|\le H$, keeping $a>0$ since changing the sign of $a$ substitutes $-X$. Condition on $(-1/p)$ and average over all sign assignments of the remaining prime squareclasses by CRT and the prime number theorem in progressions. At height one the first branch gives three independent pairs of negative-character requirements, for $(13,-3)$, $(-7,2)$ and $(-11,5)$. Only $(13,-3)$ remains on the second branch. At height five, exact elimination gives the stated probabilities on 21 free binary signs. Independent literal powering checked every reviewed quartic with nonzero constant passing the torsion screen, including 13,308 polynomials at each of $157,167,173$. [Exact density replay](../experiments/quartic-miss-density.py) · [Literal modular powers](../experiments/quartic-miss-density.gp)
