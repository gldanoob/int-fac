# Square classes of the planted sparse valuation columns

In the [private-row construction](cogentic-short-field-list.md), the $r$ planted columns have independent joint ideal parities. Their joint parity kernel is zero. Adjoining a common $-1$ leaves a one-dimensional parity kernel supported just on the sign. One field has odd degree, where the norm of $-1$ is $-1$, so the sign is nonsquare. This gives exact rank $r+1$ on the signed planted columns without any cutoff hypothesis. A normalized character matrix restricted to this parity kernel can have rank at most one. If it supplies no detecting row, the norm sign supplies it unconditionally.

## Individual square classes without new private rows

The same fields can be arranged so that each field's $r$ planted elements has independent real signatures, even though it owns only about half the private prime rows. Let $P(X)=\prod_j(X-t_j)$ for the cuts $t_j=2j$, let $K$ be the product of the selected private primes, and suppose the sparse construction has produced a pair $F_i$ at odd common argument $m$. Put $J=2r+1$ and assume $m>J$, as in the scheduled range. Replace each $F_i$ by

$$
  H_i(X)=F_i(X)+4K(X-m)P(X)(C P'(X)+s),\qquad s\in\{0,1,2\}.
$$

The change has degree at most $2r$ and preserves the degree, Eisenstein condition, marked values, common evaluation, and full reduction at every selected private prime. The derivative at $m$ varies by $4KP(m)$ per shift, a unit modulo $N$. Testing the three shifts therefore returns a proper gcd or makes both derivatives units, exactly as before.

Take $\epsilon=(8r)^{-r}$ and let $M$ bound the absolute value of $F_i(x)+4Ks(x-m)P(x)$ on $|x|\le J$ for both fields and all three shifts. One can compute $M$ by evaluating the two absolute-coefficient polynomials at $J$ and adding twice the absolute-coefficient value of $4K(X-m)P(X)$. Choose the integer $C>M/\epsilon$. On $[t_j,t_j+\epsilon]$, the derivative $P'$ retains its sign and has absolute value at least one. For $r\ge2$, this follows from $|P'(t_j)|\ge2$ and $\sup |P''|\le r(r-1)(2r)^{r-2}$ there. For $r=1$, $P'=1$. The mean-value theorem now gives $P(t_j+\epsilon)P'(t_j+\epsilon)\ge\epsilon$. The added term involving $C$ is negative at the right endpoint and has magnitude greater than $M$. Since the value at $t_j$ is the positive planted norm, each field has a real root in $(t_j,t_j+\epsilon)$. The bound on $M$ gives $\log C\le\log m+O(h\log h)$ on the sparse schedule, so the polynomial height and construction time retain their bounds.

Write $a_{ij}=t_j-\alpha_i$ in field $i$. At the real embedding from the root just to the right of $t_k$, $a_{ij}$ is negative exactly when $j\le k$. The resulting triangular sign matrix has rank $r$. For two possibly different integer exponent vectors $e_1,e_2$ and a shared sign $(-1)^\eta$, suppose both products $(-1)^\eta\prod_j a_{ij}^{e_{ij}}$ are squares. The odd-degree norm has sign $(-1)^\eta$ because all planted norms are positive, so $\eta$ is even. The two triangular signature tests then force both exponent vectors to be even coordinatewise. Conversely these parities give the explicit half-products as square roots. Negative exponents are permitted in the localization at unit residues.

## What an explicit correction can do

Let $\rho(w)=\prod_j(t_j-m)^{w_j}\bmod N$. The half-roots of the two corrected products have residue ratio $\rho(w)$ with $w=(e_1-e_2)/2$. Their squares coincide exactly when $\rho(w)^2=1$, and a proper gcd exists exactly when $\rho(w)\ne\pm1\pmod N$. Conversely, finding such a $w$ gives a correction by taking $e_1=2w$, $e_2=0$. Enumerating $|w_j|\le h$ costs $\exp(O(r\log h))$ bit operations up to polynomial factors in $\log N$. This tests an explicit bounded set of corrections. It gives no reason for a nontrivial root of unity to occur in that set on every input.

For a special input $N=m^4+m^2+1=(m^2+m+1)(m^2-m+1)$, take $h=4,r=2$ and an odd $m$ for which the sparse construction returns fields. The mark $t_0=0$ has label $-m$. Its cube is $-1$ modulo the first factor and $1$ modulo the second. Taking the sixth power of $a_{10}$ in the first field and the empty product in the other gives the two canonical roots $(-m)^3,1$ after reduction. At $m=15$, the replay builds both fields for $N=50851$, obtains residues $47476,1$ and verifies divisor $211$. This correction uses the special polynomial identity for $N$. The same modular calculation already supplies the divisor without field square extraction.

The replay checks the perturbation, private residues, and exact root brackets on three pairs. On these fixtures the normalized probes through 257 detect the sign-only parity vector in every case. The norm-sign proof covers all admissible inputs independently of that empirical cutoff. [Replay](../experiments/cogentic-planted-sparse-signs.py)
