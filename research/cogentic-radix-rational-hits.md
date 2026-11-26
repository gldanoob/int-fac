# Rational norm hits with mark contents

The [raw radix peeling bound](cogentic-radix-pair-peeling.md) extends to nonprimitive marks throughout \(0<c<(1+\sqrt{13})/6\), including on a proportion tending to one of balanced semiprimes. A shared rational prime can divide norms at different residue roots. A prime of that kind costs two congruences in the padded digit model. Summing their joint probability over the prime yields the same exponential bound used for primes dividing a mark determinant.

Use the previous notation, writing \(n_v\) for the norm in the even-degree field and \(H=\lfloor e^{cW_0}\rfloor\). Take any simultaneous square product, strip off its rational content and retain the primitive directions \(S\) whose total exponents are odd. The content has no prime divisors above \(H\), so the private ideal argument still gives \(S\subset B_r(z_0)\) at \(z_0=\log(2H^2)/W_0\). At the following cutoffs use the rational norm. A rational scalar contributes even prime valuations in this field, so
\[
 \sum_{v\in S}v_q(n_v)\equiv0\pmod2
\]
at every rational prime \(q\). Thus each odd prime of an anchor \(v\in S\) must also divide the norm of another direction in \(S\), possibly at a different ideal. This applies below \(H\) as well.

## Conditioning within a buffer

Fix \(k\) distinct directions and the padded central digits. At each direction \(v\), the independent buffer \(T\) of degree \(s=d-1-k\) gives \(n_v=B+\delta T(a_v,b_v)\), with one nonzero determinant factor for each of the other directions in \(\delta\). Put \(K=R h_v^s\) as before. Fix a squarefree modulus \(U\le (2H^2)^r\) with \(\gcd(U,\delta)=1\). Then
\[
 \frac1U-\frac1R\le \Pr(U\mid n_v\mid\text{center})\le \frac1U+\frac1R .
\]
Indeed, after fixing the other coefficients of \(T\), the coefficient of \(Y^s\) has one allowed class modulo \(U\), because \(b_v\) is coprime to \(U\). The inequality is uniform as \(U=o(R)\).

Conditional on this event, the possible norms lie in a single class modulo \(|\delta|U\). Divide by the common gcd of the new step and start to get a progression with coprime start and step. The conditional probability of any atom is \(O(U/K)\), by dividing the unconditioned atom bound by the conditioning probability. The original span is \(O(dK|\delta|)\), so the new progression contains \(O(dK/U)\) positions in this span. It follows that a prescribed divisor \(u\) of the normalized value has conditional probability \(O(d/u+U/K)\), and a shared prime with the normalized step makes divisibility impossible. The normalized magnitude bound remains \(X\ll dm h_v^{d+1}\).

Set \(K'=K/U\). Uniformly, \(\log K'=(1+x_v+o(1))V_0\) and \(X\le K'\exp(O_{k,r}(W_0))\). The primes removed with the new gcd divide \(\delta U\). Its primes above \(e^{zW_0}\) form a fixed set of size \(O_{k,r}(1)\), all bounded by \(\exp(O_{k,r}(W_0))\). Consequently the [square and smooth divisor estimates](cogentic-radix-pair-peeling.md#counting-marks-with-few-large-odd-valuations) apply verbatim with \(K'\) and this enlarged exceptional set. For every center and modulus under consideration they give
\[
 \Pr[v\in B_r(z)\mid \text{center},\ U\mid n_v]
 \le \exp\left(-\left(\frac{1+x_v}{3z}+o(1)\right)W_0\right).
\]
Congruences of this form at distinct marks use disjoint buffers, so they preserve independence conditional on the center.

## Summing the rational hits

Suppose \(S\subset B_r(z)\) and an anchor in \(S\) has \(r\) distinct odd norm primes above \(Y'=e^{z'W_0}\). They are all at most \(2H^2\) because \(S\subset B_r(z_0)\). Assign one neighboring norm hit to each prime and list the \(t\) distinct neighbors, where \(1\le t\le r\). Fix these \(t+1\) marks and a prime assignment. For a chosen prime \(q\), a required norm hit is impossible if \(q\) divides its mark denominator, by primitivity and monicity. The remaining hits fall into three cases.

- If \(q\) divides an anchor determinant, the anchor buffer perturbation vanishes modulo \(q\). Keep only the anchor hit, which fixes one class of the padded center's constant digit. The modulus here is coprime to the radix digit step because the prescribed input primes exceed \(2H^2\).
- If \(q\) divides a determinant between two neighbors but no anchor determinant, keep only the anchor hit. It fixes one congruence in the anchor buffer.
- If \(q\) divides none of the pair determinants, the anchor and assigned neighbor hits each fix a congruence in their respective buffer.

Distinct assigned primes give CRT conditions with products at most \((2H^2)^r=o(R)\) in every buffer and in the central digit. Conditional on all other central digits, the probability cost for the center is at most an absolute constant divided by its modulus. Conditional on an admissible center, multiply the independent buffer congruence probabilities, and then the conditional bounds on membership in \(B_r(z)\). The resulting probability for the tuple and prime assignment has the product of the \(t+1\) small-mark bounds, multiplied by \(O_r(\prod_q q^{-e_q})\), where \(e_q=1\) for the first two cases and \(e_q=2\) for the third.

For the fixed tuple of marks there are \(O_r(1)\) prime divisors above \(Y'\) among all its pair determinants, with \(z'>0\) fixed. Their reciprocal sum is \(O_r(1/Y')\). For primes outside those determinants use \(\sum_{n>Y'}n^{-2}\ll1/Y'\). Dropping the distinctness constraint after obtaining the product bound and summing over the finitely many choices of neighbor indices gives a cost \(O_r((Y')^{-r})\). This is the same cost as in the ideal-only argument. The sum over marks and the cutoff recurrence then show that \(S\) is empty throughout the original primitive parameter range. The odd-degree field forces the remaining rational scalar to be a square, so every simultaneous square yields a global sign. The estimate is uniform on the parity-split full boxes used for balanced semiprimes.
