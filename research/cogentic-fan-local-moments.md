# Local moments at a fixed rational mark in a polynomial fan

Fix one input \(N\), an integer \(m\), and a degree-\(d\) polynomial \(f\in\mathbb Z[X]\) with \(d\ge2\), \(f(m)=N\) and leading coefficient \(c_d\). The fan is \(f_j(X)=f(X)+j(X-m)\). Its standard implementation takes \(f\) from the base-\(m\) digits of \(N\). The smoothness hypothesis in Fan Factories concerns the rational mark and the actual algebraic norms. The congruence law below holds for every fixed mark, including every rationally smooth one. [Fan Factories, Lemma 2.2 and §2.1](https://storage.googleapis.com/deepmind-media/papers/Fan_Factories_Multiple_Number_Fields_in_Factorization_Factories_and_Batch_NFS.pdf#page=7)

## Fixed divisor

For a primitive pair \((a,b)\) with \(b>0\) and \(r=a-bm\ne0\), put
\[
 U=b^df(a/b),\qquad T=rb^{d-1},\qquad g=\gcd(U,T)>0,\qquad
 A=U/g,\quad S=T/g .
\]
The homogeneous norm is \(F_j(a,b)=U+jT=gV_j\), where \(V_j=A+jS\) and \(\gcd(A,S)=1\). In a box with \(|a|\le M<m/2\), specifying \(r\) also specifies the pair if it exists, since two solutions would have numerators differing by a multiple of \(m\). Elsewhere we condition on the pair.

- If \(p\mid r\), primitivity gives \(p\nmid b\). The identity \(U\equiv b^dN\pmod r\) gives \(v_p(g)=\min(v_p(r),v_p(N))\). Thus the \(r\)-part of \(g\) is \(\gcd(r,N)\). If \(p\mid r\) and \(v_p(N)\ge v_p(r)\), the residual step is a unit at \(p\). If \(v_p(N)<v_p(r)\), the residual norms are all units at \(p\).
- If \(p\mid b\), then \(p\nmid r\) and \(U\equiv c_da^d\bmod p^{v_p(b)}\). This gives \(v_p(g)=v_p(c_d)\) when \(v_p(c_d)<v_p(b)\). Otherwise the lower-degree coefficients can affect \(v_p(g)\), which lies between \(v_p(b)\) and \((d-1)v_p(b)\). The \(b\)-part of \(g\) divides \(|c_d|^{d-1}\). In the bit-length construction \(m=\lfloor 2^{(n-1)/d}\rfloor\) and \(2^{n-1}\le N<2^n\), so \(c_d\le2\) for large \(N\) at the NFS degree. This part of \(g\) then has \(\log g_b=O(d)\).
- If \(p\mid N\) and \(p\nmid rb\), both \(T\) and \(S\) are units at \(p\). Divisibility follows the ordinary unit-step law.
- For \(i\ne j\), \(\gcd(V_i,V_j)=\gcd(V_i,j-i)\). The only shared residual primes divide the gap. In particular, if the fan has \(J\) consecutive indices, any prime \(p\ge J\) divides at most one residual norm.

All original norms carry \(g\). If \(g\) has a prime divisor above the algebraic smoothness bound, this mark has no smooth norm. If \(g\) is smooth for that bound, a nonzero norm is smooth exactly when its residual norm is smooth. Computing \(\gcd(r,N)\) also directly detects a proper divisor whenever \(1<\gcd(r,N)<N\).

## Exact congruence law

Fix index offsets \(h_1,\ldots,h_k\) and exponents \(u_1,\ldots,u_k\ge0\). At \(p\nmid S\), the events \(p^{u_i}\mid V_{j+h_i}\) impose
\[
 j\equiv -A S^{-1}-h_i\pmod{p^{u_i}}.
\]
They are compatible exactly when \(p^{\min(u_i,u_l)}\mid h_i-h_l\) for every pair \(i,l\). If compatible, their joint density in a complete residue system is \(p^{-\max_i u_i}\). At \(p\mid S\) the density is zero unless all the exponents are zero. For \(F_{j+h_i}\), replace every \(u_i\) by \(\max(0,u_i-v_p(g))\) in this law.

With \(v_p(0)=+\infty\), for two residual norms at \(p\nmid S\), this means
\[
 \Pr[p^u\mid V_j,\ p^v\mid V_{j+h}]
 =p^{-\max(u,v)}\mathbf 1_{\min(u,v)\le v_p(h)}.
\]
The ratio to independent marginals is \(p^{\min(u,v)}\) when compatible and zero otherwise. In particular two unit-step norms at a gap prime to \(p\) have mutually exclusive divisibility by \(p\). If \(p\mid h\), their indicators for divisibility by \(p\) are identical. Exact valuation probabilities follow by taking differences of these tail probabilities.

Across a finite collection of primes the compatible congruences combine into one residue class modulo the product of the corresponding prime powers. For \(j\) in any interval of \(J\) consecutive integers, the empirical probability differs from that complete-residue density by at most \(1/J\). This error bound applies to the entire intersection. It cannot give a relative bound when its modulus substantially exceeds \(J\).

## Fixed-order local moment costs

Write \(D=(\log N/\log\log N)^{1/3}\) and \(H=D\log\log N\). Consider a fixed number \(k\) of distinct offsets of size \(\exp(O(H))\), local weights \(p^{\eta\min(v_p(V),e_p)}\) at finitely many primes, and \(0\le\eta=O(1/D)\). Each \(e_p\ge0\) is an integer. Use the joint complete-residue distribution for the weights. Relative to the product of one-norm weight means, the joint moment differs by a factor \(\exp(o(H))\), uniformly in the offsets, the mark, the selected primes and the truncation exponents.

For the proof, let \(1+a_p\) be the one-norm mean at \(p\nmid S\). By summing the geometric valuation tails, \(a_p=O(p^{-1+\eta})\). Write \(\Delta=\prod_{i<l}|h_i-h_l|\). At \(p\nmid S\Delta\) at most one weight exceeds \(1\), so the joint moment is exactly \(1+ka_p\). The absolute log of its ratio to \((1+a_p)^k\) is at most \(k^2a_p^2/2\), summable uniformly over these primes. At \(p\mid\Delta\), \(p\nmid S\), the joint moment is between \(1\) and the one-variable moment at \(k\eta\), by Hölder. Its log ratio is \(O_k(p^{-1+k\eta})\). The sum over primes dividing \(\Delta\) is \(O(\log\log(3|\Delta|))\). Indeed, for \(x=(\log(3|\Delta|))^2\), terms with \(p\le x\) are bounded by a constant times \(1/p\), and the contribution above \(x\) is \(O(\log(3|\Delta|)x^{-1+k\eta})=O(1)\). Primes dividing \(S\) contribute weight \(1\). This proves the claim by the Chinese remainder theorem. The same bound for the original norms follows by factoring out their deterministic prime powers and lowering each truncation exponent accordingly.

If \(\log(3|S|)\le(\log N)^{O(1)}\), comparing the residual norms with the complete-residue local means of a uniform integer also costs \(\exp(o(H))\). Omitting the primes of \(S\) changes the logarithm of the moment ratio by at most \(O_k(\sum_{p\mid S}p^{-1+\eta})\), bounded by the same prime split. The fixed divisor \(g\) must still be accounted for when measuring the norm size and testing smoothness.

These are local moment ratios at an exponent on the NFS smoothness saddle scale. The CRT modulus for all weights in this calculation can exceed the length of the fan by a large margin.

## A second moment inside the actual fan

The following estimate works in every interval of \(J\) consecutive indices, including the standard fan. Let \(R\ge1\), \(Y\ge2\), \(0\le\eta\), and define the nonnegative multiplicative coefficients \(w_1=1\), \(w_{p^u}=p^{u\eta}-p^{(u-1)\eta}\) for \(u\ge1\). Define
\[
 W_R(n)=\sum_{\substack{q\le R,\ q\mid n\\ P^+(q)\le Y}} w_q,\qquad
 \mu_R=\sum_{\substack{q\le R,\ (q,S)=1\\ P^+(q)\le Y}}\frac{w_q}{q},
\]
with \(P^+(1)=1\). The divisor score can be used on signed values, with the convention that every positive \(q\) divides zero.

For a uniformly chosen index \(j\) in the interval,
\[
 (1-R/J)\mu_R\le\mathbb E W_R(V_j)\le(1+R/J)\mu_R.
\]
Moreover, for any integer \(h\),
\[
 \mathbb E[W_R(V_j)W_R(V_{j+h})]
 \le (1+R^2/J)\,\mu_R^2
 \sum_{\substack{t\le R,\ t\mid h\\(t,S)=1,\ P^+(t)\le Y}}
      t^{2\eta-1}\prod_{p\mid t}(1-p^{-\eta}).
\]
For \(h=0\) the restriction \(t\mid h\) holds for every \(t\). If both indices must be inside a given fan, take the averaging interval to be its overlap with its translate by \(-h\).

The first estimate counts one residue class modulo each eligible \(q\). For the second, expand over \(q_1,q_2\) and put \(t=\gcd(q_1,q_2)\). Compatibility requires \(t\mid h\), and the joint probability is at most \((1+R^2/J)t/(q_1q_2)\) since the modulus is \(\operatorname{lcm}(q_1,q_2)\le R^2\). Decompose \(q_1=tu,\ q_2=tv\) with \((u,v)=1\). Multiplicativity gives
\[
 w_{tu}w_{tv}\le t^{2\eta}w_u w_v\prod_{p\mid t}(1-p^{-\eta}).
\]
For each prime of \(t\), at least one of \(u,v\) has exponent zero, which supplies the displayed factor. After dropping the coprimality condition on \(u,v\) and allowing each up to \(R\), the remaining sum is bounded by \(\mu_R^2\).

The divisor sum in the bound, including at \(h=0\), is at most \(R^{2\eta}(1+\log R)\). If \(J\ge4\), \(R\le\sqrt J\), \(\log J=O(H)\) and \(\eta=O(1/D)\), Paley–Zygmund gives
\[
 \Pr\!\left[W_R(V_j)\ge\frac{\mu_R}{4}\right]
 \ge \frac{1}{32R^{2\eta}(1+\log R)}
 =\exp(-o(H)).
\]
This estimate holds for each fixed rationally smooth mark after removing its fixed divisor. The score measures smooth divisors up to \(R\). A norm can score well and still carry a prime above \(Y\), and the threshold \(\mu_R/4\) can even fall below the constant contribution from \(q=1\).

## The remaining smoothness estimate

For comparison, suppose a randomized choice of fan produces \(J\) norms at the fixed mark. Let \(C\) count nonzero \(Y\)-smooth norms, and take \(\pi=\exp(-sH+o(H))\) as a proposed one-norm probability. The estimates
\[
 \mathbb E C\ge J\pi\exp(-o(H)),\qquad
 \mathbb E[C(C-1)]\le J(J-1)\pi^2\exp(o(H))
\]
would give
\[
 \Pr[C\ge\tfrac12\mathbb E C]
 \ge \exp(-o(H))\frac{J\pi}{1+J\pi}.
\]
This follows directly from Paley–Zygmund and keeps the diagonal even when \(J\pi\) tends to zero. For sparse fans it would give a matching leading probability if the corresponding upper bound \(\mathbb E C\le J\pi\exp(o(H))\) also holds. Smoothness estimates of this kind for the actual perturbation window remain necessary. The randomized NFS literature proves an averaged result by using higher-degree perturbations and averaging smooth progressions over marks, with randomness in \(m\) and \(f\). [Lee and Venkatesan, Lemmas 5.40, 5.51–5.52 and §8](https://arxiv.org/abs/1805.08873)

The universal local law alone permits all \(J\) values to be nonsmooth even with \(g=1\). Take \(b=1,\ a=m+1\) so \(r=S=1\), choose distinct primes \(p_j>Y\), and replace the base polynomial by \(f(X)+c(X-m)\). The Chinese remainder theorem allows \(c\equiv -U-j\pmod{p_j}\) for each \(j\). A sufficiently large representative makes every norm nonzero, and each has its assigned prime divisor. This construction places no bound on the perturbation size. It shows why controlling the range and distribution of the base polynomial is essential to a smoothness theorem.

For one fresh input, obtaining the rationally smooth marks is part of that input's cost. All estimates here concern the algebraic fan on those marks for that same \(N\). They leave both the total relation yield and the supply of useful square dependencies open.
