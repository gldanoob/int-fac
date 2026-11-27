# Actual norm heights in the ordinary terminal box

Under the ordinary KeyBreak coefficient law, a typical field has the predicted leading norm height simultaneously at every mark of a terminal box. This also holds over an exponentially bounded number of fresh field draws on the one-third scale. Selecting marks after observing the field cannot lower the actual heights by a fixed fraction of the radix-scale logarithm. The result concerns numerical size. Smoothness density and the cost of finding relations require separate arguments. [KeyBreak, (G.4), (G.5) and Lemmas G.4 and H.1](https://crypto.sjtu.edu.cn/factoring.pdf#page=105)

## The sampled form and a one-coordinate estimate

Write $H=(\log N)^{1/3}(\log\log N)^{2/3}$, $D=H/\log\log N$, and $n$ for the bit length of $N$. Let $M=\lfloor N^{1/d}\rfloor$, $Q$ be the public prime in $(3M/4,M]$, and $r$ be independently uniform in $(M/2,3M/4]$. In the Gaussian program of Appendices G and H the raw form is

\[
 F_{\rm raw}=F_0+2G R_c,\qquad G=QX-rY,\qquad R_c=\sum_{j=0}^{d-1}c_j X^{d-1-j}Y^j.
\]

Here $F_0(r,Q)=N$, $\|F_0\|_\infty\le(d2^d+2)M$, and $F_0$ is congruent modulo two to an irreducible degree-$d$ form. In particular, the coefficient of $X^d$ is odd. The degree is exactly $d$, and values at primitive marks are odd and nonzero. The raw content divides $N$ and is strictly smaller than $N$ by the finite height guard. If the content exceeds one, the program has a proper factor. Thus the form actually used on every continuing path is $F=F_{\rm raw}$. This uses the law of (G.4), which fixes the value at $(r,Q)$ to $N$. [KeyBreak, §H.1](https://crypto.sjtu.edu.cn/factoring.pdf#page=126)

In the ideal law the coordinates are independently distributed on $\mathbb Z$ with mass proportional to $\exp(-\pi c_j^2/\sigma^2)$. Its maximum atom is $O(1/\sigma)$ by summing over $[-\sigma,\sigma]$. Fix the environment and a mark $P=(a,b')$ with $G(P)\ne0$, and put $A_P=\max(|a|,|b'|)$. Vary $c_0$ when $|a|\ge |b'|$ and $c_{d-1}$ otherwise. Conditional on the other coordinates, successive values of $F(P)$ have spacing $2|G(P)|A_P^{d-1}$. For any $0<\eta<1$, the interval $|F(P)|<\eta|G(P)|\sigma A_P^{d-1}$ contains at most $1+\eta\sigma$ of these values. Consequently,

\[
 \Pr\bigl(|F_{\rm raw}(P)|<\eta|G(P)|\sigma A_P^{d-1}\mid r,Q\bigr)
 \ll \eta+\sigma^{-1}.
\]

The estimate is uniform in the center of the progression, so the construction of $F_0$ from $(r,Q)$ does not affect it. Lemma H.1 gives total variation error at most $e^{-n^{10}}$ for the whole vector and restricts a successful draw to $|c_j|\le\sigma n^{10}$. A union of mark failures is one event under that law, so its total variation error is charged once per field. A sampler failure has the source's ordinary epoch behavior. [KeyBreak, Lemma H.1](https://crypto.sjtu.edu.cn/factoring.pdf#page=127)

The same argument allows the fixed root systems used in the paper. Given the other coordinates, a compatible system restricts the chosen coefficient to one residue modulo some $m'\mid m$, where $m$ is the product of the distinct root primes. If $m\ll\sigma$, the Gaussian mass on any such residue class is $\gg\sigma/m'$, by the terms with $|c_j|\le\sigma$. The interval in the preceding bound contains at most $1+\eta\sigma/m'$ values in that class. This gives $O(\eta+m/\sigma)$ under the root-conditioned ideal law. The actual setup uses at most three root equations at primes at most $Y_1$ and has $\sigma/Y_1^3=\exp(\Omega(DH))$ at the stated schedule. The finite-law error after conditioning is $O(Y_1^3 e^{-n^{10}})$ by the root mass bound of G.4. The root conditions can change the progression even though its height estimate stays the same. [KeyBreak, Lemma G.4 and Proposition G.13](https://crypto.sjtu.edu.cn/factoring.pdf#page=110)

## Rational height and adaptive selection

The ordinary admissible box already prescribes $|G(P)|\asymp MV$ and $A_P\asymp V$ for coordinate scale $V$. The rational height can also be controlled before imposing that interval. For a fixed mark with $b'\ne0$, conditional on $Q$ the event $|Qa-rb'|<\eta M|b'|$ confines $r$ to an interval of length $2\eta M$. Its probability is $O(\eta+1/M)$. If $|a|\le2|b'|$, this also bounds the event $|G(P)|<(\eta/2) M A_P$. If $|a|>2|b'|$, then $|G(P)|\ge(3/8) M A_P$ deterministically, including $b'=0$. For primitive terminal marks with $0<b'\ll Q$, equality $G(P)=0$ is impossible because $\gcd(r,Q)=1$. The rational estimates use the original environment law, conditional only on $Q$. For a prescribed admissible fixed root system the ideal residue comparison in G.4 assigns essentially constant conditional mass to the system across admissible environments. For each prime that system has constant rank by the distinct evaluation vectors, and inadmissibility excludes at most one class of $r$ per marked root. Thus conditioning on such a fixed system preserves the rational estimate up to constant factors. [KeyBreak, rational environment and root law](https://crypto.sjtu.edu.cn/factoring.pdf#page=105)

Fix a cap $J=\exp(O(H))$ on the number of inspected fields, and include every integer mark with $|a|,|b'|\le\exp(O(H))$ in the chosen coordinate bound. The total number of field-mark slots is $\exp(O(H))$. For any fixed $\epsilon>0$, take $\eta=e^{-\epsilon DH}$. Because $\log M$ and $\log\sigma$ are $\Theta(DH)$, a union bound controls all the preceding small values with probability $1-e^{-\Omega(DH)}$. One can instead take $\eta=e^{-C H}$ with $C$ larger than the slot-count coefficient to obtain an $O(H)$ height error and exception probability $e^{-\Omega(H)}$. The same union applies when the order of examining the fields and the marks is chosen from the public history, provided every fresh field uses the stated law before selection. This follows by bounding the original draws or by conditioning on the past before each fresh draw. An arbitrary conditioning event of probability $p$ can increase the exceptional probability by at most $1/p$. In particular the statement with fixed $\epsilon$ survives events of probability $e^{-o(DH)}$, including the positive-probability good-field event. No claim follows from that division for arbitrarily rare preselected fields.

For the upper bound on the successful finite support, use the coefficient bounds on $F_0$, $|c_j|\le\sigma n^{10}$, and $|G(P)|=O(M A_P)$. The logarithmic slack over $M\sigma A_P^d$ is $O(d+\log n)=o(H)$. Together the estimates show that simultaneously on the ordinary terminal boxes of continuing fields,

\[
 \log|G(P)|=\log M+\log V+O(H),\qquad
 \log|F(P)|=\log M+\log\sigma+d\log V+O(H).
\]

The rational error is $O(1)$ on the prescribed band. Dividing either norm by a specified incoming prime of size $e^{O(H)}$ changes only the $O(H)$ term. In the schedule with $d\sim\delta D$, write $\ell=\log\sigma/\log M$ and $v=\log V/H$. The actual leading height coefficients on the $DH$ scale are $1/\delta$ and $(1+\ell)/\delta+\delta v$. The proof allows an adaptive choice of unusually small values inside a comparable-size box, and shows that this choice changes the heights only at lower order. Choosing a genuinely smaller coordinate scale is a different proposal law.

Lemma G.6 separately provides the fixed-mark, root-conditioned smoothness estimate. Numerical anti-concentration alone does not give it, an adaptive per-label upper bound on good candidate density, or a lower bound on the time of a selective search. The height part of the terminal ledger is already attained by the actual sampled norms at the leading scale. [KeyBreak, Lemma G.6](https://crypto.sjtu.edu.cn/factoring.pdf#page=111) · [Terminal height ledger](keybreak-asymmetric-terminal-budget.md)
