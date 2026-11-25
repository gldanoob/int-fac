# The least Legendre mass of a set of central traces

For a prime $p>3$ let $\mathcal T_p$ consist of the nonzero integers $|t|\le\sqrt p$ with $p+1-t\equiv4\bmod8$. Write $M=\#\mathcal T_p$ and let $a_p(t)$ count the parameters $\lambda\in\mathbb F_p\setminus\{0,1\}$ with trace $t$ on $y^2=x(x-1)(x-\lambda)$. For every $1\le m\le M$, uniformly in $m,p$,
$$
 \min_{\substack{S\subseteq\mathcal T_p\\ |S|=m}}\sum_{t\in S}a_p(t)
 \ \asymp\ \frac{m\sqrt p}{\log(2+\log(M/m))}.
$$
Both constants are absolute. The lower and upper estimates hold with $a_p(t)$ replaced by its automorphism-weighted Kronecker class number $H(t^2-4p)$. We use Dirichlet GRH as proved by Alpöge and independently kernel-verified by Sutherland. For every fixed $\varepsilon>0$ a classical proof also gives both bounds uniformly for $m\ge p^\varepsilon$, with constants depending on $\varepsilon$. [Alpöge](https://alpo.ge/remark.pdf) · [Independent statement checks](https://math.mit.edu/~drew/grh/)

Lenstra's Proposition 1.9(b) and Shparlinski–Sutherland's reformulation give a lower bound with a $\log p$ divisor for arbitrary central order sets of cardinality at least three. David–Koukoulopoulos–Smith give a substantially more general framework of Euler products for vertical elliptic curve statistics, including asymptotics in short trace intervals. The theorem here allows adversarially selected central traces, gives matching upper and lower bounds for their least mass, and restricts the parameter family to untwisted Legendre curves. [Lenstra, Proposition 1.9](https://pages.cs.wisc.edu/~cs812-1/Lenstra1987.pdf#page=4) · [Shparlinski–Sutherland, Lemma 10](https://arxiv.org/pdf/1403.7887) · [David–Koukoulopoulos–Smith](https://dms.umontreal.ca/~koukoulo/documents/publications/random_euler_products.pdf)

## Both quadratic signs from a logarithmic mark prefix

Let $p$ be odd, let $a_1,\ldots,a_H$ be distinct in $\mathbb F_p$, $1\le H\le p$, and let $\chi$ be the quadratic character with $\chi(0)=0$. Fix $s\in\{-1,+1\}$. The number of $x$ for which **no** $i$ has $\chi(x-a_i)=s$ is at most
$$
 B(p,H)=p\,2^{-H}
       +\big(H/2-1+2^{-H}\big)\sqrt p
       +H.
$$
At most $2B(p,H)$ values of $x$ fail to realize both signs. These bounds also hold for $\chi(a_i-x)$ and, for one requested sign, for any fixed individual nonzero multipliers of the linear polynomials. In particular the signs to be tested at individual indices may be prescribed separately.

Away from the $H$ zeros the exact indicator of missing the prescribed signs is $2^{-H}\prod_i(1-s_i\chi(x-a_i))$. At a zero this expression is nonnegative, and at most $H$ zeros need to be added. For a nonempty set of $j$ indices the complete character sum of the product of its distinct linear polynomials has absolute value at most $(j-1)\sqrt p$ by the Weil bound; scalar signs multiply the sum by a unit. Averaging these estimates over subsets gives exactly $2^{-H}\sum_{j=1}^H\binom Hj(j-1)=H/2-1+2^{-H}$. Summing the two missing-sign bounds proves the assertion about both signs. For a target set of density $p^{-1/2}\log p=o(\gamma)$, taking $H=\lceil\log_2(4/\gamma)\rceil$ loses at most $\gamma p/2$ parameters for either fixed sign, for all sufficiently large $p$. Increasing $H$ by two gives the corresponding bound for the union of both missing signs. [Weil's multiplicative character bound, Theorem 11.23 in Iwaniec–Kowalski](https://bookstore.ams.org/coll-53)

## Class numbers as short products

Write $D=t^2-4p=dF^2$ with $d$ a fundamental discriminant, and $\chi_D$ for the possibly imprimitive Kronecker character. Throughout the central interval $3p\le |D|\le4p$. The imaginary quadratic order class number formula, including the automorphism weight at $d=-3,-4$, gives
$$
 \frac{H(D)}{\sqrt{|D|}}=
 \frac{L(1,\chi_d)}{2\pi}\prod_{\ell^a\parallel F}
 \left(\ell^{-a}+
   (1-\chi_d(\ell)/\ell)\sum_{j=1}^a\ell^{j-a}\right).
$$
The factor in parentheses equals one if $\chi_d(\ell)=1$ and lies between one and $1+2/(\ell-1)$ in every case. Keeping only the summand for the order of discriminant $D$ gives a second lower bound $H(D)/\sqrt{|D|}\ge L(1,\chi_D)/(2\pi)$.

Set $L=\log p$, $y=L^{10}$. Granville–Soundararajan's Lemma 2.1 with a zero-free rectangle to the right of $1/2$ yields
$$
                 L(1,\chi_D)\asymp\prod_{\ell\le y}(1-\chi_D(\ell)/\ell)^{-1}.
$$
Apply the lemma at $s=1$ to the primitive character of conductor $|d|\le4p$, with the common cutoff $y$, and include the prime powers exceeding $y$ from the primes at most $y$, whose sum is $o(1)$. Passing to the imprimitive character costs just the missing Euler factors at $\ell\mid F$ above $y$ of total logarithmic size $O(L/y)$. The constants are absolute. Thus, for $U_t=H(D)/\sqrt p$,
$$
 U_t^{-1}\ll \prod_{\ell\le y}(1-\chi_D(\ell)/\ell),\qquad
 U_t\ll \prod_{\ell\le y}(1-\chi_D(\ell)/\ell)^{-1}
             \prod_{\substack{\ell\le y\\\ell\mid F}}(1+C/\ell).
$$
The second inequality follows by absorbing the ratio between $\chi_d$ and $\chi_D$ at conductor primes into the correction factors. Each is $1+O(1/\ell)$ uniformly even for high valuations. [Short Euler products, Lemma 2.1](https://dms.umontreal.ca/~andrew/PDF/L1chi2002.pdf#page=6)

## Inverse moments at one prime

For every integer $1\le k\le L/(\log L)^2$ and sufficiently large $p$,
$$
       \frac1M\sum_{t\in\mathcal T_p}U_t^{-k}\le (C\log(k+2))^k .
$$
To prove this, drop the nonzero restriction and average on the complete central progression $t\equiv p-3\bmod8$. Its length is comparable to $\sqrt p$. The factor at 2 costs an absolute number to the power $k$. Expand the remaining short Euler product $\prod_{\ell\le y,\ell>2}(1-\chi_D(\ell)/\ell)^k$ as $\sum_n b_k(n)\chi_D(n)/n$. At $s=1/\log y$,
$$
 \sum_n |b_k(n)| n^{s-1}
 =\prod_{2<\ell\le y}(1+\ell^{s-1})^k
 \le \exp(O(k\log\log(3y))).
$$
Terms $n>p^{1/10}$ consequently cost $o(1)$ in absolute sum for the whole stated $k$ range. On the retained terms the average of $\chi_D(n)$ differs from the complete average over $t\bmod\operatorname{rad}(n)$ by $O(n/\sqrt p)$, since eight is invertible there. The total resulting error is at most $p^{-2/5}\exp(O(k\log\log(3y)))=o(1)$. Restore the complete product with the same tail bound.

For an odd $\ell\le y<p$, direct counting gives $\mathbb E_{t\bmod\ell}\chi_\ell(t^2-4p)=-1/\ell$. Indeed $v^2=t^2-4p$ has $\ell-1$ pairs $(t,v)$ by the change of variables $(t-v)(t+v)=4p$. For $\ell>k$ the expected local factor is at most $1+O((k+k^2)/\ell^2)$ by binomial expansion. Their product is $\exp(O(k))$. The remaining primes cost at most $\prod_{\ell\le k}(1+1/\ell)^k\le(C\log(k+2))^k$ by Mertens' bound. CRT factors the complete expectations and proves the inverse moment estimate.

For $\delta=m/M$ choose $k=\max(1,\lceil\log(1/\delta)\rceil)$ when it is in range. The restricted mean of $U_t^{-k}$ on any $m$ traces is at most $\delta^{-1}(C\log(k+2))^k$. The power-mean inequality gives a restricted arithmetic mean of $U_t$ at least $\delta^{1/k}/(C\log(k+2))$, as claimed. If $k$ is larger than the allowed range, $\log(2+\log(1/\delta))\asymp\log L$. The pointwise Euler product bound and Mertens give $U_t\gg 1/\log y\gg1/\log L$ at every trace. The exact untwisted Legendre identity gives $H(D)\le a_p(t)=2(H(D)-H(D/4))\le 2H(D)$. [Exact parameter-count identity](untwisted-legendre-partners.md#exact-untwisted-legendre-mass)

## Sets attaining the lower bound

First consider $\delta\to0$. Choose $z=\max(3,c\log(1/\delta))$ with a fixed sufficiently small $c>0$. Take the traces in the central progression with $\chi_\ell(t^2-4p)=-1$ at every odd $\ell\le z$. There are at least $(\ell-1)/2$ admissible residue classes at each such prime. Indeed the number of zeros is $1+\chi_\ell(p)$ and the sum of all character values is $-1$. Thus the CRT density $\beta$ among the progression is at least $3^{-\pi(z)}$. For sufficiently small $\delta$ this is at least $10\delta$, as $z=O(\log(1/\delta))$ and $\pi(z)=o(z)$. The modulus $Q=\prod_{2<\ell\le z}\ell$ is at most $p^{1/20}$ by reducing $c$ and increasing the absolute threshold for $p$. Each residue modulo $Q$ has the expected count in the progression up to one. Excluding zero discards at most one trace.

At each prescribed small odd prime the upper product for $U_t$ contributes exactly $(1+1/\ell)^{-1}$ since $\ell\nmid F$. Their product is $O(1/\log(2z))$. We claim the mean of the rest of the upper product over the allowed traces is $O(1)$. For $z<\ell\le y$ its factor is bounded above by
$$
 (1+O(1/\ell^2))\left(1+\frac{\chi_\ell(D)+C_1[\ell\mid D]}{\ell}\right)
$$
with a sufficiently large absolute $C_1$, using $\ell\mid F\Rightarrow\ell\mid D$. The product of the first factors is bounded. Expand the second product in squarefree $n$. Its local coefficient is a function of $t\bmod\ell$ bounded by $1+C_1$, and its complete mean is $O(1/\ell)$ because the quadratic has at most two roots and its character sum is $-1$. The complete product of the expected factors is therefore at most $\prod_{\ell>z}(1+O(1/\ell^2))=O(1)$.

For this last expansion truncation at $n=p^{1/10}$ has uniformly negligible cost, by the same Rankin estimate with fixed coefficient bound. Conditional on each single admissible progression modulo $8Q$, $\operatorname{rad}(n)$ is coprime to $8Q$. Replacing the average of its product of local coefficients by the complete average has error at most $O(Qn(1+C_1)^{\omega(n)}/\sqrt p)$. Summing the weighted errors and averaging the admissible progressions preserves the $o(1)$ bound, since $Q\le p^{1/20}$. The restricted mean of $U_t$ is consequently $O(1/\log(2z))$. Markov's inequality supplies at least half of these traces with that upper bound after doubling the constant. Any $m$ of them suffice. For $\delta$ above a fixed small positive threshold, the same unconditioned mean estimate with no prescribed prime bounds the total mass by $O(M\sqrt p)$, and the least $m$ have at most that mean. Bounded $p$ with $M>0$ can be absorbed in the absolute constants.

## Classical proof for polynomially many traces

Given fixed $\varepsilon>0$, Granville–Soundararajan's Proposition 2.2 gives the same constant-factor approximation to $L(1,\chi_d)$ with cutoff $y=L^{C_\varepsilon}$ outside at most $O(p^{\varepsilon/2})$ primitive characters of conductor at most $4p$, taking a sufficiently large constant $C_\varepsilon$. For fixed $p$ each negative fundamental $d$ occurs for at most twelve traces: $(t+F\sqrt d)/2$ is an algebraic integer of norm $p$, there are at most two ideals of norm $p$ and at most six units. Therefore $O(p^{\varepsilon/2})$ traces may be discarded. On the rest, bound their inverse moments by the full-progression positive short-product moment already proved, and use the pointwise product estimate on the rest for large $k$. Every set of $m\ge p^\varepsilon$ contains $m-O(p^{\varepsilon/2})$ retained traces. For the matching upper bound at $\delta\to0$, first bound the restricted mean of the finite product and then remove the exceptional characters. The supply exceeds $m$ by a fixed factor. When $\delta$ is bounded below and the set could require every exceptional trace, the total class mass on all central traces is $O(p)$ by Deuring's count of all elliptic curves. This gives the upper bound there as well. [Granville–Soundararajan, Proposition 2.2](https://dms.umontreal.ca/~andrew/PDF/L1chi2002.pdf#page=7) · [Deuring mass formula](https://dms.umontreal.ca/~koukoulo/documents/publications/random_euler_products.pdf)

The GP replay checked the order class formula and both Legendre inequalities for 3,606 traces in 427 fields, every minimum prefix mass in that range, 15,084 fixed-discriminant fiber counts and 455 complete CRT identities. The observed ratios to the scale in the theorem ranged from 0.1554 to 0.9026. These are finite ratios with the stated normalization. [Exact replay](../experiments/vertical-trace-subsets.gp)
