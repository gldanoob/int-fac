# Averaging projective residue errors over row labels

This is a residue estimate for the **full** prime-denominator interval in the projective trace construction. It replaces a pointwise numerator progression estimate by an absolute error averaged over the main-band row residues. The height condition is $c>b$, including when the product of the two row primes exceeds the length of a numerator interval. The estimate also applies after fixing a slope class modulo a small auxiliary modulus. [Projective trace](cogentic-projective-trace.md) · [Exact finite replay](../experiments/cogentic-prime-denominator-residues.py)

## A rectangular inequality

Take intervals $I\subset[-A,A]$ and $J\subset[2,A]$. Restrict $a\in I\cap\mathbb Z$ to a fixed residue $a_0\bmod t$, and restrict prime denominators $b\in J$ to a unit class $b_0\bmod t$ and to $(b,Q)=1$. Assume $(Q,t)=1$. For each $g\mid Q$, put $q=Q/g$ and let $E_g$ be the allowed numerators with $(a,Q)=g$. Define multiplicities $u_g(x)$ of the reductions $a/g\bmod q$ for $x\in U_q=(\mathbb Z/q\mathbb Z)^\times$. Let $P$ be the number of allowed denominators, and let $C(gr)$ count slope $gr\bmod Q$ for $r\in U_q$. The group $U_1$ has just its trivial character.

For any denominator multiset, Parseval on $U_q$ gives the exact identity

$$
\sum_{r\in U_q}\left|C(gr)-\frac{|E_g|P}{\phi(q)}\right|^2
=\frac1{\phi(q)}\sum_{\chi\ne 1}|\widehat u_g(\chi)|^2
\left|\sum_b\chi(b)\right|^2. \tag{1}
$$

Indeed $b$ preserves the gcd stratum and $a\equiv grb\pmod Q$ if and only if $a/g\equiv rb\pmod q$. The Fourier coefficients of this multiplicative convolution have the factors on the right. Also $\sum_x u_g(x)^2\le(1+2A/Q)|E_g|$, since a fixed $a/g\bmod q$ fixes $a\bmod Q$.

Assume primitive Dirichlet GRH. Every nonprincipal character in (1) satisfies

$$
\left|\sum_b\chi(b)\right|\ll \sqrt A\,\log^C(2AQt)
$$

for an absolute $C$. Expand $1_{b\equiv b_0\bmod t}$ into characters modulo $t$. Every product with $\chi$ is nonprincipal by CRT, including when either factor is induced. Its prime sum on $J$ follows by partial summation and removal of prime powers from the primitive $\psi$ bound. The primes lost at the modulus of an induced character or at $Q$ cost at most $O(\log(Qt))$. One may also delete a common exceptional set of $R$ denominators, adding $R$ to the bound. [GRH primitive character bound, Theorem 1.1 and equation (4)](https://academic.oup.com/qjmath/article/74/4/1505/7240642)

Thus the squared error on $U_q$ is at most $O(A\log^{O(1)}(2AQt)(1+A/Q)|E_g|)$ if $R\le\sqrt A$. By Cauchy and $\sum_{g\mid Q}\phi(Q/g)=Q$, the total absolute error relative to the individual stratum means is at most

$$
O\!\left(\log^{O(1)}(2AQt)\sqrt{Q A(1+A/Q)|I\cap\mathbb Z|}\right). \tag{2}
$$

For comparison with the single uniform mean $|I\cap(a_0+t\mathbb Z)|P/Q$, pay in addition at most

$$
2P\sum_{p\mid Q}(2A/p+1)+2|I\cap\mathbb Z|P\sum_{p\mid Q}1/p. \tag{3}
$$

The first sum bounds the actual nonunit mass and the second bounds the uniform nonunit mass. Off the nonunit strata the difference of the two constants over all units is bounded by the sum of those masses. In particular no assertion of relative equality at slope zero, or at any other particular slope, is needed.

## Primitive counts and weighted windows

For any $h\ge1$, a specified slope $a\equiv rb\pmod h$ has $O(1+A^2/h)$ primitive integer pairs with $|a|,|b|\le A$. To see this, use the lattice with that congruence, of determinant $h$. If its points in the box span at most one dimension, only the two possible primitive representatives on that line can occur. Otherwise a shortest nonzero lattice vector $u$ has length $O(A)$ and extends to a lattice basis. The parallel rows have separation $h/|u|$, and since a vector in the box is independent of $u$, $h/|u|=O(A)$. There are $O(A|u|/h)$ rows and $O(A/|u|)$ points per row. This bound includes exceptional slopes and is unconditional.

For the asymptotic application, let $z=\log\log N$, $A=\exp((c+o(1))H)$, $B=\exp((b+o(1))H)$, and assume $c>b>0$ and $z^C=o(H)$ for every fixed $C$. Take the denominator primes in the full prescribed interval of length $A\exp(-O(z^2))$, excluding primes dividing a nonzero integer $K$ of polynomial bit length in $\log N$. Let the numerator windows have endpoints of the form $a=\gamma b$, with $0<\gamma<1$, and lengths comparable to $A\exp(-O(z^2))$. All marks are then primitive. Let weights be bounded by 1, with Lipschitz constants at most $\exp(O(z^2))/A$ in both variables on each window. The weight bound can be multiplied by any common scale. Normalize sums by the number $Z$ of unfiltered marks in a window. On GRH, $Z\ge A^2\exp(-O(z^2))$ since the denominator interval has that length and the total number of deleted denominators is polynomial in $\log N$.

Let $Q$ be the product of at most two distinct main-band primes, each at least $B^{1-o(1)}$, all coprime to a small auxiliary modulus $t_0\le\exp(C_0z^2)$. Fix a residue at $t_0$. Write $C_r$ for the weighted sum of marks at this residue and slope $r\bmod Q$, imposing $(a-mb,K)=1$. For every fixed $D>0$ the following estimate holds for large $N$.

$$
\frac1Z\sum_{r\bmod Q}\left|C_r-\frac1Q\sum_{s\bmod Q}C_s\right|
\le e^{-Dz^2}. \tag{4}
$$

Equivalently, this is the average over $r$ of the absolute error in the hit weighted by $Q$. The constant $D$ can absorb any fixed $\exp(C_1z^2)$ factor from summing over small auxiliary classes.

Here is the error accounting in (4).

1. Delete the restrictions at primes of $K$ larger than $\exp(C_2z^2)$ temporarily. In the sum over $r$ each deleted mark is counted once. The lattice bound with $h=p$, divided by $Z$, bounds the mass lost by $\exp(O(z^2))\sum_{p\mid K,\,p>\exp(C_2z^2)}(1/p+1/A^2)$. Choose $C_2$ large. Denominators dividing $K$ remain deleted throughout.
2. Truncate inclusion–exclusion on the remaining primes at $j=\lceil z^2\rceil$ levels. The pointwise truncation error is at most the sum of the indicators that all primes of a $(j+1)$-element subset divide $a-mb$. The absolute slope-averaged mass is bounded by

   $$
   e^{O(z^2)}\left[\frac{(\sum_{p\le e^{C_2z^2}}1/p)^{j+1}}{(j+1)!}
   +\frac{e^{O(z^4)}}{A^2}\right].
   $$

   The prime reciprocal sum is $O(\log(z+2))$, so this is smaller than $e^{-Dz^2}$ for any fixed $D$. This use of the lattice bound allows all CRT slopes, including rare ones.
3. Partition into square panels of side $A\exp(-C_3z^2)$, with $C_3$ large. The boundary panels have $O(A^2e^{-C_3z^2}+Ae^{O(z^2)})$ integer pairs even with primality ignored. On the interior panels freeze the weight at a point, losing at most $\exp(O(z^2)-C_3z^2)$ per mark. Apply this **once to the filtered count before expanding it**, so the error does not multiply by the number of inclusion–exclusion terms.
4. Each truncated term imposes $a\equiv mb\pmod u$ with $u\le\exp(O(z^4))$. If it is incompatible with the fixed auxiliary slope, discard it. Otherwise combine those conditions on the factors of $t_0u$ coprime to $Q$, and split the denominator into its unit classes on that modulus, thereby fixing a numerator progression. The number of resulting rectangles, including all panels and terms, is $\exp(O(z^4))$. In each use (2) and (3). Indeed the bound from (2), divided by $Z$, is at most $\exp(O(z^2))(\sqrt Q/A+1/\sqrt A)$, while (3) is exponentially small in $H$ after this normalization since every prime of $Q$ is in the main band. Terms touching $Q$ can instead be deleted already in step 1, since for large $N$ every prime of $Q$ exceeds $\exp(C_2z^2)$. The total loss from (2) and (3) stays $\exp(-\Omega(H))$, since $c>b$.

For rough upper bounds with no restriction on the size of an auxiliary modulus $t$ coprime to $Q$, the lattice argument directly gives

$$
Q\,\Pr(a/b=r\bmod Q,\ a/b=s\bmod t)\ll e^{O(z^2)}(1/t+Q/A^2)
$$

whenever the denominators are units at $Qt$. This estimate also applies to extra main-band row prescriptions and to the $p^2$ determinant exceptions, using the combined congruence modulus. It supplies an upper bound even at the exceptional slopes where relative equality fails.

Equation (4) establishes the averaged mark estimate and the rough alternative used in a possible trace transfer. A high-trace proof must additionally place the average inside the row-label sum with its actual normalizers, account for dependencies where row residues coincide, and check all the product expansions. The estimate uses every prime in the denominator interval and gives no conclusion for a fixed sparse denominator menu.
