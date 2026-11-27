# Principal genus supply from paired half-shapes

The full one-coordinate staged supply in the principal genus survives even if the retained split-prime sets have large genus bias. Count two half-shapes with **identical** stage allocations, and multiply pairs whose genus labels agree. The retained prime sets may depend on the public environment and field. It suffices that each used dyad retain a fixed positive fraction of its primes or, more generally, a fraction $D^{-o(1)}$, where $D=(\log N/\log\log N)^{1/3}$ and $H=D\log\log N$. The argument targets the principal genus, including a target multiplier whose unit squareclass is trivial. [Existing staged genus supply and prefix bounds](keybreak-reduced-form-smooth-supply.md#field-good-prime-bands-and-staged-prefixes) · [KeyBreak H.20](https://crypto.sjtu.edu.cn/factoring.pdf#page=135)

## Identical rounded halves and the stage thresholds

Use a fixed finite stage mesh with positive fractions $f_i$ summing to one, upper dyadic exponents $e_i$ of order $DH$, and disjoint stage intervals with fixed positive leading gaps. The first permitted exponent is also a positive fixed multiple of $DH$. Let $n$ be the input bit length, and take $L=\lfloor(n-1)/2\rfloor-2$ as the full one-coordinate allocation. Choose integer $L_i=f_iL+O(1)$ with $\sum_iL_i=L$ by flooring the first stages and assigning the remainder to the last. For **both** halves take $\ell_i=\lfloor L_i/2\rfloor$. If there are $J$ stages then $2\sum_i\ell_i=L-O(J)$. The identical allocation, rather than using floor in one half and ceiling in the other, ensures both halves have the same attainable genus distribution.

For each half in stage $i$, put
$$
q_i=\lceil\ell_i/e_i\rceil,\qquad m_i=\operatorname{bitlength}(q_i),
\qquad k_i=q_i+\lceil q_i/m_i\rceil,
$$
$$
s_i=k_i e_i-\ell_i,\qquad
j_i=\lfloor 2(s_i+k_i)/k_i\rfloor,\qquad d_i=\lfloor k_i j_i/2\rfloor .
$$
Use the complete dyads of upper exponents $e_i,e_i-1,\ldots,e_i-j_i$. The sum of their offsets for a half-tuple is $d_i$. The same elementary checks as in H.20 give $s_i\le d_i\le s_i+k_i$. Also $k_i=\Theta(D)$, $m_i=\Theta(\log D)$ and $j_i/e_i=o(1)$. For the width guard, $s_i\ge (k_i-q_i)e_i$, $k_i-q_i\ge q_i/m_i$, and $k_i\le2q_i$ eventually. Thus $j_i+1>2s_i/k_i\ge e_i/m_i$. The dyads eventually lie strictly in their own stage intervals, since the original mesh has fixed leading gaps. These inequalities can be checked on an integer fixture with the halved allocation.

Each half stage product has exactly $k_i$ primes and lies in $[2^{\ell_i-2k_i},2^{\ell_i}]$. In fact the product of the selected dyadic upper endpoints is between $2^{\ell_i-k_i}$ and $2^{\ell_i}$, and choosing the primes costs at most another bit per position. The public test for the final product uses the exact stage threshold
$$
T_i=2^{\,2\ell_i-4k_i}.
$$
At each stage it measures the certified prime part in the original disjoint stage interval, as in the full recipe. Two coprime halves give $2k_i$ distinct factors in that interval and reach $T_i$. The whole product is at most $2^L<\sqrt N/2$, and at least $2^{L-O(J+\sum_i k_i)}$. Halving can change the integer factor counts and thresholds even though their leading parameters stay the same. If the original count is bounded by a strict leading cap, the cap still holds since $2k_i\sim L_i/e_i$.

## Counting and matching the two halves

Fix any retained sets of field-good split primes, all prime to $2N$, with at least a $\delta_i$ fraction of all primes in each dyad of stage $i$. Assume $\sum_i k_i\log(1/\delta_i)=o(H)$, which holds for fixed positive $\delta_i$ or $\delta_i=D^{-o(1)}$ uniformly over the finite mesh. The central coefficient of $(1+z+\cdots+z^{j_i})^{k_i}$ is at least $(j_i+1)^{k_i}/(k_i j_i+1)$ by symmetry and unimodality. For a fixed ordered dyad tuple, each position with upper endpoint $w$ has at least a constant times $\delta_i w/\log Y_i$ prime choices, even after deleting the previously used primes. Indeed $Y_i=2^{e_i}$ and every used dyad still has size exponential in $DH$, while the number of previous choices is $O(D)$. The product of upper endpoints is at least $2^{\ell_i-k_i}$. Divide the total tuple count by $k_i!$ to get distinct squarefree integers. The width guard yields the stage lower bound
$$
2^{\ell_i}\exp\bigl(-k_i\log k_i-o(H)\bigr)
$$
because the extra factors from $(j_i+1)/\log Y_i$, $\delta_i$, the dyadic endpoints and the central coefficient contribute only $o(H)$ to the logarithm. Different stages have disjoint primes, so their product retains this lower bound multiplicatively.

Let $\mathcal U$ be the resulting set of distinct half-shapes, put $X_h=2^{\sum_i\ell_i}$ and $k_h=\sum_i k_i$, and write $S$ for the original full one-coordinate log loss. Equivalently $S H=2\sum_i k_i\log k_i+o(H)$ at these leading cutoffs and allocations. Thus
$$
|\mathcal U|\ge X_h\exp\bigl(-(S/2+o(1))H\bigr).
$$
A split prime determines one genus label, since the two orientations are inverses and the genus group $G/G^2$ has exponent two. For each genus label $c$, let $n_c$ be the number of members of $\mathcal U$ with that label, and put $g=|G/G^2|$. By Cauchy–Schwarz, the number of ordered pairs with principal product genus is
$$
\sum_c n_c^2\ge |\mathcal U|^2/g .
$$
This requires neither population in every genus nor an estimate of any individual genus bias.

For $p$ in the half-shapes, let $\mathcal U_p=\{u\in\mathcal U:p\mid u\}$. Then $|\mathcal U_p|\le X_h/p$ and $\sum_p|\mathcal U_p|=k_h|\mathcal U|$. Thus at most $k_hX_h|\mathcal U|/Y_{\min}$ pairs share a prime, where $Y_{\min}$ is the least retained prime bound. Relative to $|\mathcal U|^2/g$, this is $\exp(-\Omega(DH))$, since $\log Y_{\min}=\Omega(DH)$ and on the rough branch $\log g=o(H)$. It is valid to delete all these pairs after matching the genus.

Each remaining product $A=uv$ has $2k_h$ distinct prime factors and occurs at most $2^{2k_h}=\exp(o(H))$ times, by assigning a subset of its primes to the first half. Therefore there are at least
$$
\frac{\sqrt N}{g}\exp\bigl(-(S+o(1))H\bigr)
$$
distinct acceptable coefficients $A$ in the principal genus. For discriminant $-8N$, center a square root of $-2N\bmod A$ to obtain $[A,2b,(b^2+2N)/A]$. It is strictly reduced and primitive as $A<\sqrt N/2$ and is prime to $2N$. Distinct $A$ give distinct classes. The same argument uses $-N$ for discriminant $-4N$. Division by the class denominator $h/g$ and the existing $h\le\sqrt N\exp(o(H))$ gives a matching lower probability $\exp(-(S+o(1))H)$ for the uniform principal-genus sampler. This is a counting proof for that sampler and does not require the algorithm to construct halves or test their genus labels. [Reduced forms, class normalization and upper count](keybreak-reduced-form-smooth-supply.md#normalization-and-upper-count)

## Prefix caps and the nonprincipal case

The original prefix upper count works with these exact $T_i$ because it only tests that certified, disjoint prime parts reach the stage thresholds. The Rankin loss at stage $i$ remains the old one to leading order. Indeed $\log T_i=(L_i-O(1+k_i))\log 2$, so its shift from the earlier logarithmic allocation is $O(k_i)$, whereas the Rankin parameter is $O(\log D/e_i)$. The resulting change is $o(H)$. All other claims about analytic good-parent sets and launched descent costs remain separate.

For a nontrivial target genus $c_0$, the equal-half count is $\sum_c n_c n_{c_0c}$ rather than a sum of squares. It can vanish, for example when both halves are supported on one genus. Thus this relaxation cannot replace quantitative mixing for an arbitrary prescribed unit target with nontrivial squareclass.

## Arranging splitting for arbitrary retained prime sets

A random small multiplier removes the requirement that the public good sets already contain split primes of a particular quadratic field. Suppose the high-degree field and its eligibility tests have been fixed. In every required dyad let \(E_j\) be any subset of odd primes prime to \(N\), of relative density \(D^{-o(1)}\) or larger. The sets may depend on that field. Assume the number of dyads is at most \((\log(2N))^h\) for fixed \(h\); the primes in them have logarithms \(\Theta(DH)\). The sets and any coins defining them must precede the independent choice of multiplier. The algorithm need only test whether a requested row succeeds; it need not list any \(E_j\).

Choose a prime \(s\) uniformly from \([Z,2Z]\), where \(Z=(\log(2N))^K\) and \(K>2(h+4)\) is fixed. Check \(s\nmid2N\); on the rough branch this is automatic for sufficiently large inputs. Uniform integer draws with verified primality have polynomial expected bit cost. On any complementary input a proper gcd may be returned. For each \(p\in E_j\), put \(X_p=(-2N/p)(s/p)\). For distinct \(p,q\), the dependence on \(s\) in \(X_p X_q\) is the nontrivial Dirichlet character \((s/p)(s/q)\). By Dirichlet GRH, prime counting and partial summation in \([Z,2Z]\), its normalized average has absolute value at most
\[
 O\!\left(Z^{-1/2}\log^2(pqZ)\log Z\right)
 =O\!\left(Z^{-1/2}\log^3(2N)\right).
\]
The last bound is uniform since the band primes are at most polynomial in \(N\). Thus the second moment of \(\sum_{p\in E_j}X_p/|E_j|\) is at most \(1/|E_j|+O(Z^{-1/2}\log^3(2N))\). Each set has \(\exp(\Omega(DH))\) primes. Markov's inequality for the square and a union bound give probability \(1-o(1)\) that the average exceeds \(-1/2\) in every set. Then at least a quarter of each \(E_j\) splits in \(\mathbb Q(\sqrt{-2sN})\). This bound holds for every fixed choice of the original sets. [Dirichlet GRH prime progression estimates](https://arxiv.org/abs/2301.13457)

Use the order of discriminant \(-8sN\) for private rows. Its class number is between \(\sqrt{sN}/\operatorname{polylog}(sN)\) and \(\sqrt{sN}\operatorname{polylog}(sN)\) by the direct reduced-form count. The normalization at an unchanged target of order \(\sqrt N\) loses at most a polylogarithmic factor since \(s\le2Z\). The ambiguous diagonal count gives square-subgroup index \(2^{\omega(sN)}\). In the paired calculation even this factor cancels against the class denominator. For a unitary divisor \(d\mid N\), writing \(N=de\), the invertible ramified ideal \((d,\sqrt{-2sN})\) gives the relative sign \((d-2se)/(d+2se)\bmod N\). The denominator is prime to the original odd modulus, so the projection onto all its relative signs remains surjective. The signs at the auxiliary prime are immaterial.

In the direct canonical sampler keep leading coefficients prime to **the original \(N\)**, including those divisible by the known ramified prime \(s\). At \(s\) the local square-root equation has one solution modulo \(s\) and none modulo \(s^2\), since \(v_s(2sN)=1\). This preserves the padding bound and exact weight on the retained classes. If the seed norm is \(t\) with middle coefficient \(2b\), its content \(g=(t,2b)\) may include \(s\). The same three generators of \(I^2/g\) are integral, because the only such odd prime divides both \(b\) and the radicand to at least its exponent in \(g\). Their normalized imaginary coefficients are coprime, so the integer squaring formula applies with \(q=t/g\). The factor omitted from the ideal class law is still only the mass with a leading coefficient sharing a prime with \(N\), bounded by \(\operatorname{polylog}(N)/p_{\min}(N)\). Removing all multiples of the small auxiliary prime at the seed stage would not give the required whole-epoch variation estimate. [Direct proposal](keybreak-direct-reduced-class-sampler.md) · [Root and twist arithmetic](keybreak-targeted-quadratic-class.md)

Consequently the conditional cost proof at width one half works with a positive or \(D^{-o(1)}\) good-parent density in every used dyad, even if those sets are arbitrarily biased across genus characters and across the splitting condition for any single fixed quadratic order. The field still must support verified full descents at the charged rates in its retained sets. The argument supplies no narrow-Gaussian estimate for those public descents.
