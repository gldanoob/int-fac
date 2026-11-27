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
