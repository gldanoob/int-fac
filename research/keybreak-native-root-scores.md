# Root optimization in the ordinary single-input field sampler

Selecting among at most $\exp(CH)$ ordinary native fields cannot shift the terminal norm by a leading term using the truncated Murphy root score. With probability tending to one its absolute value is $O(H)$ for every continuing draw; the terminal log norm is of order $DH$. On the rough-input branch the score is in fact $O(D\log\log n)$, with $n$ the input bit length. A deliberately planted sampler can produce a known divisor with mean log size $d\log d+O(d)$, which ordinary field selection cannot replicate through this root score. [Planted roots and exact local optimum](keybreak-planted-local-roots.md) A stronger bound applies to the product of the *local* moments used in a smooth-part Rankin calculation. On the current $2.154631$ schedule that product is $\exp(o(H))$, uniformly over the same field choices. This calculation does not transfer independent local probabilities to actual pairs in a short sieve box.

Use $n$ for the bit length of the single input, $D=(\log N/\log\log N)^{1/3}$, $H=D\log\log N$, $d\sim\delta D$, and $B=\exp((b+o(1))H)$, with positive fixed parameters. For a primitive integral binary form $F$, let $\nu_p(F)$ be the mean $p$-valuation of $F(a,b')$ on primitive pairs in $\mathbb Z_p^2$. Its truncated Murphy score is
$$
 \alpha(F,B)=\sum_{p\le B}\left(\frac1{p-1}-\nu_p(F)\right)\log p .
$$
Negative values favor the form in the usual size-adjustment model. Here we bound this statistic even when the field is chosen after examining the whole pool. [Murphy’s thesis](https://maths-people.anu.edu.au/brent/pd/Murphy-thesis.pdf) · [Barbulescu and Lachand on the interpretation of the score](https://arxiv.org/abs/1403.0184)

## Local valuation bounds

Factor $F$ over a splitting extension of $\mathbb Q_p$ into $d$ linear forms, normalizing each coefficient pair to have maximum absolute value one. The remaining scalar is a unit by multiplicativity of the polynomial Gauss norm. Each root whose reduction belongs to $\mathbb P^1(\mathbb F_p)$ has one contributing projective residue class, of mass $1/(p+1)$. In its unit chart, further agreement to valuation strictly greater than an integer $j\ge0$ specifies at most one class modulo $p^{j+1}$ in the slope. This holds for roots in extension fields, with fractional valuations, because two rational slopes close to the same root are close to each other. It also applies in the chart at infinity. Therefore the valuation of each linear factor is stochastically bounded by the variable with tail $p^{-j}/(p+1)$ above each interval threshold $j<t\le j+1$, i.e. with $\Pr(V\ge t)=p^{-j}/(p+1)$ there. Roots without a rational reduction contribute zero. This gives
$$
 0\le\nu_p(F)\le\frac{dp}{p^2-1}.
$$
When the binary reduction is squarefree, each of its $r_p$ rational projective roots lifts uniquely, giving equality with $r_p$ in place of $d$.

For a tilt $\theta>0$ with $d\theta<1$, write $M_p=\mathbb E[p^{\theta v_p(F)}]$ and $g_p(t)=(p^{\theta t}-1)/(1-p^{\theta t-1})$. If a direction contains $m_x$ roots counted with multiplicity, conditional Hölder and the same tail bound give
$$
 M_p-1\le\frac1{p+1}\sum_{x:m_x>0}g_p(m_x).
$$
Indeed, conditional on this direction the valuation of each of its factors is dominated by a geometric variable on the positive integers with tail $p^{-j}$ above $j$. Other factors contribute zero. Summing in the separate residue directions gives the formula. The right side is maximized by one group of $d$ roots, since $g_p$ is convex, increasing and vanishes at zero. This includes inseparable reductions and repeated linear factors.

## Simultaneous root counts

Condition on an admissible $r,Q$ and use the affine coefficient law of the native sampler. For every $p\nmid 2NQ$ the prescribed projective point is a nonroot. Each of the $p$ other projective points is a root with probability exactly $1/p$ under the uniform residue model, including the point at infinity. Thus $\mathbb E r_p=1$ and $0\le r_p\le d$. In particular this count uses the affine space of unnormalized, degree-at-most-$d$ polynomials. [Native affine law and CRT](keybreak-native-splitting-fields.md)

Fix a large constant $A$ and partition $[n^A,B]$ into dyads, extending the last one to a full dyad. For each dyad with lower endpoint $P$, delete primes dividing $2NQ$ and let $m\asymp P/\log P$ be the number left. Take $t=\lfloor cD\rfloor$ with $c>0$ small enough that $(2B)^{2t}\le\sigma^{1/2}$, where $\sigma$ is the Gaussian width. For *any* tuple of $2t$ of those primes, its joint distinct-prime residue law is within $\eta=\exp(-\Omega(DH))$ of independent uniform residues. This follows from the Gaussian residue estimate $O(d(2B)^{2t}/\sigma)$ plus the finite-sampler error. Under the independent law a term in the centered moment expansion for $\sum_p(r_p-1)$ vanishes if any prime appears exactly once. Otherwise its $2t$ positions use at most $t$ prime indices. There are at most $m^t t^{2t}$ such tuples, by choosing a list of $t$ possibly repeated indices and assigning one list position to each tuple position. The error in the normalized moment from the actual residue law is $O(d^{2t}\eta)$. Consequently
$$
 \Pr\left(\left|m^{-1}\sum_p r_p-1\right|>1\right)
 \le (td)^{2t}/m^t+O(d^{2t}\eta).
$$
For any fixed field budget $\exp(CH)$ we can choose $A$ large enough that the first term is at most $\exp(-(C+2)H)$ for every dyad. The second is $\exp(-\Omega(DH))$, since $t\log d=O(H)$. A union over all fields and $O(H)$ dyads gives total failure $o(1)$. No independence between full-field statistics is needed. Each fresh draw must have the stated conditional coefficient law before selection.

For $p\le n^A$ the universal valuation bound contributes $O(d\log n)=O(H)$ to $\sum\nu_p\log p$. For $p>n^A$, good primes with squarefree reduction contribute $O(1)$ per dyad by the root count. The native discriminant has $O(n^{O(1)})$ bits and the actual coefficient cap gives $\log|\operatorname{disc}F|=O(dDH)$ by the resultant determinant. All primes dividing $2NQ\operatorname{disc}F$ above $n^A$ together contribute $o(1)$ by the universal bound, increasing $A$ if necessary. The integer baseline is $O(\log B)=O(H)$. This proves the uniform score bound. [Lean limited-independence moment and tail](../formal/cogentic/Cogentic/RandomizedLimitedIndependence.lean) · [Finite projective valuations](../experiments/keybreak-native-root-scores.py)

## The sharper ordinary-field score on rough inputs

Work after the rough-input prepass, so all odd primes in a fixed polynomial range in $n$ are coprime to $NQ$ eventually. In the actual native sampler the prime two is fixed by the irreducibility condition and can be included in the elementary small-prime bound. Use the total multiplicity $m_p^*$ of rational projective roots of the degree-$d$ binary reduction. Their valuations contribute at most $m_p^*p/(p^2-1)$, even at ramified primes. Put $K=(\log n)^2$ and $P_0=c_0DH$ with $c_0$ small enough that the product of all primes up to $P_0$ is below $\sigma^{1/2}$. The primes $p\le K$ contribute $O(d\log K)=O(D\log\log n)$ in absolute value.

For the remaining primes through $P_0$, the whole CRT residue law is exponentially close to the independent affine law. At each prime, prescribing multiplicities $j_x$ on nonanchor projective sites imposes exactly $\sum_x j_x$ independent linear conditions when this sum is at most $d$. Indeed the corresponding product of homogeneous linear forms must divide the binary polynomial, and its value at the anchor is a unit. If the total exceeds $d$ the event is empty. Expand $\exp(zm_p^*)$ as a product of tail indicator expansions at the $p$ nonanchor sites. For $0\le z\le1$ and $p>K$, the preceding bound gives
$$
 \mathbb E e^{z m_p^*}\le\left(1+\frac{e^z-1}{p-e^z}\right)^p\le e^{O(z)} .
$$
Use $z=(\log n)(\log p)/p$, which is at most one eventually. Under the independent law the log moment for the sum of these weighted multiplicities is $O(\log n\,\log P_0)$. Chernoff's inequality at a threshold $C' D$ on $\sum m_p^*(\log p)/p$ thus costs $\exp(-(C+2)H)$ for sufficiently large $C'$, since $D\log n\sim H$ and $\log P_0=o(D)$. Transfer this *event* through total variation. Its bound holds simultaneously over the field pool. The corresponding integer baseline is $O(\log n)$.

In a dyad between $P_0$ and $n^A$, the number $m$ of primes is at least a constant times $D^2$. Put $t=\lceil L D\rceil$ and $T=\sqrt d$, with $L$ a large fixed constant. The sum of the $t$-fold products of $m_p^*$ over ordered distinct choices is at least $(Tm-td)^t$ on $\sum m_p^*\ge Tm$. After each choice the remaining sum of multiplicities falls by at most $d$. Under the affine model the mean multiplicity is at most $p/(p-1)\le2$ by the same prescribed-root count. For each distinct tuple its moduli product has logarithm $O(LD\log n)=O(H)$, and the Gaussian residue error times $d^t$ is negligible. The expected sum of products is therefore at most $m^t(2^t+o(1))$. Since $td/m=O(L)$, the probability of a dyad average above $T$ is $\exp(-t(\log d)/2+O(t))$. Choose $L$ large enough for all draws and all these dyads. Their contribution is $O(\sqrt d\log n)=o(D)$. Endpoints can be covered by extending the two outer dyads by a factor two.

Finally, in each dyad above $n^A$ apply the centered-moment calculation to $(r_p-1)p\log(p)/(p^2-1)$, dividing weights by their common dyadic maximum. Each centered factor stays bounded by $d$. Use a relative threshold $1/\log n$ in place of one. This multiplies the first moment bound of order $2t$ by $(\log n)^{2t}$ and this factor is absorbed in the choice of $A$. The second residue-law error is still $\exp(-\Omega(DH))$. One can use the full dyad's prime count in the normalization even for the last partial dyad, by assigning zero weight beyond $B$. There are $O(H)$ dyads and each weighted deviation is $O(1/\log n)$. Discarding the finitely many discriminant or excluded primes has the same negligible cost as above. The deterministic difference between the integer baseline and the one-root mean is $\sum (\log p)/(p^2-1)=O(1)$. This proves the sharper $O(D\log\log n)$ bound for the absolute score of every continuing field in the pool.

## A positive-tilt bound

Take $\theta$ with $\theta\log B=\log D+\log\log D+O(1)$, or with $\theta\log B=\log D$. Assume $d\theta\le\lambda<1/2$ eventually for some fixed $\lambda$. Since $d\theta\to\delta/(3b)$ this strict margin holds when $b/\delta>2/3$, including the explicit $2.154631$ schedule and the conditional $1.922$ parameter set. We show
$$
 \sum_{p\le B}\log M_p=o(H).
$$
For $p\le d$ the single-cluster bound is $M_p-1\ll p^{\lambda-1}$, giving $O(d^\lambda)$ after summation. For $p>d$, choose a projective chart over $\mathbb Z_p$ whose point at infinity is a nonroot modulo $p$; one exists because $p>d$. The transformed leading coefficient is a unit and the discriminant changes by a unit. The degree of the common divisor of the reduced polynomial and its derivative is at least $\sum_x(m_x-1)$ over rational root directions. It is the corank of the Sylvester matrix modulo $p$, hence at most $v_p(\operatorname{disc}F)$. The latter step follows by Smith normal form over $\mathbb Z_p$. By the chord bound for the convex $g_p$,
$$
 M_p-1\le \frac{r_pg_p(1)}{p+1}+
 O\left(\min\left(1,\frac{v_p(\operatorname{disc}F)}{d-1}\right)p^{\lambda-1}\right).
$$
Indeed the total multiplicity excess is at most $d-1$, and the contribution of each excess is at most $g_p(d)/(d-1)$ before division by $p+1$. Set $Y=2+\log|\operatorname{disc}F|/(d-1)=O(DH)$. Sum the excess bound trivially up to $Y$. Above $Y$ use $p^{\lambda-1}\le Y^{\lambda-1}$ and the bound $O(Y)$ on the sum of the indicated weights. This costs $O(Y^\lambda)=o(H)$.

It remains to sum the first term. Through $n^A$ it is $O(d\theta\log n)=o(H)$ since $r_p\le d$ and $p^\theta-1=O(\theta\log p)$. Beyond $n^A$ the dyadic bound on $r_p$ gives $O(\log\log B+B^\theta/(\theta\log B))=O(D+\log\log B)=o(H)$ by summing over dyads. The $O(n)$ bits of $2NQ$ give negligible extra contribution from excluded primes above $n^A$. Finally $\log M_p\le M_p-1$, completing the proof.

This rules out a leading gain *solely from these local scores or their product* inside the ordinary sampler. The size-adjustment interpretation of $\alpha$, and particularly the multiplication of local moments, require additional information to describe joint smoothness in the actual terminal lattice.
