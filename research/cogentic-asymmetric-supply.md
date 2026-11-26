# Unequal norm sizes and smoothness cutoffs on the full projective grid

Within the two-field construction that uses jointly smooth marks, equal norm exponents and a common smoothness cutoff attain the infimum of the existing cost ledger. The conclusion allows the two fields to have different degrees, leading coefficients, and cutoff exponents. It uses the original common-root Gaussian construction, the full projective grid, and the rank criterion that retains all but a vanishing weighted mass of ordinary rows. [Averaged trace and rank criterion](cogentic-averaged-projective-trace.md#repetitions-diagonal-and-the-cost-implication) · [Fast extraction ledger](cogentic-fast-full-grid-cost.md)

## The common root and the two norm heights

Write $L=\log N$, $z=\log L$, $D=(L/z)^{1/3}$, $H=Dz$, and $V=DH$, so $L=DV$. Fix positive schedule coefficients with $\log A\sim cH$, $d_i\sim x_iD$, and $\log m\sim\mu V$. In field $i$, the perturbation is an isotropic coefficient Gaussian of width $W_i$ in the degree-at-most-$(d_i-1)$ kernel of evaluation at $m$ modulo $N$. The base-$m$ digit polynomial of $N$ has degree $(1/\mu+o(1))D$. The existing projected Gaussian proof fits it into the kernel after removing a fixed number of marked linear factors. This requires $x_i\mu\ge1$ at leading order. Its choice $W_i=m\exp(O(H))$ and leading coefficient at least $W_i$ give a nominal norm exponent $S_i\ge \mu+cx_i$. Indeed an absolute homogeneous evaluation includes the denominator raised to $d_i$, and the separated real-root windows contribute $o(V)$ to its logarithm. It follows that

$$
S_i\ \ge\ \mu+\frac c\mu\ \ge\ 2\sqrt c .
$$

Unequal leading coefficients coprime to $N$ preserve the evaluation maps into $\mathbb Z/N\mathbb Z$. On both sides each marked element still maps to $a-b_vm$, and the single all-ones row cancels the constant pole offsets separately in each field. The shared root neither ties the random coefficients together nor changes the markwise product of probabilities. [Variable-multiple lattice and width](cogentic-variable-multiple-lattice.md#the-two-polynomial-fields) · [Fixed-order degree slack](cogentic-narrow-band-moments.md#any-fixed-number-of-marks) · [Homogeneous extraction](cogentic-homogeneous-marks.md#rank-the-field-map-and-time)

The width condition also has a volume obstruction for any full-dimensional isotropic Gaussian that uses a relative Poisson normalizer. The kernel in field $i$ has rank $d_i$ and determinant $N$, because evaluation is surjective on constants. Its centered normalizer is at least one from the zero vector, so a relative estimate of $(1+o(1))W_i^{d_i}/N$ requires $\log W_i\ge (1/x_i-o(1))V$. When the width is bounded by the leading coefficient as above, this gives the same norm bound through $S_i\ge 1/x_i+cx_i$, even without the digit-basis width estimate.

## Smooth columns and row dimension

Take field-specific cutoffs $\log B_i\sim b_i H$ and main bands $B_i^{1-\delta_i}<p\le B_i$, with $\delta_i=(\log u_i)^{-1/2}$ and $u_i\sim (S_i/b_i)D$. Use the usual single protected target prime in the first field. Its forced factor has logarithm $O(z^3)=o(H)$ and leaves the smoothness exponent unchanged. For a fixed primitive mark where $a-b_vm$ is a unit modulo $N$, the one-field saddle gives probability $\exp((-S_i/(3b_i)+o(1))H)$ of squarefree smoothness, uniformly in the mark. Field draws are independent conditional on the common inputs and target. Hence the joint smoothness exponent and the upper bound on the expected clean-column count are

$$
\rho=\frac{S_1}{3b_1}+\frac{S_2}{3b_2},\qquad
\mathbf E M\le \exp((2c-\rho+o(1))H).
$$

This factorization is at a fixed mark. It places no independence requirement on different marks. Coprimality checks on the fixed grid either split $N$ or admit every original numerator. [Uniform one-point estimate](cogentic-variable-multiple-lattice.md#the-two-polynomial-fields) · [Narrow-band saddle](cogentic-narrow-band-moments.md) · [Small protected target](cogentic-projective-trace.md)

In field $i$, the top dyadic interval $(B_i/2,B_i]$ lies in the main band. For each prime there, the probability of a prescribed root is $p^{-1}(1+O(e^{-L^3}))$. Two distinct residues at the same prime give independent linear conditions, and conditions at distinct primes combine by CRT, with the same relative Gaussian error. Summing the indicators gives an expected count asymptotic to the number of primes in the interval and variance at most that expectation plus $e^{-L^3+O(H)}$. Therefore the ordinary row count there is $B_i^{1+o(1)}$ with probability $1-o(1)$. The expected number of multiple or shared roots is $o(1)$ by the narrow-band reciprocal-prime sum, using the intersection of the two bands for shared roots. Rows in different fields have distinct indices, including at a physical prime present in both bases. Their total dimension has exponent $b=\max(b_1,b_2)$. [Conditional root probabilities](cogentic-projective-trace.md#joint-smoothness-at-distinct-marks) · [Narrow-band cleanliness](cogentic-narrow-band-moments.md)

With probability $1-o(1)$ the top dyadic rows of field $i$ carry total saddle weight bounded below by a positive constant. Each row weight $p^{-\alpha_i}$ is comparable to $B_i^{-\alpha_i}$. The count is asymptotic to $B_i/(2\log B_i)$, and $B_i^{1-\alpha_i}\sim u_i\log u_i\sim S_i H/(3b_i)$. A deletion of $o(1)$ total weight therefore leaves $B_i^{1+o(1)}$ of these rows. The positive Gram criterion on the retained rows requires at least as many clean columns as retained rows. By Markov's inequality a schedule with $2c-\rho<b$ fails this criterion with probability $1-o(1)$. The existing symmetric trace uses the strict margin $2c-\rho>b$.

## Infimum of the cost ledger

Since $S_i\ge2\sqrt c$ and $b_i\le b$,

$$
\rho\ \ge\ \frac{2\sqrt c}{3}\left(\frac1{b_1}+\frac1{b_2}\right)
\ \ge\ \frac{4\sqrt c}{3b} .
$$

Put $u=b/c\in(0,1)$, the range of the existing averaged-residue ledger. The necessary supply inequality $2c-\rho\ge b$ gives $c^{3/2}\ge 4/[3u(2-u)]$. The grid and square pivot terms of the ledger are $2c$ and $\omega b$, even if rectangular column processing changes. The lower envelope of $c\max(2,\omega u)$ under this inequality decreases up to $u=2/\omega$ and increases thereafter for $2<\omega\le3$. On the first interval $u(2-u)$ increases, while on the second the cube of the envelope is proportional to $u/(2-u)^2$. At $u=2/\omega$ the symmetric schedules approach the boundary $\rho=2c-b$, where the column term $2c-\rho+(\omega-1)b$ approaches $\omega b=2c$. The infimum is therefore

$$
2\left[\frac{\omega^2}{3(\omega-1)}\right]^{2/3}.
$$

For a fixed cutoff ratio $\vartheta=\min(b_1,b_2)/b$, the same calculation multiplies the lower envelope by $((1+\vartheta^{-1})/2)^{2/3}$. Any fixed separation of the cutoff exponents thus raises this ledger bound. Equality in the leading norm and density inequalities requires $\mu=\sqrt c$, $x_1=x_2=1/\sqrt c$, and $b_1=b_2=b$. [Strict schedules attaining the infimum](cogentic-fast-full-grid-cost.md#exact-infimum-and-a-strict-rational-schedule)
