# Averaged row residues in the fixed-multiple deterministic selector

The fixed-multiple trace proof can use $c>b$ in place of $c>2b$ when it uses the full admissible prime-denominator interval. The existing conditional selector then gives a manuscript-level deterministic complete-factorization bound
\[
 \exp\!\left(\bigl((4/3)^{1/3}+o(1)\bigr)
        (\log N)^{2/3}(\log\log N)^{1/3}\right).
\]
The coefficient is $1.1006424163\ldots$. This transfer uses the fixed-multiple Gaussian projection, clean local moments and extractor under their existing hypotheses, including Dirichlet GRH. It changes the residue estimation in the trace expectation. The coefficient selection still uses the existing numerical contraction. [Fixed-multiple local trace estimate](cogentic-fixed-multiple-trace.md) · [Deterministic trace selector](cogentic-projective-trace-selection.md)

## A weighted residue estimate for the filtered grid

Use the notation of the fixed-multiple proof. Thus $L=\log N$, $z=\log L$, $D=(L/z)^{1/3}$, $H=Dz$, $V=DH$, $\log A\sim cH$, $\log B\sim bH$, $d\sim xD$, $v=xc$ and $S=v+1/x$. Write $K=k_1k_2$ for the fixed cofactors. Take the full prescribed prime-denominator interval of length $J_b\asymp Ae^{-30z^2}$, excluding primes dividing $K$. At denominator $\beta$ each original numerator interval has length $\asymp J$ for $J=Aw$. The grid after the preliminary gcds retains $\gcd(a-m\beta,K)=1$. All denominator primes exceed $B$ when $c>b$ and are units modulo $K$. The fixed-denominator sieve at modulus one leaves at least a fixed inverse polynomial fraction of each numerator interval, since $\log(2K)=L^{O(1)}$ and the Bonferroni errors are uniform there. This step does not involve any main-band row modulus. [Fixed-multiple grid and weighted Brun estimate](cogentic-fixed-multiple-trace.md)

For any modulus $u$ coprime to every available denominator, two distinct retained fractions in a single slope class modulo $u$ differ as real numbers by at least $u/A^2$. Their numerator determinant is nonzero and divisible by $u$. In each grid interval there are $O(1+A^2w/u)$ such fractions. The prime number theorem under RH gives $\asymp J_b/\log A$ available denominator primes, and the preceding sieve lower bound therefore gives the normalized upper bound
\[
 \pi_0(\operatorname{slope}\equiv s\bmod u)
       \ll e^{O(z^2)}\left(u^{-1}+(A^2w)^{-1}\right).                \tag{1}
\]
Use $\pi_0$ with equal grid-interval masses. Pruning the numerator sieve for this upper bound only increases its numerator. The factor $w^{-1}$ falls only on the additive term.

The corresponding unfiltered weighted mean-square estimate applies for every modulus $u\le B^2e^{O(z^4)}$ coprime to the denominator pool. For a fixed grid interval, let $Z$ be its raw number of marks and let $F(a,\beta)$ have supremum and numerator total variation at most $M$. For the unfiltered discrepancy
\[
 D_s=uZ^{-1}\!\!\sum_{\operatorname{slope}\equiv s(u)}F(a,\beta)
                   -Z^{-1}\sum F(a,\beta)
\]
one has
\[
 \left(u^{-1}\sum_{s\bmod u}|D_s|^2\right)^{1/2}
 \ll M L^{O(1)}
       \left(\frac{u}{P J}+\frac{\sqrt u}{J}+\frac{u}{J^2}\right)^{1/2},
 \qquad P\asymp J_b/\log A.                                        \tag{2}
\]
Here $P$ counts the available primes, still omitting those dividing $K$. For a proof, expand the square so that each mark pair has the kernel $u1_{u\mid(a\beta'-a'\beta)}-1$. For fixed denominators the numerator congruence lattice has determinant $u$. Its count on any numerator subrectangle differs from area divided by $u$ by $O(J/\lambda+1)$, where $\lambda$ is its shortest vector length. Count on lines parallel to a shortest vector, using their spacing $\gg\lambda$ and summation by parts on the slice lengths. Two-dimensional partial summation gives the weighted error $O(M^2u(J/\lambda+1))$.

For distinct denominators a numerator lattice vector of size at most $U\le\sqrt u$ yields a primitive pair $(s_1,s_2)$ of size at most $U/h$ satisfying $s_1\beta'-s_2\beta\equiv0\bmod u/h$ for some $h\mid u$. At primitive size $\asymp Z_0$, each direction gives $O(1+Z_0J_b/(u/h))$ possible exact multiples of $u/h$ and $O(1+J_b/Z_0)$ integer denominator pairs for each multiple. Since $J_b\gg\sqrt u$, sum these bounds over dyadic direction sizes and over $h$, using $\sum_{h\mid u}1/h\le1+\log u$. After division by $P(P-1)$ the proportion is $L^{O(1)}(U/J_b+U^2/u)$, so dyadic summation gives average $\lambda^{-1}\ll L^{O(1)}u^{-1/2}$. Equal denominators contribute only $P$ pairs and use $\lambda\ge1$. Divide by $Z^2\asymp(PJ)^2$ to get (2). This elementary argument allows the actual angular width $\log(1/w)\sim D\sqrt z$ and requires no regularity of $F$ in the denominator. All three ratios in (2) are $\exp(-\Omega(H))$ if $c>b$.

Take a main-band row product $Q=pp'\le B^2$ and fix a small-prime slope class $s\bmod t$ with $t\le e^{Cz^2}$. Reinsert the fixed cofactor sieve as follows. Omit its primes exceeding $y=e^{C_2z^2}$ in this estimate. Each omitted prime costs $O(1/p+1/J)$ at fixed denominator, which is negligible after summing over the polynomially many cofactor primes and choosing $C_2$ large. Truncate the rest by Bonferroni through $j\asymp z^2$ terms. The error is bounded by the mass of the $(j+1)$-fold intersections, at most
\[
 L^{O(1)}\frac{(\sum_{p\le y}p^{-1})^{j+1}}{(j+1)!}
       +\frac{\exp(O(z^4))}{J}.
\]
The ignored mass bounds apply to the $L^1$ error over the $Q$ row residues after the $Q$-weighting, since each mark lies in just one row residue. They also bound the change in the unweighted mean. For each retained sieve product $u_0$, the required congruence is the fixed slope $m\bmod u_0$. Combining with $s\bmod t$ either gives an empty set or one slope class modulo $t_0=\operatorname{lcm}(t,u_0)\le\exp(O(z^4))$, coprime to $Q$. Apply (2) at $Qt_0$. Restricting the mean square to one $t_0$-class loses at most a factor $t_0$. Center the $Q$-residue hit at the actual mean on that class, which is the average of the $Q$ hits. The resulting error remains exponentially small in $H$ even after summing the $\exp(O(z^4))$ retained terms. After normalization by the retained grid count this bounds the averaged absolute error by $M e^{-C'z^2}$ for any fixed $C'$, with the constants chosen in that order. An incompatible cofactor slope gives zero identically. [Original sieve truncation and small-class density](cogentic-fixed-multiple-trace.md)

## Inserting the residue average into the trace

Keep the fixed-multiple one-mark reference densities, including the actual coprime progression normalization and the eligible prime exclusions from $K$ and the mark modulus. Keep the squarefree row-deletion saddle ratios as well. In the clean local formula the one-mark densities cancel the reciprocal densities in the score weights. The surviving pointwise incidence identity is $f_j\Pi^\circ_j=Q_j1_{\rm hit}\overline U_j(v_{\rm mark})$ for the retained two endpoints. Its model depends on the endpoint primes, fields and nominal mark means. Lemma 9.2(2) gives the model entries without any dependence on the endpoint residues, with polynomial supremum and numerator total variation in the normalized entry scale. The fixed-multiple progression factors are already included in the local clean formula and do not change this identity. Use the model's mean under the actual filtered grid. [Cogentic Lemma 9.2(2), p. 45, and Proposition 10.1(1), pp. 52–53](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=45)

For each fixed small slope class, the filtered estimate above centers the weighted hit against the model mean on that class. The ordinary fixed-denominator weighted Brun estimate at the small modulus $t$ centers that class mean against the global model mean times the class density. It needs no two-prime modulus. The extra row hits and the unwanted protected-target hits are suppressed by (1), intersecting their slopes with the endpoint hit when needed. The main-band primes are $B^{1+o(1)}$ and $\log\ell\asymp z^3$, so these costs are negligible after any fixed $e^{O(z^2)}$ loss. Every edge also has a uniform upper bound of its original scale times $e^{O_k(z^2)}$ by (1).

Expand the small-prime singular series on the partition lattice including the fixed slope $m$, as in the fixed-multiple trace proof. For product $t$ below its cutoff, split the independent marked sums by slope classes. Fix the physical primes and fields of a cyclic row tuple with distinct physical primes at distinct labels. Use the averaged bound on one edge and the rough bounds on every other edge. In the universal sum over potential rows the prescribed-root probabilities weight the allowed residues uniformly up to the stated Poisson error. The exclusion of residue $m$ at an endpoint costs at most a constant in converting the all-residue average to the allowed-residue average. Reusing a row label in another edge merely reuses its residue, since the other edge factors have already been bounded uniformly. The row-tuple prime sums and the repeated-physical-prime saving are the original ones. The latter case uses only upper bounds. The count of small slope classes is $e^{O_k(z^2)}$ and is absorbed by the chosen accuracy. [Distinct-position and root-label accounting](cogentic-projective-trace.md#expansion-of-the-centered-trace)

For a tail product above $T=\exp(Cz^2)$, retain one required equality per prime, either between varied marks or with the fixed slope $m$. Some later-mark modulus exceeds $T^{1/k}$. Apply (1) at its joint modulus with the row hit and use rough bounds at all other marks. The total cost is bounded by $e^{O_k(z^2)}(T^{-1/k}+B^2/(A^2w))$ before the polynomial partition-coefficient sum. This gives the desired tolerance for large fixed $C$. The $p^2\mid\Delta$ exclusions use (1) with $\operatorname{lcm}(Q,p^2)$, and restoring true coincidences to the factored distinct main sum costs $B^2\|\pi_0\|_\infty$ up to the rough factors. Narrow-band diagonal and protected entries have support at most $BE^2=B^{1+o(1)}$, where $\log E\sim z^3$. For them the original fixed-denominator estimates still apply, as $Aw=B\exp(\Omega(H))$.

Put $\rho=2S/(3b)$ and $\eta=2c-b-\rho>0$. In the repeated-position graph argument use (1) for each single-prime tree constraint and the two-prime closing constraint. They have costs $B^{-1+o(1)}$ and $B^{-2+o(1)}$. The original duplicate price $n^{-1}\exp(o(H))$ with $n=\exp((2c-\rho)H)$ and the tree exception $2h\le k$ remain unchanged. Choose fixed even $k>2b/\eta$ with slack. The diagonal duplicate price is $B^{1+o(1)}/n$. These are the inputs to the original trace and peeling argument, along with its unchanged root-mass and real interval bounds. Condition on neither the cleanliness event nor any future rank success when summing the row moments. [Repeated positions and protected diagonal](cogentic-projective-trace.md#repeated-marked-positions) · [Fixed-multiple spectral transfer](cogentic-fixed-multiple-trace.md)

## Conditional selection and its coefficient

The averaged row estimate is used only to prove $o(1)$ initial expectation for the fixed-order nonnegative score. The conditional evaluator still resolves each elementary term at its actual affine congruences and marked lattices. With high coefficients fixed, the exact image index and the Poisson kernel bound depend on primitive marks, the number of terms and the width, independently of $c>2b$. The tensor contraction runs in $WA^j\exp(O_k(H))$ to estimate a prefix with remaining degree $j$, with exhaustive enumeration of its fixed-size last block. The reference coefficient preprocessing may still trial-divide the actual $|a-b_vm|$ for their totient factors. Its exponent $1/(2x)$ on the $V$ scale is below $v$ by the retained assumption $v>1/x$. Thus the complete selected-score scan has exponent $v+o(1)$ as in the existing algorithm. The averaged trace estimate is unnecessary on the partly fixed coefficient boxes. [Exact conditional tensor contraction](cogentic-projective-trace-selection.md#tensor-calculation-with-partially-fixed-coefficients) · [Reference weight computation](cogentic-projective-selection.md)

The strict conditions are $c>b$, $2c>b+\rho$ and $x>1/v$. They imply
\[
 v+1/x=S<\tfrac32 b(2c-b)<\tfrac32 c^2,\qquad
 v^2>\tfrac23(vx^2+x)>\tfrac4{3v}.
\]
Conversely, for any rational $v>(4/3)^{1/3}$ take $x$ just above $1/v$, $c=v/x$ and $b$ just below $c$. The constraints are strict since at their limiting $x,b$ the inequality $2v<\tfrac32 v^4$ holds. For example $v=1.100643$, $x=0.9085600$, $c=v/x$ and $b=1.211413$ satisfy the inequalities as exact rationals. Fixed-order and Gaussian-width constants can then be chosen as in the original proof. The standard interleaving over strict rational schedules gives the infimum coefficient for the existing deterministic algorithm. This is a bound on its two-thirds scale. [Original selection and interleaving](cogentic-projective-trace-selection.md#parameter-limit)

The displayed strict schedule was checked with rational arithmetic. The existing selection replay checks the numerical contraction on 36 restricted three-mark examples.
