# Wide cofactor intervals and the two-mark determinant lattice

A cofactor interval of length $\exp((40000+o(1))V)$ gives mark-value width $\exp((50001+o(1))V)$ on the fixed Cogentic schedule. With a short intercept and fixed slope the width is almost entirely in one direction. Axis-parallel rectangle decomposition incurs an exponential loss. Even on a full Cartesian rectangle, the available uniform additive and multiplicative Fourier bounds on the determinant quotient permit a large two-mark correlation. [Cofactor family](cogentic-cofactor-dispersion.md) · [Oscillatory Mellin estimate](cogentic-band-additive-spectrum.md)

## Admissible cofactor range and physical widths

Take $m=\lceil N^{1/d}\rceil$, $g=P_0\ell$, and the base-$m$ digit polynomial $R$ for $N$. With the slope fixed, write the signed marked values as a constant plus $g(R_i k-n_i x)$, where $n_i=m-a_i$ and $R_i=R(a_i)$. Changing signs at either mark preserves all width and index statements. Write $K=\exp((\kappa+o(1))V)$ and $T=\exp((\tau+o(1))V)$ for the cofactor and intercept lengths. In the fixed schedule $g=\exp(O(H))$, $\log m\sim V$, $d\log A\sim10000V$, and the mark height has leading logarithm $100001V$. The digit bound gives $\sup_{|t|\le A}|R(t)|\le dm A^{d-1}=\exp((10001+o(1))V)$. Any fixed $\kappa<90000$ keeps the addition exponentially below the original real-grid and center margins. It also keeps $gK=o(c_d)$, since $\log c_d\sim90001V$. The perturbations in the two Gaussian coordinates can keep their original support for the initial moment proof. [Fixed-schedule margins](cogentic-deterministic-two-thirds.md#the-grid-its-sieve-and-its-real-roots) · [Moment proof with shifted cofactors](cogentic-cofactor-dispersion.md#a-low-mean-initial-score-for-the-enlarged-family)

There is a matching leading lower bound on nonnegative marks $a\ge A/L^C$ with $C$ fixed. The highest digit satisfies $[X^{d-1}]R\ge m-d$ by $N>(m-1)^d\ge m^d-dm^{d-1}$. That term alone gives $\log R(a)=(10001+o(1))V$. For two distinct such marks, $a_1<a_2$, both $\gcd(R_i,n_i)=1$ by $R_i\equiv N\bmod n_i$ and grid eligibility. The positive determinant is
\[
 J=n_1R_2-n_2R_1=n_1(R_2-R_1)+(a_2-a_1)R_1
   =\exp((10002+o(1))V).
\]
The highest digit bounds $R_2-R_1$ below by $(m-d)(a_2-a_1)a_2^{d-2}$. All bounds are uniform for these marks, including $a_2-a_1=1$.

If the intercept is fixed and the slope varies, replace $n_i$ by $a_i n_i$. The determinant still has leading exponent $10002$. To see the lower bound, use $R(a)/a$ in the displayed positive-difference identity and multiply by $a_1a_2$. The highest digit contributes at least $(m-d)(a_2-a_1)a_2^{d-3}$ to the difference of $R(a)/a$. The only decreasing term, from the constant digit, costs at most $m(a_2-a_1)/(a_1a_2)$. The former dominates uniformly on the same mark range. The row gcds now divide $a_i$, so dividing each physical coordinate by its row gcd gives primitive rows and changes the determinant and all lengths by at most $\exp(O(H))$ factors. The following leading-exponent bounds apply to this case as well.

For independent uniform boxes in $k$ and $x$, the covariance matrix is the sum of the two rank-one matrices on $g(R_1,R_2)$ and $-g(n_1,n_2)$ with multipliers $(K^2-1)/12$ and $(T^2-1)/12$. Its determinant is $g^4J^2(K^2-1)(T^2-1)/144$. When $\kappa+10001>\tau+1$, the two standard deviations have leading exponents $\kappa+10001$ and $\tau+1$. These are variance scales of the uniform coefficient box before imposing any score predicates. If the slope is allowed to vary over a second intercept-size box on the leading $V$ scale, its variance affects only the short scale, up to $\exp(o(V))$ factors, since every $a_i$ is at most $A=\exp(O(H))$.

## Bounds for direct pooling and rectangular decompositions

At one mark put $R=R_a$ and $n=n_a$. Remove $g$ and the origin. Fix an integer $z=Rk-nx$. In the bulk $0\le z\le R(K-1)-n(T-1)$ the possible $k$ lie in an interval of length $n(T-1)/R$ and one residue class modulo $n$. The count is $T/R+O(1)$. In the two remaining edge intervals it is at most that upper bound, and their combined length is $O(nT+R)$. Comparing to the uniform law on an interval of length $RK$ costs total variation $O(R/T+nT/(RK)+1/K)$ when $T\gg R$ and $nT\ll RK$. This gives the swapped one-mark count at leading conditions $\tau>10001$ and $\kappa+10001>50000.5$. Those conditions already give $\tau+\kappa>50000.5$ for a direct residual scan. [Swapped-axis count](cogentic-cofactor-point-construction.md#what-the-width-estimates-give-when-the-axes-are-exchanged)

For two marks, work in the two physical coordinates after removing $g$. In a Cartesian rectangle contained in the image parallelogram, hold the second coordinate fixed. The first coordinate varies by at most $JT/R_2$, since the inverse map expresses $x$ as an affine function with first-coordinate slope of absolute value $R_2/J$. At a fixed original $x$, the number of $k$ in any such rectangle is at most $1+JT/(R_1R_2)$. Thus any family of contained rectangles covering a positive fraction of the coefficient box requires at least
\[
 \Omega\!\left(\frac{K}{1+JT/(R_1R_2)}\right)
  =\exp\!\left((\kappa-\max(0,\tau+1-10001)+o(1))V\right)
\]
rectangles when the exponent is positive. The bound applies even before decomposing by residues. For instance, $\kappa=40000$ and $\tau=10002$ require exponent $39998$.

## An obstruction from count profiles on the quotient

The obstruction below concerns the information provided by uniform Fourier inequalities. It uses artificial integer counts on a full Cartesian rectangle and applies to the determinant-quotient frequencies. Additional arithmetic of the actual smooth products remains available.

The lattice after removing $g$ is the image of the rows $(R_i,-n_i)$. Each row is primitive and its projection onto the corresponding physical coordinate is surjective. It has index $J$. For a fixed first coordinate, the second coordinate is determined modulo $J$, since the primitive kernel direction of the first row changes the second coordinate by $\pm J$. Surjectivity of the second projection then makes the residue slope a unit. Hence in general a translated lattice corresponds to $r_2=ur_1+c\bmod J$ with $u$ a unit. Let $S$ consist of the residues on which both $r$ and $ur+c$ are units. If this set is nonempty, its density is $e^{-o(H)}$. Indeed each prime forbids at most two residues, a compatible prime two costs at most a factor two, and the logarithmic loss at the other primes is $O(\sum_{p\mid J}p^{-1})=O(\log(2+\omega(J)))$.

Use aligned physical intervals with exactly $M_i$ integer slots per class modulo $J$, with $JM_i=\exp((w+o(1))V)$ and $w=50001$. Let $p=\exp(-C_0 H)$ for fixed $C_0>0$. In each interval set the baseline count on every unit class to $b_i=\lfloor pM_i\rfloor$ and put zero off the units. Pair all but at most one of the residues in $S$, and on each pair choose perturbation signs $(+1,-1)$ with independent random orientations. Use the same signs at the paired second-mark residues under $r\mapsto ur+c$. Leave all unpaired classes unchanged. Add the signed increment $h_i=\lfloor pM_i/4\rfloor$ to the corresponding count. Both perturbed profiles have the same principal totals as the baselines and have integer counts in $[0,M_i]$.

There exists a choice with each nonprincipal multiplicative and each additive perturbation sum bounded by $O(h_i\sqrt{J\log(2J)})$ at both marks. For any such character or additive phase, each independent pair contributes a mean-zero random complex number of absolute value at most $2h_i$. Apply Hoeffding's inequality separately to real and imaginary parts and take a union bound over at most $4J$ phases. The multiplicative baselines vanish on all nonprincipal characters. The total perturbation bound in count units has leading exponent $w-10002/2=45000$, below the available square-root character bound at exponent $50000.5$.

For additive frequencies of reduced denominator $d>Q_i$ with $Q_i=JM_i/\sqrt X=\exp((0.5+o(1))V)$, the Ramanujan sum bound puts the baseline normalized by $JM_i$ below $p\,d(J)/d$, where $d(J)$ is the divisor count. The normalized perturbation is at most $O(p\sqrt{\log(2J)/J})$. Both fit an additive bound with leading exponent $-(w-50000.5)/2=-0.25$. The oscillatory Mellin proof extends its pointwise bound to these quotient frequencies. In its notation $|\beta|W\ge W/(JQ)=\exp((50000.5-10002+o(1))V)$, so the low contour term in count units stays exponentially small since $w<2(50000.5-10002)$. The remaining contour estimates keep their original exponents. [Additive band-product estimate](cogentic-band-additive-spectrum.md#additive-sums-in-a-physical-interval)

The lattice average of the two normalized counts is $J^{-1}\sum_{r\bmod J}(C_1(r)/M_1)(C_2(ur+c)/M_2)$. Its perturbation from the baseline is exactly
\[
        \frac{h_1h_2}{M_1M_2}\frac{2\lfloor |S|/2\rfloor}{J}.
\]
The linear terms cancel by the sign balance. The density bound on $S$ gives a difference of $\exp((-2C_0+o(1))H)$. Thus exact principal totals, all the individual multiplicative bounds and every high-denominator additive bound on this quotient can coexist with a two-mark error at the scale of the squared density. The construction does not realize these profiles by band products. A determinant-lattice estimator at finer precision must use joint information beyond those bounds.
