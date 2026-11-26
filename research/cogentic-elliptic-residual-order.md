# An odd residual order on a moving elliptic curve

A public moving curve can split an unknown odd modulus when it separates two prime divisors and the marked point has residual odd order at most $K^2$ at any prime divisor. The interval search costs $\widetilde O(K\,\operatorname{poly}(\log N))$ beyond the public odd scalar and curve construction. A collision that gives a global annihilator can still yield a split. Recover its odd multiplier and compare the last nonzero points in the doubling chains. [Moving separation menu](cogentic-moving-elliptic-separation.md) · [Local saturation](cogentic-elliptic-local-halves.md#finding-a-relation-after-an-odd-public-power)

## The residual order and a checked group law

Let $N>1$ be odd. On a public curve $E:y^2=(x-e_1)(x-e_2)(x-e_3)$, check the gcd of each root difference with $N$. A proper gcd splits $N$. Discard a curve with a globally zero root difference. On every remaining curve the three roots are distinct at every prime dividing $N$. Let $R$ be the marked point and let $U$ be a public positive odd scalar. Write $h_p$ for the odd part of $\operatorname{ord}_{E(\mathbb F_p)}(R)$ at a prime $p\mid N$. For $h=\lceil\log_2(4N)\rceil$ put
\[
             Z=[2^hU]R,\qquad r_p=\operatorname{ord}_{E(\mathbb F_p)}(Z)
                   =h_p/\gcd(h_p,U).
\]
Hasse's bound makes $2^h$ divisible by the two-part of every local group order. If a supplied scalar has an even factor, use its odd part for $U$ and the public $2^h$ for removing the two-part.

Maintain modular points that are affine or globally the identity. For two affine points whose abscissas differ modulo $N$, check the gcd of their difference before using a secant. At equal abscissas the ordinate differences satisfy $(y-v)(y+v)=0\bmod N$. If neither factor vanishes globally, either one gives a proper gcd. Otherwise the opposite points sum to the identity, or the equal points use the tangent. The tangent denominator $2y$ is checked in the same way. These formulas compute the correct reductions and the correct point over the residue ring. In particular an intermediate identity at some primes and a finite point at another cannot pass a checked computation without exposing a proper divisor. The argument also works for repeated prime factors. A nonzero denominator with a proper gcd is already enough to split.

## A bounded search that recovers the scalar

Suppose a positive exponent is to be found in a public interval $[A,A+W-1]$, with $A\geq1$. Let $s=\lceil\sqrt W\rceil$ and $M=2s+1$. Partition the interval into full blocks centered at $c_i=A+s+iM$, followed by fewer than $M$ exponents. Generate the baby points $[j]Z$ for $1\leq j\leq s$, and the giant points $[c_i]Z$ for the full blocks. After computing the first giant and $[M]Z$ by binary multiplication, consecutive giants cost one addition each. Check the centers for the identity. Process the terminal exponents by one binary multiplication followed by consecutive additions. An identity baby already gives a global annihilator if any positive annihilator is acceptable. To keep the search inside the interval, omit identity babies from the affine collision test. A match with an identity baby requires an identity giant, and its center is an allowed exponent.

For the affine babies form the monic product
\[
                       P(X)=\prod_{j:\,[j]Z\ne O}\bigl(X-x([j]Z)\bigr)
\]
and evaluate it at all affine giant abscissas by monic product and remainder trees. At a good prime, two affine points with the same abscissa are equal or opposite. Thus an identity at the local exponent $c_i\pm j$ appears in that row product. Both signs lie in the same block, and every exponent in the interval is covered by a center, a signed offset, or the tail. An identity at only some primes during list formation has already given a gcd.

Any row whose gcd with $N$ is proper gives a divisor. If a row gcd is $N$, choose that row and scan its babies once. Some abscissa difference has nonunit gcd. A proper gcd splits; if the gcd is $N$, check the two ordinates. Mixed signs again give a proper gcd. Global equality of the ordinates gives the verified relation $[c_i-j]Z=O$. Global opposition gives $[c_i+j]Z=O$. Either scalar is positive and in the interval. Baby abscissas may repeat and there may be multiple globally equal pairs. One resulting nonzero global relation suffices, so neither removing duplicate projective points nor locating the first hit is necessary. A row product equal to zero modulo $N$ can therefore be resolved with one scan rather than repeated searches.

This costs $\widetilde O((\sqrt W+\log(2A+W))\operatorname{poly}(\log N))$ bit operations after forming $Z$. Forming $Z$ and restoring its odd multiple also charge the bit length or the chosen short product representation of $U$. Setting $A=1,\ W=\lfloor K^2\rfloor$ covers any residual $r_p\leq K^2$. The output is a proper divisor, a verified global nonzero annihilator, or a complete miss for the interval. If a local positive annihilator is in the interval, a complete miss is impossible. [Polynomial evaluation over the composite residue ring](cogentic-elliptic-batch-search.md#why-a-globally-zero-product-causes-no-quadratic-scan)

## Recovering the two-torsion labels from a global hit

Suppose $[n]Z=O$ has been verified, and let $d$ be the odd part of $n$. For every $p\mid N$, the odd order $r_p$ divides $d$. Hence $S=[dU]R$ has two-power order in every prime-field reduction. Compute $S$ by the checked group law, and double until the identity. Whenever the local orders become trivial at different times, a denominator or sign test exposes a divisor. If all the local orders are $2^a$ with $a>0$, the last affine point $T=[2^{a-1}]S$ is a two-torsion point at every prime. Compute the three gcds $\gcd(x(T)-e_i,N)$. If two of the prime reductions give different torsion roots, a gcd is proper.

Now suppose $p,q$ are any two prime divisors for which the stacked Kummer matrix on $(R,T_1,T_2)$ has rank three, with $T_1,T_2$ the two public basis torsion points. Without a split, a common local order $2^a$ at these primes gives a contradiction. If $a=0$, then $[dU]R=O$ at both, with odd marked coefficient. If $a>0$ and the last affine point has the same torsion label $T$ at both, then
\[
                          [2^{a-1}dU]R-T=O
\]
at both. The torsion labels of the nonzero $T$ have at least one nonzero bit in the basis. In either case the relation has nonzero parity, and Kummer maps at both primes kill it. Rank three rules that out. Thus any global annihilator from the interval search completes the split on a separating curve. This argument uses only the public roots and computed gcds in the modular algorithm. It applies with any number of distinct prime factors of $N$.

## Shifted exponents, prime tails and mixed words

Beginning the blocks at an arbitrary public $A$ incurs a scalar cost polynomial in $\log A$ and leaves the square-root dependence on the interval width. The guarantee is that $r_p$ divides a positive exponent in the interval. At least one multiple always occurs if the interval width is at least $r_p$. Even a residual much larger than $K^2$ works if it divides a scanned exponent in a public interval of width $O(K^2)$. For an arithmetic progression with public step $v$, use babies $[jv]Z$ and giants for the actual center exponents. Require that all tested exponents be positive. The same proof applies to public baby and giant scalar sets with both signs allowed and all signed differences and sums nonzero, with cost soft-linear in the two side lengths and the costs of constructing their points. The residual need only divide one signed sum or difference. Dropping a sign or including the trivial scalar zero can destroy the stated collision guarantee.

With the smooth scalar $U$ containing all powers of primes at most $K$ up to the Hasse bound, a nontrivial $r_p\le K^2$ is necessarily a single prime in $(K,K^2]$. The search works for a composite residual too when $U$ is more general. A surviving prime factor of the order in the searched interval is sufficient only if the other residual factors are also covered. For example, if the residual is $b\ell$ and the cofactor $b$ is a public candidate, searching $b$ times an interval containing $\ell$ works. A bound on an individual prime divisor alone supplies no annihilator.

For a fixed number of selected integer words $W_j=\sum_i c_{ji}R_i$, run the search separately on $Z_j=[2^hU]W_j$. Each word can have its promised local hit at a different prime. If no split appears, each hit supplies a verified global row $n_j(c_{j1},\ldots,c_{jm})$ on the generators $[2^hU]R_i$. One may also use affine collisions between selected lists of points of this form. A globally signed match supplies the corresponding sum or difference row, so a public offset word can participate in the relation. Such a match alone need not annihilate any single generator.

If the verified rows span the desired directions over the rationals, clear denominators to obtain scalar multiples of their integer exponent vectors in the row lattice. In particular, for full rank a nonsingular square row block of determinant $D$ contains all $D$ times the standard basis vectors in its row lattice, by the adjugate identity. The odd part of $|D|$ then kills the residual odd orders of all the marked generators at all primes. This follows by taking local orders after multiplication by $2^hU$. Replacing $U$ by $U$ times this odd part preserves every Kummer column, and the fixed-dimensional two-saturation test applies to those generators and any public torsion generators. For a single marked direction with full rational two-torsion, the simpler top-label proof suffices. The work is charged to each selected search and its row arithmetic. No rank supply follows from one arbitrary mixed collision.

## An exact shared-annihilator example

Use $N=76127$, the menu positions $(0,25,28,-25)$, and the marking at zero. The roots modulo $N$ are $(56865,33238,19262)$ and $R=(0,67206)$. The two primes are $269,283$. At both primes $R$ has order $132$, and the stacked Kummer matrix has rank three. With $U=3$ and $h=19$ one obtains $Z=(67725,23665)$, of order $11$ at both primes. In the interval $[1,49]$ the first center is $8$ and
\[
                    [3]Z=(38843,25141),\qquad [8]Z=(38843,50986).
\]
The abscissa gcd is $N$. The ordinates are globally opposite and give $n=8+3=11$. Restoring $[33]R$ and doubling gives the top point $(45298,0)$. Its three root gcds are $269,1,283$. This is a split after a global hit despite identical residual orders and identical two-order heights at the two primes.

Under the moving-menu theorem, Dirichlet RH supplies separating entries without inspecting the factors. The additional promise here is that some separating entry has a local residual covered by the public search at some prime divisor. If this prime lies outside the separating pair, its hit either splits directly or gives a global annihilator that still activates the separating pair. Testing the polynomial-sized menu with $K=L_N[1/3,O(1)]$, a smooth scalar through $K$, and intervals or candidate sets of the stated costs stays at the one-third scale. Separation alone supplies no bound on these odd residuals.
