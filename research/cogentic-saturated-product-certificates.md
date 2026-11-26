# Saturated product relations and sharp cofactor thresholds

Verified relations on products of small bases can replace certificates for individual primes. A relation lattice of codimension $k$ leaves unresolved blocks with at most $k+1$ distinct prime factors. Explicitly computable certificates for at most $k$ additional small negative-Jacobi products suffice for complete factorization. This is a rank condition on the certified relations and uses no prime-density hypothesis. The dyadic density method has a separate exact threshold on each recursive cofactor. [Pooled order comparison](cogentic-pooled-order-certificates.md)

## Use rational rank by saturating the verified relations

Let $G=(\mathbb Z/N\mathbb Z)^\times$ for odd $N>1$, and choose unit bases $a_1,\ldots,a_t$ whose classes generate $G/G^2$. Under Dirichlet RH these can be all coprime positive integers up to $Q=3\lceil\log_2N\rceil^2$. Bach's bound guarantees that these generate $G$. A nonunit encountered in the scan gives its gcd with $N$. Using only prime generators is also valid by factoring the small trial integers. [Bach's bound](https://doi.org/10.1090/S0025-5718-1990-1023756-8)

Write $a^c=\prod_j a_j^{c_j}$. The input consists of verified integer exponent vectors $r_i$ with $a^{r_i}=1\bmod N$. A certificate $(a^{c_i})^{E_i}=1$ supplies the vector $r_i=E_ic_i$. Form the lattice $L=\sum_i\mathbb Zr_i$ and its saturation
\[
 S=(\operatorname{span}_{\mathbb Q}L)\cap\mathbb Z^t.
\]
For a basis vector $c$ of $S$, clear denominators to find $E>0$ with $Ec\in L$. Then $(a^c)^E=1\bmod N$ is a certified order multiple for a new word, even when all original coefficient vectors were even. A Smith normal form computes the basis and multiples at the same time. If $R$ has columns $r_i$ and $URV$ is diagonal with nonzero entries $d_j$, the vectors $U^{-1}e_j$ are a basis of $S$ and the corresponding multiples are $|d_j|$. Polynomial-time integer normal-form algorithms give polynomial bit cost in the explicit input. Negative coefficients only require modular unit inversion. [Kannan and Bachem](https://doi.org/10.1137/0208040)

Suppose $L$ has rational codimension $k$. Since $S$ is primitive, its binary reduction $W$ has codimension $k$ as well. On each cofactor $D\mid N$ the quadratic quotient of its unit group is an $\mathbb F_2$-space of dimension $\omega(D)$. The map from $\mathbb F_2^t$ induced by the bases is onto, since reduction on units is onto. The image of $W$ has dimension at least $\omega(D)-k$. Apply the pooled 2-primary comparison to the saturated basis certificates. Failure means that the projected subgroup is cyclic and injects into every local prime-power unit group. Its quadratic image has dimension at most one, so a block left after repeating the split comparison has $\omega(D)\le k+1$. At $k=0$ the result is complete factorization after prime-power recognition. Equivalently, surjectivity modulo squares generates the entire finite abelian 2-primary group, since a quotient by a proper subgroup cannot have surjective squaring.

This dimension obstruction is sharp under abstract relation availability. In a block with $r$ distinct primes take the cyclic diagonal subgroup of maximum height $s=\min_{p\mid D}v_2(p-1)$. Its image in the quadratic quotient is one-dimensional. The preimage of this line in the formal binary exponent space has codimension $r-1$. Any vector in that preimage can be represented by a word whose 2-primary projection is in this diagonal subgroup, after adding even coordinates to an arbitrary lift. Indeed the image of the even coordinates in the 2-primary group is precisely its square subgroup, by surjectivity modulo squares. One can select a basis of these lifted words and take their true orders as certificates. Their span has a binary image of codimension $r-1$ and cannot split the block by pooled comparison. Its saturation does not force a better rank guarantee when the lifted list has just $t-r+1$ vectors and its binary image already has that dimension.

## Complete the rank with small negative-Jacobi products

Greedy binary elimination selects $k$ standard coordinate vectors whose classes extend $W$ to the whole space. Order multiples for their bases finish the rank computation. In a negative-only interface, assume $N$ is nonsquare. At least one generator $a_b$ is Jacobi-negative because the Jacobi character is nonprincipal on $G/G^2$. Use instead the binary basis consisting of
\[
 e_j\quad\text{if }\left(\frac{a_j}{N}\right)=-1,
 \qquad e_j+e_b\quad\text{if }\left(\frac{a_j}{N}\right)=1 .
\]
These vectors are all negative under the public character and form a basis because the elementary column additions from $e_b$ are invertible. Greedy elimination selects the required $k$ from this list. Every corresponding integer product is at most $Q^2$. A certificate on such a product adds the integer relation $Ec$, whose rational span includes $c$. Hence these certificates complete the saturation, whether $E$ is odd or even. All target representatives can be selected before requesting their orders. If $N$ is a perfect power, extract maximal roots first and apply the nonsquare construction to the resulting base. The completion uses an interface for products or arbitrary small unit bases. An interface that only accepts primes in a fixed large dyadic band does not promise these certificates.

## Exact dyadic thresholds on recursive blocks

Retain the original negative filter $\chi_N=(\cdot/N)$ on primes in the dyadic interval. For a divisor $D$ with at least two distinct prime divisors, put $u_p=v_2(p-1)$ and $s=\min_{p\mid D}u_p$. If the certificate pool has not split $D$, its projected group is contained in a diagonal cyclic subgroup of height $s$. For a nontrivial observed cyclic subgroup of height $h$, choose a $2^{s-h}$-th root of its generator in each local cyclic group. For a trivial observed subgroup choose any diagonal of height $s$. A generator of a maximal diagonal subgroup is a local quadratic nonresidue exactly where $u_p=s$. The pullback of this subgroup to the units of $N$ has index $2^{\sum_{p\mid D}u_p-s}$.

The largest possible no-split negative pool consequently has unit-group proportion
\[
 \begin{cases}
 2^{-1-\sum_{p\mid D}u_p+s},
   & \text{some }p\mid N,\ p\nmid D\text{ has odd }v_p(N),\\
 2^{-1-\sum_{p\mid D}u_p+s},
   & \sum_{p\mid D,\ u_p=s}v_p(N)\text{ is odd},\\
 0,&\text{otherwise}.
 \end{cases}
\]
Either first condition suffices, and the sum uses exponents in the original modulus $N$. Indeed the original Jacobi character restricted to the pullback is nontrivial precisely when a free outside component or the diagonal generator gives a negative value. In that case the negative set is a coset of an index-two subgroup of the pullback. Taking the entire coset attains the bound as an order-certificate obstruction, since all those bases have orders and pooled comparison cannot split $D$. Under the uniform dyadic Dirichlet-RH estimate the corresponding prime fraction differs by $o(1)$, uniformly in the pullback and coset. [Uniform estimate and pooling](cogentic-pooled-order-certificates.md#what-density-of-certified-primes-suffices)

In particular a pool covering more than $1/8+\delta$ of all interval primes leaves only prime powers and two-prime blocks with both primes $3\bmod4$. A squarefree $N=pqr$ with $p,q\equiv3\bmod4$ admits a negative no-split coset of proportion $1/4$ for the block $pq$, because the component $r$ allows the original negative filter. Thus the $1/4$ complete-factorization threshold is sharp for the pooled comparison even on squarefree inputs. Factoring an unresolved block by some other procedure is outside this obstruction.

For a first split put $w=v_2(N-1)$. A nonempty negative no-split coset requires $s=w$, because expanding the product defining $N$ modulo $2^{s+1}$ gives odd minimum-level exponent sum exactly when $v_2(N-1)=s$. The cap on bad prime density is therefore $2^{-1-(\omega(N)-1)w}+o(1)$. If $N$ is squarefree with an even number of prime divisors, the cap improves by an extra factor of two, because not all $u_p$ can equal $w$ with odd minimum multiplicity. These caps are attained, as finite-group proportions, by choosing all $u_p=w$ when the minimum parity permits, or by choosing one $u_p=w+1$ in the squarefree even case. For fixed $w$ the patterns occur in arbitrarily large prime products by the prime number theorem in fixed progressions. If $(2^w+1)^2>N$, then $s=w$ is impossible for a modulus with at least two distinct prime divisors, so any negative certificate gives a first split. The same argument with a freshly applied Jacobi filter $\chi_D$ gives the public bound in terms of $v_2(D-1)$ at any recursive step in which new targets can be certified.

The complementary valuation $v_2(N+1)$ alone does not improve the worst $1/4$ initial threshold for general inputs. For any fixed $\nu\ge2$ choose $q\equiv-1\bmod 2^{\nu+1}$ and $p\equiv2^\nu-1\bmod 2^{\nu+1}$ prime. Then $N=pq^2$ has $v_2(N+1)=\nu$, yet both primes have $u_p=u_q=1$ and the minimum exponent sum is odd. There is a no-split negative coset of proportion $1/4$ for every such $\nu$.

The [finite replay](../experiments/cogentic-pooled-order-certificates.py) checks 22 exact recursive coset sizes and two rank fixtures. Modulo 77, the verified relations $(60,60)$ and $(60,-60)$ on the bases 2 and 3 give individually trivial words. Their sum and difference certify both bases and split 77. Modulo 63, the negative certificate for 5 leaves a stalled pool and the negative product $2\cdot5$ completes the rank and splits off a prime-power block. Run the replay with Python 3 from the repository root.
