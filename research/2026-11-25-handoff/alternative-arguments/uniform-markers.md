# Uniform small split markers for cyclic cubic conductors

Write L=log X. Let ell_1,…,ell_m be the first m primes congruent to 1 modulo 3 and set m=floor(κ L/log L), with fixed small κ>0. The prime number theorem in the fixed progression gives ell_i≪L uniformly for i≤m. Let K_i be the cyclic cubic subfield of Q(ζ_(ell_i)). The conclusions below hold uniformly for each K_i and each compositum K_iK_j, which have degrees 3 and 9.

## Split-marker supply

For any of these fields apply Thorner–Zaman, *A unified and improved Chebotarev density theorem*, Theorem 1.4, taking F=Q, H=G=Gal(K/Q), and the identity conjugacy class. The fixed field of H is Q. Thus their parameter D_base Q_char^(n_base) n_base^(n_base) equals the maximum conductor Q_char of a character of G. It equals ell_i or ell_i ell_j by the CRT realization of these abelian fields. There are no nontrivial real characters because G has odd order, and the principal zeta function has no possible exceptional real zero in the stated range. The error in Theorem 1.4 is therefore

    O(exp(−c_3 log Y/log Q_char) + exp(−√(c_3 log Y))),

provided Y≥Q_char^c_2. The constants are absolute and effective by Theorem 1.1 and the last sentence of Theorem 1.4. At Y=L^B, a fixed sufficiently large absolute B makes the first error term less than 1/4 after its constant and makes the hypothesis hold uniformly. The second error term tends uniformly to zero. Thus the number of completely split rational primes s≤Y is ≫Y/log Y for every field under consideration. [Thorner–Zaman, Theorems 1.1 and 1.4](https://arxiv.org/pdf/1803.02823#page=3)

Alternatively, apply Thorner–Zaman's progression Corollary 1.4 to each of the classes in the common kernel of the cubic characters and sum. At Y≥q^12 and with B large enough, each error is at most half its main term. For modulus q=ell_i or ell_i ell_j, a possible exceptional real character has nontrivial restriction to the kernel because the kernel has odd index. Thus its sum over the kernel is zero. The exceptional term cancels on summing main terms, and the relative errors still sum to at most half their sum. This is also a proof for every field, without discarding any moduli. [Thorner–Zaman, Corollary 1.4 and Remark 1.5](https://arxiv.org/pdf/2108.10878#page=3)

A weaker alternative that already suffices is Maynard's Theorem 2. Uniformly at Y≥q^8 and q≥q_2, each reduced class has at least a constant times

    (log q)/√q · Y/(φ(q)log Y)

primes up to Y. Sum this over the φ(q)/[K:Q] classes where the cubic characters equal one. As q≪L², this supplies ≫Y/(L log Y) markers. The bounded moduli q<q_2 follow from the usual fixed-modulus prime number theorem. This loses one power of L in the marker count, which can be absorbed by increasing B. [Maynard, Theorem 2](https://arxiv.org/pdf/1201.1777#page=3)

## Uniform product-box calculation

For K_i choose a Gaussian period η_i generating it. Its three conjugates have absolute value at most ell_i. For K_iK_j use the products η_i^aη_j^b with 0≤a,b≤2 as the basis of the order Z[η_i,η_j]. For K_i use the analogous power basis. These are linearly independent because the two extensions with distinct prime conductors are linearly disjoint. Write k=3 or 9 for the field degree and A for the order. Every real embedding of a basis element has size O(L^4), uniformly for all i,j. The real embedding matrix V has |det V| equal to the positive square root of the order discriminant and hence at least one. By cofactors its inverse has max-norm operator bound O(L^(4(k−1))). The order index in O_K is O(L^(4k)) by the same determinant upper bound, so all tested primes t≥X are coprime to it.

Let s≤Y be one of the completely split primes and choose one residue-degree-one prime ideal above it. Intersect it with A. The resulting coordinate lattice has index s because the reduction map onto F_s is already surjective on rational integers. Minkowski on the coefficient cube produces a nonzero a_s with coefficient norm ≤2s^(1/k). Hence each archimedean value has absolute value O(L^4 s^(1/k)), and

    |Nm(a_s)|=s m_s,   1≤m_s≪L^(4k)≤L^36

up to an absolute constant. Discard all s below a common bound C L^36 on m_s. This loses negligible markers if B is chosen large, even with Maynard alone. The remaining s uniquely mark their norm products since no marker prime s divides any m_s.

Take products of r distinct markers. Their embedding bound multiplies, and the inverse V bound is applied just once to the result. For products in the coordinate cube of radius X² we may therefore take

    r=(2/(B/k+4)+o(1)) L/log L,

by leaving O(log L) room in the logarithmic budget before dividing by the one-generator growth. The marker count P is ≫ L^B/log L from Thorner–Zaman, giving

    log binomial(P,r) = (2k(B−1)/(B+4k)+o(1)) L.

Using Maynard's lower count gives ≥(2k(B−2)/(B+4k)+o(1)) L instead. All estimates are uniform in i,j. The additive large-sieve proof for the coordinate box gives at most X^(2k(1+4k)/(B+4k)+o(1)) exceptional tested primes under the first marker count, or X^(2k(2+4k)/(B+4k)+o(1)) under the second. In both cases B≥2000 makes this exponent less than 1/2 for k≤9. Taking a union over O(m²) fields and then dividing by the number of tested primes gives a saving X^(−1/2+o(1)) or better. The shifts are replaced here by elements of the uniform coefficient box of radius 2Y^(1/k).

For joint generation at a pair of tested primes p,q, use the same uniform markers in the coordinate cube of radius X⁴. This doubles the product-cardinality exponent and the extra exceptional-pair exponent from the additive large sieve. If the group generated at pq has proper image although each individual prime has full image, a killing character has nonprincipal factors at both primes. Hence its nonzero additive frequencies have exact joint denominator pq and are disjoint for distinct unordered pairs. For B≥2000, the extra bad pairs are bounded by X^(1+o(1)) even with the weaker marker count. Pairs involving an individually bad prime number at most X^(3/2+o(1)), so the exceptional proportion is again X^(−1/2+o(1)). The union over the conductor fields does not change that exponent.

## Exponential profile cutoff

The full compositum of the K_i has Galois group C_3^m by the cyclotomic CRT. Write Q_all=∏ell_i. Then log Q_all≤(κ+o(1))log X, since each ell_i≪L. The CRT gives φ(Q_all)/3^m reduced residue classes for each profile in C_3^m.

To dominate actual prime profiles by the uniform profile measure it suffices to use Brun–Titchmarsh. If κ<1/4, then each reduced residue class has ≪X/(φ(Q_all)log X) primes in [X,2X], giving profile mass O(3^−m) after summing over the classes in that profile and normalizing by the total number of primes. Equivalently, Thorner–Zaman Theorem 1.4 applies to the full compositum with H=G and base Q. Its maximum character conductor is Q_all and still no nontrivial real character occurs. Small κ makes X≥Q_all^c_2 and gives relative error bounded by a fixed constant for every profile. Thus product profile distributions of distinct balanced primes are dominated by a fixed multiple of the uniform product measure. Any uniform-profile miss bound exp(−c m) transfers unchanged in rate, and X^(−1/2+o(1)) from the generation exceptions is negligible there. [Montgomery–Vaughan, Brun–Titchmarsh](https://doi.org/10.1112/S0025579300004708)
