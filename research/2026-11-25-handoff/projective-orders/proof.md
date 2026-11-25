# Exact 2-primary profiles of projective reductions

Let K=Q(θ) have degree k and normal closure E. Let α_1,…,α_u be nonzero elements of K. Exclude primes dividing their denominators or norms, 2, and the discriminant of the chosen polynomial for θ. At an eligible rational prime t, write d_1,…,d_r for its splitting degrees and

    a_i=v_2(t^{d_i}−1),   a_0=v_2(t−1).

The projective group is

    P_t = (∏_i F_(t^{d_i})^×)/F_t^×,

where scalars are diagonal. Under the projective Kummer independence condition below, conditional on the splitting type and any compatible residue class t mod 2^m with m>max_i a_i, the 2-primary components of the u marked projective classes are independently uniform in the Sylow 2-subgroup of P_t. The conditioning is about natural density of rational primes. In particular the probability that all u classes have odd order is exactly

    2^(−u(Σ_i a_i−a_0)).

## Sufficient independence conditions

Write α_(j,l) for the conjugates of α_j in E, indexed by the k embeddings l of K. In the strongest form assume that the ku elements α_(j,l) have independent classes modulo 2^m powers in F_m=E(μ_(2^m)), for every m. A sufficient valuation construction is to isolate each coordinate at an odd prime. For example choose α_j with absolute norm a distinct odd prime ell_j unramified in E. Such an α_j has a single norm-ell_j prime ideal of valuation one in K. At a prime of E over ell_j exactly one conjugate α_(j,l) has valuation one and every other marked conjugate has valuation zero. The marked degree-one prime corresponds to a singleton orbit of that prime’s decomposition group on the embeddings of K. Conjugating the prime of E gives this property for every l. Such markers exist for any fixed K by choosing odd rational primes splitting completely in a normal closure of the Hilbert class field, so their degree-one prime ideals in K are principal. The cyclotomic extension F_m/E is unramified above odd primes and preserves these valuations. Applying them to a purported 2^m-power relation shows each exponent is zero modulo 2^m.

A weaker sufficient condition is independence of the u(k−1) ratios α_(j,l)/α_(j,l0), l≠l0, modulo 2^m powers in F_m for every m. It can be proved by showing that any 2^m-power relation among conjugates forces a constant exponent vector in each block, as long as k is odd. In the ratio relation the exponents in each block sum to zero. Since k is odd, a constant block vector with zero sum vanishes modulo 2^m. For example if independent odd-degree fields share a marker prime and the joint Galois action allows the single marked conjugate in each block to be chosen independently, the valuation equations on the common prime imply this constant-vector condition by subtraction. Ordinary multiplicative independence of the α_j alone does not imply the projective condition, as α and 2α have identical projective images.

## Frobenius cycle sums

One can also build suitable **integer translates** for a fixed monic defining polynomial. At stage $j$, choose an odd prime $v_j$ larger than the degree, splitting completely, away from the polynomial discriminant and all earlier marker norms. Set $c_j$ equal to a root modulo $v_j$ and choose a lift modulo $v_j^2$ other than its unique Hensel lift. At every earlier marker prime choose $c_j$ away from all the roots, and combine the congruences by CRT. The translate $\theta-c_j$ then has valuation one at its selected prime and zero at the others over $v_j$. The earlier translates are units at $v_j$, and all later translates are units at the earlier markers by construction. Conjugation supplies the separating valuations above each marker, which persist in the two-power cyclotomic tower. The finite examples below use distinct prime norms.

Fix m and N=2^m. Adjoin N-th roots b_(j,l) of all α_(j,l) to F_m, giving a Galois extension of Q. If the full Kummer condition holds, its kernel over F_m is (Z/N)^(uk) by the Kummer pairing. Fix compatible base data σ∈Gal(E/Q) and s∈(Z/N)^×. A lift h acts by

    h(ζ_N)=ζ_N^s,
    h(b_(j,l))=ζ_N^(v_(j,l)) b_(j,σl).

When h runs through the full lift coset, the phase vector v is uniformly distributed in all (Z/N)^(uk). For a cycle C of σ of length d, represented by l∈C, iteration gives

    h^d(b_(j,l))/b_(j,l)
         = ζ_N^(Σ_(b=0)^(d−1) s^(d−1−b) v_(j,σ^b l)).

Write this cycle sum as W_(j,C). For the corresponding a=v_2(t^d−1), at a prime where h is a Frobenius lift apply the same identity to b_(j,l)^(N/2^a) and reduce. Frobenius acts there as t-powering and reduction of ζ_(2^a) retains its order. This identifies

    ζ_(2^a)^(W_(j,C)) = (α_(j,l) mod t)^((t^d−1)/2^a)

in the relevant residue field. The power map on the right kills the odd part and is an automorphism of the 2-Sylow subgroup because its exponent is odd. On the left the cycle sum is uniform modulo 2^a because a coefficient is one. Different cycles use disjoint coordinates. Thus before quotienting, the 2-Sylow coordinates are mutually independent and uniform. Quotienting by diagonal scalars of 2-order 2^a0 preserves uniformity and divides the order by that factor.

For the ratio version, adjoining N-th roots of the ratios suffices to make the phase vectors uniform modulo a common shift in each block. Indeed the ratio-root phases in the field above are v_(j,l)−v_(j,l0), and restriction onto the ratio extension is surjective. For each d a global common phase shift c adds

    c T_d,   T_d=1+t+⋯+t^(d−1),

to the cycle sum modulo 2^a. This is precisely the image of a scalar λ∈F_t^× chosen with λ^((t−1)/2^a0)=ζ_(2^a0)^c. To verify it use v_2(T_d)=a−a_0 and

    λ^((t^d−1)/2^a) = (λ^((t−1)/2^a0))^(T_d/2^(a−a_0)).

Thus the map to the projective 2-Sylow group factors through the phase quotient by common shifts, and stays surjective since the unquotiented cycle-sum map is already surjective. Uniformity and the probability formula follow again.

The condition on the projective orders is conjugacy invariant. Chebotarev therefore turns these proportions of lifts into conditional prime densities, including if the given splitting degrees come from several conjugacy classes. One must use compatible σ and s if E intersects the cyclotomic tower. Fixed finite m suffices on each progression where all a_i are determined. The remaining primes at large m lie in at most two classes near ±1 modulo 2^(m−O_k(1)), by the valuation formula below. Their upper density tends to zero, so the geometric averages obtained from the finite levels are natural densities as well.

## Geometric averages and entanglement

Write A=r−1, B=# even d_i, and D=Σ_even (v_2(d_i)−1). The 2-adic lifting-the-exponent formula gives

    Σ_i a_i−a_0 = A v_2(t−1)+B v_2(t+1)+D.

If E is disjoint from the 2-power cyclotomic tower, t's cyclotomic coordinate is uniform independently of the splitting type. For uniform odd t, the pair (v_2(t−1),v_2(t+1)) equals (j,1) or (1,j), each with probability 2^(−j), for j≥2. The exact conditional average for a fixed splitting type is therefore

    2^(−uD) [
      2^(−uB)/(2^(1+uA)(2^(1+uA)−1))
      + 2^(−uA)/(2^(1+uB)(2^(1+uB)−1))
    ].

For the cubic split type this reduces to 1/(2^(2u+1)−1). For a disjoint S3 transposition it is 2^(−2u)/(2^(u+1)−1). At u=1 these are 1/7 and 1/12. The inert cubic type has no projective 2-part. Cyclic cubic fields are automatically disjoint by degree. An odd discriminant also suffices in any degree, since the normal closure is then unramified at 2.

For a general S3 field the only possible nontrivial intersection is its quadratic resolvent, one of Q(i), Q(√2), Q(√−2). For example when it is Q(√2), a transposition occurs only when t≡3 or 5 mod 8. Then v_2(t²−1)=3 identically, so the transposition average is 2^(−3u). At a split prime t≡1 or 7 mod 8, so its average is

    2^(−2u−1) + 2^(−4u−1)/(2^(2u+1)−1).

This quadratic example shows that the disjoint qualifier for the averaged numbers is essential. The fixed compatible-class formula itself does not require disjointness.

For several fields with independent joint projective Kummer blocks, multiply conditional probabilities at a fixed cyclotomic residue of t. The unconditional averages generally do not multiply across fields because all fields share the same t and therefore the same 2-adic valuations. For a cubic split type the conditional odd-order failure is always at most 4^(−u). For a transposition it is at most 8^(−u), since t²−1 is divisible by eight. Thus uniform exponential miss bounds still follow from conditional independence. For instance with disjoint S3 profile blocks and an independent candidate covered prime, the probability of inertness at the covered prime is 1/3 and conditional even-order witness probability at the other is at least (1−4^(−u))/6+(1−8^(−u))/2. At u=1 this gives a per-field pair-split probability at least 3/16, simultaneously for every compatible t residue.

## Full conditional order law

The Sylow 2-subgroup of P_t is obtained from the direct product with exponents a_i by replacing one smallest a_i by a_i−a_0. To see this, pick generators of the local cyclic groups that identify a generator of the diagonal scalar subgroup with coordinate vector (2^(a_i−a_0))_i. Once i0 has minimum a_i, subtract 2^(a_i−a_i0) times coordinate i0 from coordinate i for every i≠i0. These are well-defined automorphisms and leave the scalar generator supported on coordinate i0 only. Thus the exact probability that all u classes have 2-adic order valuation ≤b is

    2^(−u Σ_i max(a'_i−b, 0)),

where the modified exponents are a'_i. This specializes to the odd order formula at b=0.

## Related work

The projective group is the group of F_t-points of the torus Res_(K/Q) G_m/G_m at good primes, by Hilbert 90. The u marked points form one point in the u-fold product of this torus. Lombardo–Perucca's general density theorem expresses the coprime-order density of such a point as a Kummer-weighted Haar integral. For this torus with maximal projective Kummer degree, the reciprocal kernel factor at a Frobenius element agrees with the cycle calculation above. In fact its determinant on the projective Tate module is ∏_i(t^(d_i)−1)/(t−1) up to sign, and the u-fold product raises it to the u-th power. Perucca separately treats simultaneous prescribed valuations on tori and coprime order with prescribed Frobenius for multiplicative groups. [Lombardo–Perucca, Theorem 1](https://arxiv.org/pdf/1612.02847#page=2) · [Perucca, simultaneous valuations](https://arxiv.org/pdf/0909.4806#page=2) · [Perucca, order and Frobenius](https://orbilu.uni.lu/bitstream/10993/34418/1/Perucca-Frobenius.pdf)

## Finite checks

Run `gp -fq replay.gp` for the finite prime profiles through 250,000. Each field uses two translated roots with distinct odd prime norms away from the polynomial discriminant. The test raises each witness to the least common multiple of the odd parts of the local ambient group orders, then checks scalarity by its nonconstant coefficients. It covers all splitting types in the C3, S3 and S4 examples and the entangled S3 example with quadratic resolvent Q(√2). Both u=1 and u=2 are checked. The empirical proportions are compared with the conditional model averaged over the actual test primes. Finite agreement is a diagnostic, while exact densities come from the proof. Run `python3 -B cycles.py` for exact small projective phase-fiber enumeration independent of the prime profile counts.
