# The best height-six collision rate under fixed public character profiles

This is an exact limiting probability for irreducibility-mask collisions. It is not a new numerical height-six counterexample or a finite-time lower bound for arbitrary searches.

Let F be the set of rational cubic fields represented by monic cubics with all three remaining coefficients in [-6,6]. Fix every quadratic character occurring in their discriminants, and fix the four cyclic-cubic characters. Independently and uniformly sample p,q from primes in [X,2X] satisfying these fixed data, with p≠q. At unramified primes the mask has one bit per field: one for irreducibility, zero for a root. Let X tend to infinity with the character data fixed.

Among all fixed character profiles, the largest limiting mask-collision probability is

    P_max = (5/9)^55 (5825/531441)(61/729)
          = 14213 * 5^57 / 3^128
          = 8.364796870309026... * 10^-18.

It occurs with p,q≡1 (mod 3). The optimum on p,q≡2 (mod 3) is (5/9)^70 = 1.3518379767324537... * 10^-18. Cyclic bits may be fixed identically at both primes, so they contribute one. The replay fixes them all to split.

The upper bound P_max also applies when the two primes are sampled with different fixed quadratic profiles, including different branches modulo 3, and to independent mixtures of such profiles. It follows from Cauchy–Schwarz on their full mask distributions. This does not cover deliberately imposed conditions on nonabelian cubic Artin coordinates or arbitrary numerical input-dependent filters.

## 1. Enumeration and degrees

Independent PARI enumeration gives 369 cubic fields: four cyclic fields of conductors 7,9,13,19 and 365 S3 fields. The latter have 329 distinct nontrivial quadratic resolvents. Their squareclasses span dimension 154 over F2. On fixing p mod 3, there are 153 remaining independent binary character coordinates.

Each S3 closure has degree 6 over Q and degree 3 over its quadratic resolvent K_D. For fields sharing K_D let r_D be the dimension over F3 of the joint cubic Galois group over K_D. All groups except four have rank equal to the number of fields in that group. The exceptions are:

    K_D       number of fields     r_D
    -3                10            6
    -19                5            3
    -51                4            2
    -307               3            2

The total S3 ternary rank is 356. The four cyclic characters add four independent ternary directions. Consequently the full joint Galois group has order $2^{154} \cdot 3^{360}$. Only its active coordinates enter a specified mask.

Every pure irreducible cubic in the box has a nonpure translate in the same box: translate by +1 or -1 to reduce the absolute constant coefficient, introducing coefficients of absolute value 3. Thus retaining all 369 represented fields does not introduce irrelevant pure-only field conditions.

## 2. Unconditional certification of the repeated-resolvent ranks

The argument does not rely on a heuristic class-group computation. The supplied exact algebraic checks, together with ramification, certify the ranks and the required line arrangements.

For a cubic field of discriminant D_K f², the cyclic extension of K_D in its normal closure has conductor f O_K. Conjugation inverts its cubic character. It therefore factors through the ring class group of conductor f: rational principal ideles are fixed by conjugation, so an odd-order anti-invariant character is trivial on them. This explains why ring class groups give rank upper bounds, but the checks below also prove all upper bounds directly by explicit field inclusions.

For two distinct fields with one resolvent, the cubic directions are distinct, hence independent. For the other three-field groups (D=13,-7,-4,-11), each field has a rational ramification prime absent from the other two conductors:

    D=13:   conductors 18,10,11; use primes 3,5,11;
    D=-7:   conductors 9,5,17; use primes 3,5,17;
    D=-4:   conductors 9,11,37; use primes 3,11,37;
    D=-11:  conductors 9,2,17; use primes 3,2,17.

Restricting a putative character relation to inertia at these primes proves independence. The trivial compositum bound gives the matching upper rank.

For D=-19 take the three basis fields with polynomials

    a=x³-2x-2          (discriminant -76, conductor 2),
    b=x³+6x-5         (discriminant -1539, conductor 9),
    c=x³-x²+5x-6      (discriminant -931, conductor 7).

Their distinct ramification primes 2,3,7 prove rank at least 3. The remaining fields x³-12x-22 and x³-x²-9x-13 embed, respectively, in the degree-nine composita ab and ac. Their Galois closures therefore add no direction, proving rank at most 3. Each extra field differs from either constituent, so its line has both coefficients nonzero. Scaling the basis makes the five lines

    e1,e2,e3,e1+e2,e1+e3.

For D=-51, the two basis polynomials x³-x²+x-3 and x³+3x-8 have discriminants -204 and -459. Both other fields, x³-6x-10 and x³+6x-6, embed in their degree-nine compositum. Four distinct lines in a ternary plane are all its projective lines. The rank is exactly 2.

For D=-307, x³-x²+3x+2 and x³-x²+x-7 are distinct basis fields. The third, x³+4x-6, embeds in their degree-nine compositum. Three distinct lines in a ternary plane are equivalent to e1,e2,e1+e2. Again rank 2.

For D=-3, the ten fields are explicitly isomorphic to pure cubic fields whose radicand exponent vectors on the primes (2,3,5,7,11,17) are

    (1,2,0,0,0,0), (0,0,0,0,0,1), (0,0,0,1,0,0),
    (1,1,0,0,0,0), (0,0,1,0,0,0), (1,0,1,0,0,0),
    (0,1,0,0,0,0), (1,0,0,0,0,0),
    (1,0,0,2,0,0), (1,0,0,0,2,0).

Their span is six-dimensional. Kummer theory over Q(sqrt(-3)) gives rank 6: the six rational prime classes are independent modulo cubes, as their valuations have independent support; the ramification index 2 at 3 is invertible modulo 3. The displayed vectors also prove that these ten directions generate all six. check-blocks.gp verifies each pure-cubic field identification by exact polredabs equality and verifies every preceding embedding by nfisincl. Distinctness and discriminants are checked by the complete canonical enumeration.

## 3. Independence across resolvents and from cyclic data

Let B/Q be the abelian compositum of the quadratic resolvents and the four cyclic fields. Over B, the joint cubic kernel belonging to K_D is V_D=F3^r_D. Adjoining B preserves its rank: any nontrivial cubic quotient acted on by quadratic conjugation through inversion is nonabelian over Q and cannot lie in B.

The quadratic Galois group acts on V_D through the character of K_D. Different resolvents give different characters. Character projections over F3 separate these eigenspaces because the acting group has two-power order. A subdirect subgroup projecting onto every block must therefore be the full product of the blocks. Equivalently, commutators with a sign acting by inversion retain each block and show it remains disjoint from abelian data. Thus all V_D are independent over B. The four cyclic fields are mutually independent because their conductors 7,9,13,19 are pairwise coprime; their characters lie in B and do not remove any V_D.

These are the independence requirements used in the calculation. No independence is assumed between the several fields sharing one resolvent: their exact line arrangements are used instead.

On a fixed quadratic profile, a negative resolvent sign gives a transposition and mask bit zero throughout that group. A positive sign leaves a uniform vector v in V_D; its field bits are 1{l_i(v)≠0} for the indicated cubic lines l_i. Uniform vectors for different D and the two independently sampled primes are independent. Chebotarev gives these distributions in the limit X→infinity. All profiles are attainable by quadratic reciprocity and CRT; cyclic splitting can be imposed simultaneously because its order-three characters are independent of the quadratic characters.

## 4. Exact local collision factors

For m independent directions the factor is (5/9)^m. For an arbitrary line family, enumerate vectors v and count n_z giving each zero pattern z. Its collision factor is sum_z n_z²/3^(2r).

The exceptional histograms are:

    block       pattern multiplicities                         factor
    -3          1×1, 32×2, 64×4, 37×8, 5×16, 1×32             5825/531441
    -19         1×1, 11×2, 1×4                                  61/729
    -51,-307    1×1, 4×2                                        17/81

Here a×b means a distinct patterns each attained by b vectors. collision-profile.py enumerates all 729,27,9 vectors, respectively, with exact integer arithmetic. Thus none of these factors is a heuristic estimate.

## 5. Exact optimization over all character profiles

Use x_-1 for the sign of (−1/p), x_2 for (2/p), and x_l for (p/l) at odd marker primes l≠3. The value x_3 is fixed by p mod 3. Quadratic reciprocity writes every resolvent sign as an affine binary parity in these 153 variables. A negative sign contributes collision factor 1, a positive sign its exact factor from section 4.

The objective is therefore a product of positive rational factors, each depending on a small variable set. Eliminate a variable by multiplying every incident factor and taking the larger value over its two possible signs; retain the maximizing sign for backtracking. This max-product elimination is exact. Initial factors partition between buckets, so induction on eliminated variables proves it equals the global maximum over all assignments. The largest intermediate scope in this instance has eight variables. All comparisons and products use Fraction; floating point is used only to display the final number.

The attaining branch-one profile has 49 active resolvents and 70 field bits. Apart from the -3 and -19 blocks, its 55 directions are independent. This gives P_max above. The branch-two optimum has 70 independent active directions. The replay emits complete attaining sign profiles for both branches.

For profiles s,t let mu_s and mu_t be their probability distributions on the full 369-bit mask. Their cross-profile collision is their inner product. Cauchy–Schwarz bounds it by sqrt(||mu_s||² ||mu_t||²)≤P_max. Convex mixtures cannot increase the largest squared norm. Thus allowing different or mixed quadratic profiles does not improve this optimum under independent sampling.

## 6. What the birthday scale does and does not prove

In the limiting independent-sample model, m samples have expected collision-pair count choose(m,2)P_max, and the union bound bounds collision probability by the same expression. One expected pair requires approximately 488,975,724 samples. This is a rigorous statement about the limiting model, not a uniform finite-X Chebotarev estimate or a lower bound on all algorithms.

The finite genus-form scanner samples primes of a quadratic polynomial F(j,1). Equidistribution of Frobenius on that thin prime-value sequence is not proved here. The exact P_max describes primes conditioned only on the stated fixed character data, not the thin sequence's unproved runtime distribution. Additional Artin control can change the birthday rate and is outside the optimum.

Matching all bits is a necessary input to a dual-order height-six certificate, but a finite pair still needs exact cross-order and modular-power checks before being called a counterexample. No new full height-six collision was certified in this run. The [finite scan and complete literal replay](sample/README.md) accompany this calculation.
