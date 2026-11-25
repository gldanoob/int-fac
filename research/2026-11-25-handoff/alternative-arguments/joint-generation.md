# Average deterministic factoring from one supplied divisor sum

The original close/far harmonic argument is valid. It can also be replaced by direct joint generation at pq in a quadratic order with small radicand selected at the smaller prime. This route uses no profiles for the proof of the average-time result.

## A uniform quadratic generating box

Let d≥2 be squarefree and d≤(log(2T))^D. In A_d=Z[√d] use coordinates (a,b). Let Y=(log T)^B with B>8D, large enough below. For each completely split prime s≤Y choose one prime ideal of degree one above it and intersect it with A_d. Its coefficient lattice has determinant s because scalars already surject onto F_s. Minkowski supplies a nonzero generator marker α_s=a+b√d with |a|,|b|≤2√s. The norm satisfies

    |Nm(α_s)| = m_s s,  1≤m_s≤4(1+d).

Discard s≤4(1+d), so each marker prime occurs in its own norm and in no other marker multiplier. The conductor q of Q(√d) is ≤4d. Maynard's Theorem 2 for x=Y≥q^8 gives, uniformly for large conductor q and for every reduced class a, at least a constant times

    (log q)/√q · Y/(φ(q)log Y)

primes in that class. Sum over the φ(q)/2 splitting classes. For the bounded remaining conductors, use the classical prime number theorem in each of the finitely many progressions. The number P of remaining s is at least (log T)^(B−D/2+o(1)). This uniform lower bound allows a real exceptional character and its associated zero. [Maynard, Theorem 2](https://arxiv.org/pdf/1201.1777#page=3)

All embeddings of a marker have magnitude at most O((log T)^(D/2)√Y). Products of r distinct markers remain in the coordinate box of radius T² for

    r=(4/(B+D)+o(1))log T/loglog T,

chosen by rounding down with ample constant-factor slack. Recovering coefficients from the two embeddings does not increase their bound since d≥2. The norm support distinguishes every r-element subset of markers, hence the product set S has

    |S| ≥ T^(4(B−D/2−1)/(B+D)+o(1)).

For each rational prime t∈[T,2T] the marker norms are coprime to t for large T. If the reductions of the coefficient box of radius 2√Y fail to generate (A_d/tA_d)^×, choose a nonprincipal character χ trivial on the generated subgroup, extended by zero to nonunits. It is one on S, with additive Fourier mean zero and normalized squared l2 norm ≤1. Cauchy and the additive large sieve for separated points v/t in R²/Z² give

    number of exceptional t · |S|² ≪ T⁴ |S|.

The sieve uses spacing at least 1/(4T²) between distinct frequency vectors and the coefficient box of radius T². Thus there are at most

    T^(4(3D/2+1)/(B+D)+o(1))

exceptions, and the bound is uniform in d. Union over polylogarithmically many d does not change the exponent. [Huxley, multidimensional additive large sieve](https://doi.org/10.1112/S0025579300002540)

## Joint generation at unbalanced semiprimes

The same calculation applies with distinct prime factors p,q, modulus w=pq∈[T,2T], and d≤(log(2T))^D, provided the two local images already generate separately and every marker norm is coprime to w. For a proper joint subgroup, choose a nontrivial character χ_pχ_q trivial on it. Both local factors are nonprincipal by individual generation. Its additive Fourier coefficients vanish whenever the frequency vector is zero modulo p or zero modulo q, since the corresponding normalized local mean is zero. Every frequency vector in the support therefore has exact common denominator pq. Frequencies from different w are disjoint and still 1/(4T²)-separated. The same sieve yields at most T^(4(3D/2+1)/(B+D)+o(1)) bad semiprimes, after the union over d, with no balance restriction.

If w≤Z and p,q>(log Z)^C for C>B+D+1, the marker norms are automatically coprime to w. This is why uniform generation at pq may use a scale depending on log(pq) even when p and q are unbalanced. The chosen d will depend only on log p, so individual generation can use the local scale at both p and q. Enlarge the joint coefficient box by an absolute constant to ensure it contains both local boxes.

## Small nonsquares

For prime p in a dyadic interval [T,2T], the one-dimensional rational version shows that, with at most T^(2/D+o(1)) exceptions, some prime d≤(log p)^D is a nonsquare modulo p. Take smooth products of r=(2/D+o(1))log T/loglog T distinct primes up to (log T)^D, supported on [1,T²]. If all marker primes are squares, the Legendre character is one on the product set. Its additive Fourier mean is zero and its normalized squared l2 norm is at most one. The one-dimensional large sieve gives the stated count. Only a nonsquare at the smaller prime is needed.

For example D=5, B=80 and C=87 give local, joint and rational exceptional counts bounded by T^0.45 uniformly for large T. The underlying exponent from each sieve is 0.4. Here C can be increased freely. None of the constants depend on the input or on its number of prime factors.

## Static splitting algorithm on the favourable residual inputs

Given N and M=σ(N), fix a search through all positive squarefree d≤(log Z)^D and all a,b≤O((log Z)^(B/2)) in absolute value. Input Z can be the next power of two above N. For each remaining composite cofactor n, perform gcds with d and Nm(a+b√d). If a gcd is proper, return it. If a candidate is a unit, test A=a+b√d to successive powers 2^i M_odd, 0≤i≤v_2(M), in (Z/nZ)[√d]. A test yields a proper split when the gcd of n with the nonconstant coefficient is proper. Use primality testing and recurse on a proper split, with the same original M. Each run has polynomial bit complexity in log Z, including recursion over at most O(log Z) nodes. Runs may stop when no candidate works.

Suppose all remaining prime factors have original multiplicity one. For any two remaining primes p<q choose a small squarefree d that is a nonsquare at p and for which the box generates the local groups separately and jointly. The projective groups at p and q are cyclic of orders p+1 and q−(d/q), respectively. This follows from the cyclic multiplicative group of F_(p²) and the diagonal quotient of F_q× × F_q× in the split case. Both projective orders are even. The original M is divisible by p+1.

There is a single joint box element whose two projective orders have different 2-adic valuations. If the two group 2-exponents differ, one generator must attain the largest exponent at the larger side. If the exponents agree, at least one generator has opposite square signs under the two local quadratic characters, since otherwise all signs lie in the diagonal. Such a witness is a unit at p,q. A norm-gcd at some other prime is already proper. Otherwise the chain reaches scalarity at p by the final exponent M. If it does not reach scalarity at q this endpoint separates. If it reaches both, the first scalar index is the 2-adic valuation of the projective order at each prime, so an earlier step separates. This argument extends through every recursive cofactor, with no restriction on the number of distinct primes.

## A summable tail and average runtime

Let L≥L_0=(log Z)^C. Remove all prime powers whose underlying prime is ≤L before attempting the static search. The fraction of integers N≤Z with a squared prime divisor p>L is at most Σ_(m>L)m^−2≪1/L. A bad individual prime t>L affects at most Z/t inputs. Summing the uniform dyadic counts T^0.45 with these weights gives a fraction O(L^−0.55). A bad joint modulus w=pq>L² affects at most Z/w inputs. The dyadic sum for these is O(L^−1.10). Thus after removal and static tests at L the failure probability is O(L^−0.55), uniformly in the depth of the stage. The same bounds hold with a factor two on the dyadic population [Z/2,Z].

Bostan–Gaudry–Schost Lemma 13 finds a prime divisor at most L or certifies no such divisor in O(M_int(√L log N)+log L M_int(log N)loglog N) deterministic bit operations. Repeat at most log_2 N times to strip all small primes with full multiplicity. Thus a stage costs at most √L times a polynomial in log Z. Start at L_0 and double L after each incomplete static run. At L≥√N the trial step alone proves every remaining cofactor is prime or one, so the algorithm always completes. The mean stage cost over the dyadic population is at most a polylogarithmic factor times

    √L_0 + Σ_(j≥1) (2^j L_0)^1/2 (2^(j−1)L_0)^−0.55,

which converges and is polylogarithmic in Z. Summing dyadic population sizes gives the same average-time bound over N≤Z. Correctness uses exact gcds and primality tests and does not depend on an exceptional-set hypothesis. The bounds only control the runtime. [Bostan–Gaudry–Schost, Lemma 13](https://mathexp.eu/bostan/publications/BoGaSc07.pdf#page=15)

## Audit of the alternative signature argument

Let m=ceil(2 log_2 L), let ell_j be the first m primes congruent to one modulo four, and Q=8∏ell_j. Quadratic reciprocity turns a prescribed sign profile into exactly φ(Q)/2^m reduced classes. The largest ell_j is O(log L loglog L), below a fixed power of log p for p>L. If q≥Q², Brun–Titchmarsh on each dyadic interval of q gives for fixed p an upper bound O(2^−m loglog Z) for the sum of 1/q over matching profiles. Summing 1/p contributes another O(loglog Z). This is O(L^−2(loglog Z)^2), negligible relative to the individual-prime tail. If q<Q², log(pq)=O(log L loglog L)≪(log p)^2. The primitive quadratic χ=(·/p)(·/q) then has a nonsquare marker below (log(pq))^D unless pq is one of at most T^(2/D+o(1)) exceptional products in a dyadic T interval. The frequencies in its additive transform have exact denominator pq, so the one-dimensional rational product sieve proves this uniformly. A p,q collision despite all such markers has total harmonic weight O(L^−2+4/D+o(1)). The d produced by close products is within (log p)^(2D). The argument checks, but the joint-generation route proves the needed separation directly.

## Related primary results

Bach–Miller–Shallit, Theorem 2 and §4, give randomized polynomial-time complete factoring from the one value σ(N), including arbitrary multiplicities. Their quadratic split analysis is randomized. Miller's Lemma 5 and Theorem 3 give deterministic polynomial-time factoring under ERH from Euler totient and related multiples of the group exponent. Morain–Renault–Smith §4.2 and Theorem 5.5 give deterministic size-regime results with unfactored p+1-type hints or a single σ. Źrałek's partial deterministic cyclotomic results use smoothness and prescribed fields. The focused search did not identify a prior unconditional deterministic polynomial average-time result from a single supplied ordinary divisor sum. [Bach–Miller–Shallit](https://www.cs.cmu.edu/~glmiller/Publications/Papers/BMS86.pdf) · [Miller](https://www.cs.cmu.edu/~glmiller/Publications/Papers/Mi76.pdf#page=11) · [Morain–Renault–Smith](https://arxiv.org/pdf/1802.08444) · [Źrałek](https://arxiv.org/pdf/0707.4102)

There is strong prior art for the distinct Euler-totient oracle. Burthe bounds the arithmetic mean of the integer cutoff G(N) that generates (Z/NZ)^× by O(log^97 Z). Źrałek §6 explicitly draws the deterministic almost-all factoring conclusion from Euler's totient. Doubling the base cutoff and using the projections of the full generating group to recursive cofactors gives deterministic polynomial average time from φ(N) as a consequence. Pomykała–Radziejewski Theorem 3.1 applies a harmonic count of multiples of primitive-character exceptional conductors to complete factoring with one Euler-totient query. Their §6 treats one supplied multiple of φ on squarefree inputs. These are close methodological precedents. [Burthe, Corollary 3.3](https://matwbn.icm.edu.pl/ksiazki/aa/aa80/aa8043.pdf) · [Źrałek, §6](https://arxiv.org/pdf/0707.4102#page=13) · [Pomykała–Radziejewski](https://doi.org/10.1515/jmc-2019-0023)
