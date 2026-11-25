# An executable order certificate from two imaginary quadratic fields

Google's deterministic extractor uses smooth norms in two fields with a common evaluation modulo $N$. A small specialization produces the order certificate from scratch with rational linear algebra. Imaginary quadratic fields have finite unit groups, eliminating the real logarithms and continued-fraction reconstruction in Cogentic Lemma 7.5. This gives a working way to study the certificate separately from the difficult question of how many smooth norms a given input supplies. The fields, relation matrix, exponent and divisor are all computed from $N$ and the stated search limits. [Cogentic, Lemmas 7.3–7.5](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=31) · [Buhler–Lenstra–Pomerance, number-field norm relations](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/1993_Book_TheDevelopmentOfTheNumberField.pdf) · [PARI/GP implementation](../experiments/cogentic-quadratic-order.gp)

## Relation and certificate

Take $m=\lfloor\sqrt N\rfloor$. For $i=1,2$ choose distinct small integer slopes $s_i$ and set $c_i=N-m^2-s_i m$, $f_i(X)=X^2+s_iX+c_i$. Their common evaluation is $f_1(m)=f_2(m)=N$. Use only polynomials with $D_i=s_i^2-4c_i<0$. Let $K_i=\mathbb Q(\theta_i)$ with $f_i(\theta_i)=0$. For a primitive integer pair $(a,b)$ with $b\ne0$ and $\gcd(a-bm,N)=1$ the two norms are
$$
 F_i(a,b)=\operatorname{Norm}(a-b\theta_i)=a^2+s_iab+c_i b^2>0 .
$$
Keep a column if both norms factor completely by trial division at primes $p\le B$ and no prime $p$ in its field norm satisfies $p^2\mid D_i$. The latter test only needs the trial primes. At any prime dividing the retained norm, $b$ is invertible modulo $p$ and $r=a/b\bmod p$ is a root of $f_i$. Because $p^2\nmid D_i$, the order $\mathbb Z[\theta_i]$ is maximal at $p$. The only prime ideal above $p$ which can divide $a-b\theta_i$ is $(p,\theta_i-r)$, of residue degree one. Its valuation equals $v_p(F_i(a,b))$. This also handles a ramified prime of discriminant valuation one. Hence the column with entries $v_p(F_i(a,b))$ in rows $(i,p,r)$ describes the complete ideal factorizations in the two fields. Repeated powers in the norms are allowed.

Let $V$ be the matrix of these columns. For any prime $\ell\le B$ coprime to $ND_1$ that splits in $K_1$, put a one in each of the two first-field rows above $\ell$, and zeros elsewhere, to form $b_\ell$. Skip the base if either row is missing. Solve $Vx=b_\ell$ over $\mathbb Q$ and verify every row. Put $k=\operatorname{den}(x)$, $z=kx$. The field elements
$$
   \epsilon_1=\ell^{-k}\prod_j(a_j-b_j\theta_1)^{z_j},
   \qquad \epsilon_2=\prod_j(a_j-b_j\theta_2)^{z_j}
$$
are units because all their ideal valuations vanish. Every imaginary quadratic unit has order dividing 12. For instance its two conjugates have modulus one, so its trace is an integer in $[-2,2]$ and its order lies in $\{1,2,3,4,6\}$. Both evaluation homomorphisms $\theta_i\mapsto m\bmod N$ extend across the denominators here, since $\ell$ and all $a_j-b_jm$ are units modulo $N$. Taking twelfth powers and dividing the two resulting congruences therefore gives $\ell^{12k}=1\bmod N$. The implementation checks that equality directly. Its gcd scan returns a verified proper divisor whenever the base has differing local two-parts of its order. [Gcd splitting proof and Lean check](cogentic-dense-exponents.md)

A whole batch of soluble targets can share a common exponent. Choose independent pivot rows and columns with nonsingular square minor $M$. Every right-hand side in the column space has a solution supported on those columns whose denominators divide $|\det M|$. Thus $12|\det M|$ works for every target whose column-space membership was checked. A single smaller denominator often suffices in the example.

## Joining distinct marks by their evaluated residue

Each smooth element has a label $a-bm\bmod N$. Retain one reference per label up to sign, across both fields. For each subsequent element with the same label up to sign, append its ideal-valuation vector minus the reference vector. The quotient of the two modular images is $1$ or $-1$, even when the marks differ, and even when they come from the same field. One reference generates every pair difference in the class. Every original same-mark column belongs to this new span after changing the signs of the second field's rows, which leaves the target vector unchanged.

When a linear combination of these differences equals $k b_\ell$, divide the first-field product by $\ell^k$ to get a unit. The second-field product is also a unit. Taking twelfth powers in both fields and multiplying the modular equations gives $\ell^{12k}=1\bmod N$. These evaluations can be performed by clearing the denominators of the marked expressions: all their modular images are units. In particular no reduction map on the entire maximal order is needed. The hash join tests exact equality of residues; its work is linear in the number of smooth marks up to sorting or dictionary overhead.

## A sufficient density within the split primes

Suppose the first polynomial has discriminant $D_1$ coprime to odd $N$, with $|D_1|\le N^{O(1)}$. Let $\delta$ be the primitive quadratic character of $K_1$ and let $B$ grow faster than every power of $\log N$. It suffices that $b_\ell$ be in the column space, with both rows present, for at least $(1/2+\eta)$ of the split primes in $(B/2,B]$, for any fixed $\eta>0$. Indeed for any character $\chi\ne1$ modulo $N$, both $\chi$ and $\chi\delta$ are nonprincipal, since the nontrivial conductor of $\delta$ is coprime to $N$. The Dirichlet-RH character estimate applied to both gives $\sum_{\ell:\,\delta(\ell)=1}\chi(\ell)=o(B/\log B)$ uniformly, after deleting ramified primes. The prime number theorem for $\delta$ gives $(1/2+o(1))$ of the dyadic primes split. If all the soluble bases lay in a proper subgroup of $(\mathbb Z/N\mathbb Z)^\times$, a nontrivial quotient character would be one on those bases, contradicting the sum bound by taking real parts. Thus the verified common exponent is divisible by $\lambda(N)$. Applied just to the quadratic characters detecting different local two-parts, the same estimate guarantees that the gcd scan gives a divisor at some soluble base. The argument counts the soluble targets **within the split primes** and makes no density assertion for the quadratic norm values. [Character estimate and extraction](cogentic-dense-exponents.md) · [Dirichlet theorem verification](https://math.mit.edu/~drew/grh/)

## Finite results

The replay searches $1\le a\le220$, $1\le |b|\le220$, primes up to 71, and the six choices $s_1=-i,s_2=-j$ with $0\le i<j\le3$. All eight development inputs use the same schedule. The table uses identical marks in both fields and gives the first certificate producing a split. The last two columns count the paired smooth relations and their exact matrix rank for the successful field pair.

| $N$ | Base $\ell$ | Verified exponent | Proper divisor | Relations | Rank |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 77 | 29 | 480 | 7 | 134 | 43 |
| 143 | 19 | 720 | 11 | 59 | 35 |
| 221 | 3 | 1,728 | 13 | 98 | 45 |
| 10,001 | 17 | 4,896 | 137 | 42 | 32 |
| 10,203 | 11 | 6,408 | 19 | 48 | 35 |
| 24,997 | 17 | 8,568 | 3,571 | 48 | 41 |
| 15,251 | 3 | 475,200 | 151 | 65 | 46 |
| 10,403 | | | Unresolved | | |

For $10{,}001=73\cdot137$ and $15{,}251=101\cdot151$ the factor-base cutoff is below both prime factors. Joining equal residues also splits $10{,}403=101\cdot103$ with slopes $0,-1$. Its 271 relation columns have rank 37. The base is $7$, the verified exponent is $1{,}285{,}200$, and the gcd scan returns 103.

A separate fixed corpus takes every unordered pair of distinct primes in $[79,149]$, excluding the development input 10,403. At the same height 220, cutoff 71, and six slope pairs, the identical-mark search split **24 of 90** inputs. The residue join split **87 of 90**. Every returned divisor and modular power was checked. Prime labels enter only in the evaluation of the survey. The factoring routine takes $N$ and the search limits. At any subpower mark height and sufficiently large input, the direct residue join coincides with identical-mark matching. At height 220 this already holds when $\lfloor\sqrt N\rfloor\ge441$. [Collision bound and finite replay](quadratic-mark-collisions.md) The three unresolved inputs prevent an all-input claim for this schedule. The proof for high-degree fields uses a separate supply estimate. [Worst-case construction](cogentic-deterministic-two-thirds.md)

Run `gp -fq experiments/cogentic-quadratic-order.gp` for the development examples. In an interactive GP process set `cogentic_as_library=1` and read the script. Use `probe(N,220,71,1)` for the residue join and `probe(N,220,71)` for identical marks. A successful result gives the slopes, base, exponent, divisor, relation count and matrix rank. An empty vector records exhaustion. The full surveys are `survey(0)` and `survey(1)`; each reports the number tried, the number split and the sum of relation counts for the successful field pairs.

## Partial rational factorizations

A third mode uses prime valuations of the evaluated residue. Let $t=\min(y,N-y)>0$ for the unit label $y=a-bm\bmod N$. Strip every factor $p\le B$ to write $t=r\prod p^{e_p}$. For each smooth algebraic element $\alpha$ form a column with its algebraic ideal valuations and rational entries $-e_p$. If $r=1$, keep this column. Otherwise store the first column at $r$ and use differences to the other columns with this same $r$. The leftover $r$ can be composite. An exact rational target is now a single row for any $\ell\le B$ coprime to $N$, including inert primes or 2. No prescribed splitting type is needed.

If the retained matrix has a combination $Vz=k e_\ell$ with integers $k>0,z$, its algebraic products are units in the two fields, because both algebraic valuation vectors vanish. The choice of columns cancels every leftover integer $r$. Multiplying the corresponding modular equations, with signs killed by the twelfth powers, gives $\ell^{12k}\equiv1\pmod N$. Reversing the sign of $k$ only inverts a modular unit. The program verifies the power, checks the gcd chain, and returns only proper divisors. Rational and algebraic factor bases and elimination of shared cofactors occur in the number field sieve and its large-prime variants. Here the linear target yields an integer order multiple, using the finite unit groups of the two imaginary fields. [Buhler, Lenstra and Pomerance](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/1993_Book_TheDevelopmentOfTheNumberField.pdf) · [Lenstra and Manasse on partial relations](https://infoscience.epfl.ch/server/api/core/bitstreams/490ebcc2-36fb-4a5a-80fa-6a8e6f0831fe/content)

With the same height 220, cutoff 71 and six slope pairs the complete fixed surveys gave:

| Distinct primes in input | Inputs | Same mark | Equal residue | Partial rational factorization |
| --- | ---: | ---: | ---: | ---: |
| $[79,149]$, excluding development input 10,403 | 90 | 24 | 87 | 90 |
| $[443,487]$ | 28 | 0 | 0 | 28 |
| $[5003,5051]$ | 21 | 0 | 0 | 3 |

The last two equal-residue counts follow exactly from the [injectivity bound](quadratic-mark-collisions.md), since $m\ge441$. The other columns were run on all inputs. Across the largest set, slopes $0,-1$ yield $3^{340816272000}\equiv1\pmod{25070033}$. Its odd exponent part gives $3^{2662627125}\equiv6268760\pmod{25070033}$ and $\gcd(6268759,25070033)=5003$. The other successful inputs are 25,160,231 and 25,220,483. All 21 inputs use the same schedule. Coverage on this set was 3/21, so the small-corpus results alone provide little guidance about growth.

In GP use `probe(N,220,71,2)` for this mode. To reproduce a row use `survey(mode,lower,upper)`, with modes 0, 1 and 2 in table order. The simple equal-residue join and this rational-side construction both leave open a sufficient general supply of relations for these particular imaginary quadratic fields.
