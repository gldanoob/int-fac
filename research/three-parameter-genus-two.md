# Three coefficients suffice for a genus-two search at every prime

For **every fixed prime** $p$ and $Z\ge p$, let $m$ range over integers in $(Z,2Z]$, put $b=\lceil\log_2(2pZ+1)\rceil$ and $L=\log(2p)$. A deterministic algorithm given $N=pm$ alone returns a proper divisor or identifies a prime power. For any fixed positive integer $r$ its actual time satisfies
$$
   \big(\mathbb E_m T(pm)^r\big)^{1/r}
     \le b^{O_r(1)}\min\!\left\{\sqrt p,\ (1+p^{3r}/Z)^{1/r}
                       \exp(O_r(\sqrt{L\log(2L)}))\right\}.
$$
The same bound holds over the prime partners and over all partners for which $p$ is the least prime factor. For primes $m$ this gives complete factorization. In particular every $p$ has a square-root-exponent mean once $Z\ge p^3$. The bound uses the proved ordinary RH in Younis's smooth-number theorem and proved Dirichlet GRH for a polynomial list of quadratic characters. The classical estimates of Younis and the multiplicative large sieve also give the result with exponent $O_r(L^{2/3}(\log(2L))^{4/3})$. [Alpöge](https://alpo.ge/remark.pdf) · [Independent kernel verification](https://math.mit.edu/~drew/grh/) · [Younis, Theorems 1.1 and 1.3](https://arxiv.org/pdf/2409.05761)

## Translating and scaling a model

Use the [genus-two order count](quadratic-cubic-genus-two.md#uniform-supply-of-smooth-orders-of-twice-odd-size). For the smooth cutoff $Y$ at size $p$ it gives at least $p^5/E$ monic quintics with ordinary odd Frobenius trace and Jacobian order $2s$ for $s$ odd and $Y$-smooth, with $E=\exp(C L\log(2L)/\log Y)$ for a sufficiently large absolute $C$. Every such quintic factors uniquely into a monic irreducible quadratic and a monic irreducible cubic by the parity of rational two-torsion and trace. [Lenstra–Pila–Pomerance II, Proposition 2.4 and Theorem 1.1](https://people.maths.ox.ac.uk/pila/HyperII.pdf#page=8)

Translate to put the quadratic in the form $X^2-e$ and write the cubic as $X^3+b_1X^2+b_2X+b_3$. At most $p^4$ original monic pairs have $b_1=0$, counting even reducible polynomials. For every other pair substitute $X=b_1 x$ and divide the product by $b_1^5$. Its normalized factors are
$$
                    x^2-e',\qquad x^3+x^2+B x+C'.
$$
Store the original squareclass of $b_1^5$ as the successful twist sign, choosing one if both signs work. A normalized triple has at most $p(p-1)$ preimages, since translation and scaling determine the original monic model. Absorb fixed constants in $E$. We therefore have at least $p^3/E$ triples $(e',B,C')$ with a successful twist and $e'$ nonsquare. For readability write these coefficients as $(e,B,C)$ below.

## Conic marks independent of the cubic

Fix $f>1$ with $(f/p)=+1$. For a partner with another prime divisor $q\ne p$ we want $(f/q)=-1$. The verified Dirichlet GRH and the index-four least-prime-in-a-coset theorem give such a prime $f\ll b^2$ for every pair after small-factor trial. Alternatively use the [classical polynomial list with at most $O(\sqrt Z)$ exceptional whole partners](untwisted-legendre-partners.md#whole-integer-partners-and-rare-failure-of-the-conic-list). [Lamzouri–Li–Soundararajan, Theorem 1.4](https://arxiv.org/pdf/1309.3595#page=3)

The three public word coordinates will be $(A,B,C)$. For every $1\le v\le H=\lceil E^3\rceil$ try $e=A^2-fv^2$. For each $e$ this asks for a base point $(A,v)$ of the conic $a^2-fz^2=e$. The values $f v^2$ are distinct modulo $p$ when $p>2H$ and $f$ is a unit. The identity
$$
   \sum_{e\bmod p}\left|\sum_{v=1}^H\chi_p(e+fv^2)\right|^2=Hp-H^2
$$
shows that at most $O(p/H)$ values of $e$ lack any nonzero-square choice of $e+fv^2$. The character correlations are $p-1$ on the diagonal and $-1$ off it. If the positive sign is missing, at most one summand vanishes. Dropping these $e$ loses at most $O(p^3/H)$ normalized triples. For each remaining $e$, fix one base point analytically, independently of $B,C$.

Parametrize the conic by the line $z=v+t(a-A)$ through $(A,v)$. Its second intersection has
$$
          a=A+\frac{2(fvt-A)}{1-ft^2},\qquad z=v+t(a-A).
$$
Use $0\le t\le 4H+10$ and discard poles and branch values. For a nonsquare $e\ne0$ and a valid base point the map to $a$ is a nonconstant rational function of degree at most two. This follows also because any vertical fiber of this nonsingular conic has at most two points and every line through the base point specifies the residual point uniquely, including the tangent. At most two slopes are poles. At $p$ a finite point always has $a^2-e\ne0$. As $p>4H+11$, this supplies at least $H$ distinct $a$ modulo $p$. Bounds on the rational heights uniformly in $A$ are unnecessary. Every denominator is tested by gcd at the input modulus.

For fixed $e$ and $B$, the cardinality of the set of $a^3+a^2+Ba$ for these marks is at least $H/3$ because the polynomial is monic of degree three. Apply the same two-shift character identity in $C$ to a set of these distinct values. At most $O(p/H)$ coefficients $C$ fail to give both signs of $a^3+a^2+Ba+C$ among the marks. Losing these triples costs $O(p^3/H)$ in total. For each surviving good shape choose a mark with sign equal to the required twist. This decision occurs only in the proof.

Write $F(x)=(x^2-e)(x^3+x^2+Bx+C)$ and $d=F(a)$. The public curve $y^2=dF(x)$ has the rational point $(a,d)$. At $p$ the factor $a^2-e=fz^2$ is a nonzero square, so $d$ has the successful twist sign. The quadratic-factor Tate pairing on the marked class $[(a,d)-\infty]$ is $\chi_p(a^2-e)=+1$ on every twist, since the leading value at infinity of the quadratic function is a square. In a Jacobian of order $2s$ with $s$ odd, the marked class accordingly has odd smooth order. At $q$ its pairing is $-1$ whenever all values are units, forcing even order. Test the numerator of $z$, every denominator, the discriminant and the twist coefficient separately by gcd. If one of these is bad at $q$ and good at $p$, its gcd splits the input. On a smooth branch one can convert to a monic quintic $d^5 F(X/d)$ with point $(da,d^3)$ before the gcd-checked Cantor scalar multiplication. The odd scalar kills the class at $p$ and leaves a nonidentity class at $q$. [Frey–Rück](https://doi.org/10.2307/2153546) · [Pairing, local parameter at infinity and composite arithmetic](quadratic-cubic-genus-two.md#a-two-torsion-character-of-the-marked-point)

## Target size and the cost of selection

There are still at least $cp^3/E$ good normalized shapes for an absolute $c>0$. For the analytically assigned $(A_e,v_e)$ each shape supplies a successful word $(A_e,B,C)$. Any single word occurs through at most $H$ of the possible $v_e$, since $e=A_e^2-fv_e^2$. Thus the successful word density among the three field coordinates is at least $c/(EH)$. The binary cube whose three $k$-bit words range from zero through $2P-1$, for $P<p\le2P$ and $2^k=2P$, contains every field word and has at most eight times as many words. Its target is fixed at $p,f$, independently of the prime partner.

Use the [multiblock moment calculation](untwisted-legendre-partners.md#partner-bits-and-time-moments) with blocks of $3k$ bits. Each of the $r$ initial blocks is filled from the low bits of $\lfloor N/2^j\rfloor$ at the appropriate guessed shift. For $j=\lfloor\log_2p\rfloor$ this integer is injective as $m$ varies and each joint word occurs $O(1+Z/p^{3r})$ times. At stage $a$, each start receives the $4^a$ small-bias shifts separately, so the joint missed fraction is at most $((3k)^2 EH/(c4^a))^r$ for a given successful $f$. Take the union only over the polynomial public list of $f$. All $H(4H+11)$ base and slope tests for a word are included in its cost. Small primes and exact powers are handled first, and the factorial search gives the $\sqrt p\,\mathrm{poly}(b)$ cap. Guess $P$ by round robin, including trial cutoffs, scalar preparation and all arithmetic at each guess. The true guess's trial cutoff need only exceed $4H+11$ and the polynomial-height list of $f$. It costs $Y^{O(1)}b^{O(1)}$. The Cartesian-word estimate, all slow cases, and the two normalizations now give the displayed bound. Its classical version uses the same $O(\sqrt Z)$ exceptional-partner charge as the four-parameter proof.

As a further consequence, interleave the unrestricted deterministic benchmark algorithm. For $Z<p^{3r}$ the total input length is $O_r(L)$, while for $Z\ge p^{3r}$ the length factor in the new estimate is bounded. Thus for every fixed $p$ and every partner dyad the $r$-th root of the mean cost is at most $b^{O_r(1)}\exp(O_r(L/\sqrt{\log(2L)}))$. This least-prime-scale subexponential bound also holds on the whole-partner ensembles. The sharper square-root exponent in the long-partner range and the benchmark's worst-case exponent measure different input regimes. [Verified unrestricted algorithm](https://bigospeedrun.com/integer-factoring)

## Exact finite checks

Over the fields of sizes 5, 7 and 11, the normalized chart contained 260 marked twist choices with odd trace and Jacobian order twice an odd integer. Both signs occurred equally often. All 520 changes of affine coordinates preserved the independently computed Weil polynomial. In five more prime fields the replay checked 15,356 marks across the cubic fibers, including the two exact character-correlation identities. Thirteen locally smooth witnesses, six with negative twist, gave 120 composite gcd splits at nine first primes and nineteen partner primes. A separate run using only each input integer split all fifteen fixtures, nine during Cantor arithmetic. [PARI/GP replay](../experiments/three-parameter-genus-two.gp)
