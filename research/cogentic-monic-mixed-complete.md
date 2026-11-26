# Complete finite mixed-field square decisions

A prescribed finite library of fields with one common modular evaluation admits a deterministic decision for mixed primitive-grid relations. The decision includes independent field signs subject to even sign incidence. It either finds a proper divisor or proves that every exact square tuple in the chosen domain has a trivial modular sign. Dedekind GRH gives one-third time for the decision on the monic degree and height scales. [Complete two-field decision](cogentic-monic-complete-grid.md) · [Mixed incidence](cogentic-mixed-square-graphs.md)

## Finite signed domain and exact parity

Let $N>1$ be odd. Fix $r$ monic irreducible integer polynomials $P_i$ of degrees at least two, with field roots $\alpha_i$, for which $P_i(m)\equiv0\pmod N$ and $P_i'(m)$ is a unit modulo $N$. These assumptions give reductions from the rings of integers. Use the primitive grid $J=\{(a,b): |a|\le A,\ 1\le b\le A,\ \gcd(a,b)=1,\ \gcd(a-bm,N)=1\}$. For $j=(a,b)\in J$ put $u_{ij}=a-b\alpha_i$ and $s_j=a-bm\pmod N$. Add a coordinate $j=0$ with $u_{i0}=s_0=-1$ in each field.

A mask is an array $v=(v_{ij})\in\mathbb F_2^{r\times(J\cup\{0\})}$. In a connected graph, impose $\sum_i v_{ij}=0$ for every $j$, including $j=0$. These rows are exactly the image condition for oriented edge incidence. For each $j$ separately, route the required parity along a spanning tree by clearing leaves toward its root. For a disconnected graph, impose the sums separately on each component. With prescribed edges for a particular column, impose the sums on the components of that column's allowed graph. In all cases the local product is
\[
\beta_i(v)=\prod_{j\in J\cup\{0\}} u_{ij}^{v_{ij}},
\]
with each bit represented by zero or one. General integer incidence exponents reduce to these masks. Removing an even exponent multiplies the corresponding root by an explicit unit-reducible factor, so allowing integral exponents adds no new sign classes.

Construct exact ideal-parity rows in each field separately, using the cutoff $Y\ge\max(2A^2,2\max_i\deg P_i)$. At any prime ideal over $p>Y$, an odd valuation in one primitive direction forces that field's coordinate to zero, because two different directions would imply $p\mid ab'-a'b$, impossible for a nonzero determinant of absolute value at most $2A^2$. The exact collector tests the entire private residual, including singular primes, and retains all bounded ideal rows. Restore private failures as zero coordinates in their own field. Other fields may still use those directions where their own tests pass. Adjoin the sign coordinates with zero ideal rows, then stack the graph incidence rows. The resulting space $V_0$ is the full finite signed domain of even ideal parity. [Exact singular and private computations](cogentic-monic-singular-ideals.md#kernel-and-cost)

## Local rows and the exact stopping rule

At every odd simple residue root $x$ of $P_i$, use the leading-unit character $u\mapsto \left(\frac{p^{-v_p(u)}u\bmod p}{p}\right)$ in the local embedding. It is multiplicative and annihilates squares. Its primitive entries are computed from signed homogeneous norms and the derivative at $x$. Its only sign entry is in coordinate $(i,0)$ and equals $1_{p\equiv3\pmod4}$. The separate incidence row imposes the global sign parity. [Leading-unit formula](cogentic-monic-square-probes.md#leading-units-from-signed-norms)

For probe cutoffs $3,6,12,\ldots$, intersect the current space with the new rows. In each round test basis vectors for exact squarehood in every field. A verified square tuple can yield a split immediately. If a basis vector fails, increase the probe bound. In an all-square round the candidate space equals the exact square kernel $K$, because every probe annihilates $K$ and every basis vector is in $K$. An empty candidate basis is an all-square round. Exact square tests may be cached by the tested mask. A user-imposed query cap can interrupt the decision and is reported separately.

For unconditional termination, take a fixed $v\in V_0\setminus K$ and a field $K_i$ where $\beta_i(v)$ is nonsquare. In the quadratic extension $E=K_i(\sqrt{\beta_i(v)})$, the prime ideal theorem gives $2\psi_{K_i}(x)-\psi_E(x)=x+o(x)$. Terms at rational prime powers with exponent at least two contribute $O(\deg(P_i)\sqrt{x}\log x)$, and the finitely many rational primes dividing $2\operatorname{disc}(P_i)$ or ramified in $E$ can be excluded. The remaining weighted first-degree inert count grows without bound. At any such inert prime the simple-root leading-unit row detects $v$. The mask family is finite, so some finite doubling round reaches $K$. [Effective and unconditional prime-ideal count](cogentic-monic-complete-grid.md#termination-and-time)

## Normalization and signs

Put $\nu_j(v)=\sum_i v_{ij}$ as an ordinary integer, so every $\nu_j$ is even. A square mask provides roots $r_i(v)^2=\beta_i(v)$. These roots are algebraic integers and their reductions are defined by derivative clearing. Define
\[
 T(v)=\prod_{j\in J\cup\{0\}}s_j^{\nu_j(v)/2},
 \qquad z(v)=\frac{\prod_i\rho_i(r_i(v))}{T(v)}.
\]
The sign contribution in the denominator is $(-1)^{\nu_0/2}$. For an integer incidence lift $b$ of $v$, each coordinate satisfies $\sum_i b_{ij}=0$. Its root correction at vertex $i$ is $\prod_j u_{ij}^{(b_{ij}-v_{ij})/2}$; the total residue of these corrections is exactly $T(v)^{-1}$. The modular square check is $z(v)^2=1$. Equivalently compare $\prod_i\rho_i(r_i(v))$ to $T(v)$ by a difference gcd. Every modular factor used here is a unit.

Each field root can change by a sign, so the ratio defines a class modulo the two global signs. For masks $v,w\in K$ a valid root for their sum is
\[
 r_i(v+w)=\frac{r_i(v)r_i(w)}{\prod_j u_{ij}^{v_{ij}w_{ij}}}.
\]
The quotient is defined in the localization at the elements with unit residue. On each coordinate, including $j=0$, one has $\nu_j(v+w)=\nu_j(v)+\nu_j(w)-2\sum_i v_{ij}w_{ij}$. Thus the ratios of the overlap denominators are exactly canceled by $T(v+w)$, and the class of $z$ is a homomorphism. A nontrivial class gives a proper divisor of odd $N$, including for $N$ with repeated prime factors. Therefore all basis ratios being global signs certifies absence of splits throughout $K$. For certification without repeating the search, the influential probe roots and a full-dimensional intersection basis with exact field roots suffice after exact parity reconstruction. [Basis certificate principle](cogentic-monic-complete-grid.md#replaying-an-exact-no-split-certificate)

## Conditional time and implementation

Assume GRH for the zeta functions of the fixed fields and the quadratic extensions from nonsquare vertex products of $V_0$. Each product has even ideal valuations, so the relative discriminant of its quadratic extension divides $4\mathcal O_{K_i}$. The [parity-even cutoff](cogentic-monic-square-probes.md#adaptive-stopping-and-the-parity-even-cutoff) is polynomial in the field degrees and defining coefficient bit lengths. It separates every nonsquare vertex product by a degree-one character below that cutoff, without a factorization of any marked norm. The doubling procedure stops in $O(\log\log N)$ rounds bound by this cutoff when all degrees and coefficient bit lengths are polynomial in $\log N$.

For a fixed number of fields, $A,Y\le\exp(O(W))$ with $W=(\log N)^{1/3}(\log\log N)^{2/3}$ give $\exp(O(W))$ exact ideal and probe work, by the per-field bound. Each tested field product starts from its mask and uses each marked element at most once. Its explicit bit length is $O(A^2\operatorname{poly}(\log N))$. The exact test, derivative clearing and modular operations are polynomial in that size. At most the finite domain dimension worth of masks is tested per round, giving total $\exp(O(W))$ conditional bit cost. The bound decides the relation question for the specified fields and grid. Finding a library with a productive relation for every surviving input remains a separate problem.

The separate [complete replay](../experiments/cogentic-monic-mixed-complete.py) accepts any fixed number of monic Eisenstein fields through its importable connected-domain search. It uses the exact SageMath collector and existing dyadic roots. The CLI uses the scheduled trio $F,G,G+4(X-m)$. A nonunit common derivative is reported before relations are tested. Running without an input checks the following fixtures.

| Input | Grid height | Ideal dimension | Exact square-basis dimension | Result |
| ---: | ---: | ---: | ---: | :--- |
| 895 | 20 | 18 | 13 | Split $179\cdot5$ |
| 247 | 2 | 2 | 0 | Complete no-split decision |
| 65 | 1 | 2 | 1 | Split $13\cdot5$ with signs $(-1,-1,+1)$ |

The first two rows use the scheduled trio. The positive witness at 895 uses two of its fields and the full basis is computed across all three. The signed fixture uses $m=9$ and $(X-1)^2+1$, $(X+9)^2+1$, $X^2+6X-70$. Its support has no marked points. Two roots of $-1$ reduce to $57$ and $18$, the third root is one, and $T=-1\pmod{65}$. The resulting ratio is 14. A further four-field check selects $(3,2)$ four times and verifies the exponent two in $T$. The [earlier bounded search](cogentic-monic-mixed-grid.md) remains separate and uses its original conservative settings.

Run in a Python environment with SageMath installed.

```sh
python3 -B experiments/cogentic-monic-mixed-complete.py
python3 -B experiments/cogentic-monic-mixed-complete.py 895 --height 20 --basis
```
