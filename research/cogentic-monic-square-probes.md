# Exact local probes before joint square testing

A small-prime prefilter can remove nonsquare classes from the signed ideal-parity kernel before exact square testing. It handles probes at good primes that divide retained marked norms. The test at such a prime uses the Legendre symbol of the leading local unit of the mark. Every probe annihilates the true joint square kernel unconditionally. Remaining masks still go to the exact square oracle.

## Leading units from signed norms

Let $P\in\mathbb Z[X]$ be monic irreducible of degree $d\ge2$ and let $p$ be odd. Every simple residue root $r$ lifts by Hensel to $\alpha_r\in\mathbb Z_p$ and defines an embedding $\mathbb Q(\alpha)\to\mathbb Q_p$. Simplicity at that root is sufficient even if another root is repeated modulo $p$. For $z\ne0$ the function
\[
        z\longmapsto \left(\frac{p^{-v_p(z)}z\bmod p}{p}\right)
\]
is multiplicative and sends every square to $+1$. Here $z$ and the valuation are taken in this embedding. For a shared sign coordinate use the same function on $-1$ in each field, giving the bit $1_{p\equiv3\pmod4}$.

At a mark $z=a-b\alpha_r$, evaluate $a-br\bmod p$ directly when nonzero. If it vanishes and $(a,b)$ is primitive, then $p\nmid b$. Put $H=b^dP(a/b)$, the signed homogeneous norm. Over $\mathbb Q_p$ write $P(T)=(T-\alpha_r)g(T)$. Then
\[
         H=b^{d-1}z\,g(a/b),\qquad g(a/b)\equiv P'(r)\not\equiv0\pmod p.
\]
Thus $v_p(H)=v_p(z)$ and the residue used in the symbol is
\[
                (H/p^{v_p(H)})\, b^{1-d}/P'(r)\pmod p.
\]
This only requires the signed norm, repeated division by $p$, and inverses modulo $p$. The implementation first strips any common $p$-power from $a,b$ and retains the formula if the resulting residue is still zero. Removing rational $p$-powers leaves the leading unit unchanged, and the corresponding factor $p^{d}$ per power likewise disappears during the division of the norm. For $b=0$ the direct unit case applies after stripping, with homogeneous norm $a^d$.

## Projection and exact use

At each root make one bit row on all marks plus the single shared sign bit. For a signed parity basis $v_1,\ldots,v_J$, project a row $h$ by taking the $J$ binary dot products $h\cdot v_j$. Find the kernel of the projected rows and express its basis as XORs of the original basis masks. This gives the exact intersection of the signed parity space with the kernels of the tested local characters. Every true signed square relation remains in the intersection, and an empty intersection certifies that no such relation exists. The intersection can be larger than the square kernel. Exact tests of basis elements together with [adaptive class processing](cogentic-adaptive-square-kernel.md) are still needed to extract every square dependency.

The importable function prefilter takes ascending polynomial coefficients, $(a,b)$ pairs, and support masks whose bit just above the final mark is the shared sign. With the optional discriminant set to None, it accepts exactly the roots for which the modular derivative is nonzero. A supplied nonzero integer can exclude primes by simple remainder tests. The return value consists of surviving original masks, probe counts, projected rank, last tested prime and stop reason. It precomputes the signed homogeneous norms and enumerates roots by modular Horner evaluation. It neither factors the norms nor computes a maximal order. A rational prime can contribute separate rows for different fields or roots.

## Adaptive stopping and the parity-even cutoff

Enumerate increasing rational primes in doubling sieve blocks up to the requested cutoff. At a new root, test its row on the current basis. If all results are zero, keep the basis. Otherwise remove the first basis mask of odd row value and XOR it into every remaining odd mask. The new masks span exactly the intersection with that row's kernel. Each informative row reduces the dimension by one, and each redundant row leaves it unchanged. Sieve work and memory depend on the largest block reached. Root scanning, exact local rows and elimination cost polynomial time in that prime bound and in the input description.

The function stops as soon as the surviving dimension is at most its requested survivor_limit, which defaults to zero. Zero survivors prove that the signed joint square kernel is trivial. If an earlier exact search already produced $s$ independent certified square masks, reaching dimension $s$ proves that those masks span the full kernel. With no prior lower bound, a handoff limit $k$ instead guarantees that the exact fallback takes at most $1+2+\dots+2^{k-1}=2^k-1$ joint square tests using independent pivots. A run reaching only the prime cutoff has an exact filtered space and still needs that fallback. Rank stagnation alone gives no certified stopping rule.

A uniform cutoff much smaller than the one for arbitrary products is available under the same Dedekind GRH when the input space has exact even ideal parity. In one field let $\beta$ be any nonzero nonsquare signed product in that space and put $E=K(\sqrt\beta)$. At every finite prime $\mathfrak p$ write $\beta=\pi^{2h}u$ locally with $\pi$ a uniformizer and $u$ a unit. The discriminant of the local quadratic order given by $T^2-u$ is $4u$. Hence the relative field discriminant divides $4\mathcal O_K$, and
\[
          \log|\Delta_E|\le 2\log|\Delta_K|+d\log4 .
\]
At an odd prime the extension is unramified, and its inertness at a degree-one prime is exactly the nontrivial leading-unit character of $\beta$, including when an individual mark is not a unit. This removes the marked norms from the discriminant size bound and from the prime exclusions.

In the [prime-ideal count from $2\psi_K-\psi_E$](cogentic-monic-squareclass-cutoff.md#uniform-quadratic-discriminant-and-inert-prime-count) take the only excluded rational primes to be those dividing $2\prod_i|\operatorname{disc}(P_i)|$. Its proof works with $M$ replaced by $10+\sum_i(d_i+D_i)$, where $D_i$ bounds the bit length of each polynomial discriminant. The implementation parity_probe_cutoff computes these bounds from coefficient heights alone. With $H_i=\max(2,\lVert P_i\rVert_\infty)$, the Sylvester row norm bound gives
\[
       |\operatorname{disc}(P_i)|
          \le ((d_i+1)H_i)^{d_i-1}(d_i^2H_i)^{d_i}.
\]
This supplies $D_i$ by bounding each factor with a power of two using integer bit lengths. At $X=(10^6M\lceil\log_2(2M)\rceil^2)^2$ every nonsquare parity-even mask is detected in at least one field, assuming the Dedekind GRH used in that count. No discriminant needs to be constructed or factored. Passing None scans a superset of the primes counted by the proof and uses modular derivatives to select simple roots. A supplied exact product of defining discriminants also works. Extra exclusions require their own bit budget in $M$.

On the monic schedule the degree times the coefficient bit length is $O(\log N)$, so this cutoff is polynomial in $\log N$, independently of the number of marked norms. Only the generation and root scanning of the rational probe primes has this polynomial dependence. Computing and projecting their rows still depends on the marked input length.

## Finite replay

Run the [Python replay](../experiments/cogentic-monic-square-probes.py). The fixed tests use primitive marks of height $64$, full parity cutoff $8192$, and the [ramified ideal row at two](cogentic-monic-ramified-two.md). The character enumeration uses odd primes through $257$ coprime to the common product of defining discriminants. This crosses the grid's in-base bound $151$. A second pass through $151$ reaches the same projected ranks on these four cases. The three raw pairs use the existing common-root check or repair, with manual degrees $2,3,3$ respectively. The norm-two fixture uses parameter $4$ at $85$. A separate regression over $\mathbb Q(\sqrt2)$ at $p=7$ checks previously vanishing marks with valuations one and two, a rational $p$ factor, and the signed norm $-49$. An Eisenstein cubic at $5$ verifies the simple-root test alongside a repeated root and stops at $5$ even with the larger theoretical cutoff.

| Input | Marks | Signed parity dimension | Probe roots | Roots with a nonunit column | Surviving dimension | Exact tests | Verified square basis vectors | Proper gcd |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 27 | 2068 | 715 | 97 | 95 | 712 | 128, query cap | 128 | |
| 323 | 916 | 8 | 95 | 91 | 5 | 5 | 5 | 19 |
| 247 | 692 | 2 | 103 | 99 | 1 | 1 | 1 | 19 |
| 85, planted | 38 | 2 | 3 | 1 | 0 | 0 | 0 | |

The replay verifies every returned congruence of squares and takes the gcd of the root difference with the input. In the augmented raw $323$ fixture the basis alone splits the input without a unit correction. Setting the exact fallback handoff dimension to five for $323$ and one for $247$ reaches the same respective filtered spaces at $p=7$. The planted $85$ case certifies an empty kernel at $p=7$ without calling the exact oracle. At $27$ it checks 128 square vectors before the query cap, so it gives a partial exact basis and does not certify the full square-kernel dimension. Most rows in the raw cases have a nonunit somewhere among the retained marks. Requiring every mark to be a unit at its probe root would leave at most $2$, $4$, and $4$ rows respectively, even before any global norm-prime exclusion. The observed ranks are finite measurements.
