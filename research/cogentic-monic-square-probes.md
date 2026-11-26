# Exact local probes before joint square testing

A small-prime prefilter can remove nonsquare classes from the signed ideal-parity kernel before exact square testing. It handles probes at good primes that divide retained marked norms. The test at such a prime uses the Legendre symbol of the leading local unit of the mark. Every probe annihilates the true joint square kernel unconditionally. Remaining masks still go to the exact square oracle.

## Leading units from signed norms

Let $P\in\mathbb Z[X]$ be monic irreducible of degree $d\ge2$ and let $p$ be an odd prime coprime to the defining discriminant. Each residue root $r$ is simple, lifts by Hensel to $\alpha_r\in\mathbb Z_p$, and defines an embedding $\mathbb Q(\alpha)\to\mathbb Q_p$. For $z\ne0$ the function
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

The importable function prefilter(fields, points, signed_parity_basis, discriminant, *, prime_cutoff=257) takes ascending polynomial coefficients, $(a,b)$ pairs, and support masks whose bit just above the final mark is the shared sign. The supplied nonzero discriminant product must be a multiple of every defining discriminant. The return value consists of surviving original masks and the probe counts and projected rank. It precomputes the signed homogeneous norms, enumerates roots by modular Horner evaluation, reuses the existing binary elimination, and neither factors the norms nor computes a maximal order. A rational prime can contribute separate rows for different fields or roots. The cost is polynomial in the cutoff and in the binary description of the fields, marks and parity basis. The cutoff is a fixed practical choice. Completeness at a larger prescribed cutoff requires a separate result. [Conditional complete character cutoff](cogentic-monic-squareclass-cutoff.md)

## Finite replay

Run the [Python replay](../experiments/cogentic-monic-square-probes.py). The fixed tests use primitive marks of height $64$, full parity cutoff $8192$, and the [ramified ideal row at two](cogentic-monic-ramified-two.md). The character enumeration uses odd primes through $257$ coprime to the common product of defining discriminants. This crosses the grid's in-base bound $151$. A second pass through $151$ reaches the same projected ranks on these four cases. The three raw pairs use the existing common-root check or repair, with manual degrees $2,3,3$ respectively. The norm-two fixture uses parameter $4$ at $85$. A separate regression over $\mathbb Q(\sqrt2)$ at $p=7$ checks previously vanishing marks with valuations one and two, a rational $p$ factor, and the signed norm $-49$.

| Input | Marks | Signed parity dimension | Probe roots | Roots with a nonunit column | Surviving dimension | Exact tests | Verified square basis vectors | Proper gcd |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 27 | 2068 | 715 | 97 | 95 | 712 | 128, query cap | 128 | |
| 323 | 916 | 8 | 95 | 91 | 5 | 5 | 5 | 19 |
| 247 | 692 | 2 | 103 | 99 | 1 | 1 | 1 | 19 |
| 85, planted | 38 | 2 | 85 | 50 | 0 | 0 | 0 | |

The replay verifies every returned congruence of squares and takes the gcd of the root difference with the input. In the augmented raw $323$ fixture the basis alone splits the input without a unit correction. At $27$ it checks 128 square vectors before the query cap, so it gives a partial exact basis and does not certify the full square-kernel dimension. Most rows in the raw cases have a nonunit somewhere among the retained marks. Requiring every mark to be a unit at its probe root would leave at most $2$, $4$, and $4$ rows respectively, even before any global norm-prime exclusion. The observed ranks are finite measurements, and no uniform rank claim is made for the cutoff $257$.
