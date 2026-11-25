# The antipodal cube cannot improve the half exponent in any number of axes

Fix an integer $d\ge2$, put $m=2^{d-1}$ and place one terminal at each vertex of the binary $d$-cube. The tensor $E_D$ connects each opposite pair by an independent equality wire on $D\ge2$ labels. For any finite exact decomposition $E_D=\sum_i T_i$ over any field, let $R_{ia}$ be the matrix rank of the nonzero piece $T_i$ across the two halves of axis $a$. For all weights $\alpha_a\ge0$ with $\sum_a\alpha_a=1$,
$$
         \boxed{\quad\sum_i\prod_{a=1}^d R_{ia}^{\alpha_a}
                       \ \ge\ D^{m\|\alpha\|_2}.\quad}                       \tag{1}
$$
In particular the geometric-mean score used by the upstream finite-seed criterion is at least $D^{m/\sqrt d}$. The inequality is strict at equal weights when $d$ is nonsquare, since the left side is algebraic and the right side is transcendental by Gelfond–Schneider. The bound holds at every finite dimension and also for polynomial degenerations. These deductions use the joint convexity of the Euclidean price in OpenAI's November 24 theorem. [Primary tensor-price theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/build/hilbert.tex#L10-L18) · [Exact upstream seed score, §6](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/multiaxis-type-amplification.md#6-a-sharper-test-for-one-finite-seed) · [Gelfond's theorem](https://www.mathnet.ru/eng/im4924)

For $D=2^\lambda$ and $M$ pieces, (1) gives
$$
 \max_i \sum_a \log_2 R_{ia}
      \ \ge\ d\big(m\lambda/\sqrt d-\log_2 M\big).
$$
Thus any fixed-axis family satisfying the upstream width cap $dm\rho\lambda+o(\lambda)$ with $\log M=o(\lambda)$ has $\rho\ge1/\sqrt d$. Its transfer formula $\log_d(1/\rho)$ can certify at most $1/2$. This applies equally to the three-axis construction and the proposed nine-axis improvement. At nine axes, $\rho=8/25$ needs $\log_2 M\ge256\lambda/75-o(\lambda)$. The conclusion concerns the exact endpoint and these common axis factorizations. The unrestricted deterministic factoring problem remains open. [Three-axis transfer](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/cube-crossing-transfer.md) · [All fixed axes and relaxed piece count, §§1 and 5](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/multiaxis-cube-transfer.md)

## One spectral inequality for every piece

Take positive side lengths $a_1,\ldots,a_d$ and the orthogonal box of corners $x_v=(a_1v_1,\ldots,a_dv_d)$ for $v\in\{0,1\}^d$. Its normalized Gaussian mean width is $W=\sum_a a_a$. The maximum of $\langle g,x_v\rangle$ over the box is $\sum_a a_a\max(0,g_a)$ and $\sqrt{2\pi}\,\mathbb E\max(0,g_a)=1$. A fixed spectral point $F$ on these corners satisfies $W\log_2 F(T)=H(T;x)$, where $H$ is the compatible Euclidean tensor price. At distinct corners all the original terminal spaces are separate. [Spectral point and shared-label formula](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/build/intro.tex#L21-L52)

The placement $x$ is the sum of its $d$ coordinate placements. At placement $a$ all the legs on each side of that axis coincide. The resulting two-site tensor of matrix rank $R_a$ is mutually restrictable with an equality wire of dimension $R_a$ by matrix rank factorization, so its price is exactly $a_a\log_2 R_a$. For a fixed nonzero tensor the price is a seminorm of the placement. Its triangle inequality therefore gives the single-piece bound
$$
        F(T)\le\prod_a R_a(T)^{a_a/W}.
$$
The ordinary sum is a restriction of the direct sum and $F$ is additive on direct sums. Hence $F(E_D)\le\sum_i F(T_i)$. Each antipodal wire costs $\sqrt{\sum_a a_a^2}\log_2 D$ and their prices add under tensor product. Exponentiating gives (1) for $\alpha_a=a_a/W$. Weights equal to zero follow by continuity of the explicit final inequality. The same proof permits a different label count for each opposite pair, replacing $D^m$ by the product of the counts. [Seminorm, grouping coincident legs and two-site prices](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/build/hilbert.tex#L85-L115) · [Ordinary-sum inequality](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/build/intro.tex#L101-L116)

## A leading coefficient or a shared product residue

Suppose the pieces depend rationally on an indeterminate $t$ and their sum has leading coefficient a nonzero scalar multiple of the crossing at some order. Compute their axis ranks over the rational function field. Clearing common denominators makes the pieces polynomial with unchanged generic ranks and preserves the leading coefficient up to a scalar. Write $h$ for its new order and $J$ for a bound on the polynomial degrees. In the $n$th tensor power the coefficient at $t^{nh}$ recovers the crossing on $D^n$ labels. Interpolate from $nJ+1$ distinct values in a sufficiently large extension field. Specialized ranks cannot exceed generic ranks because the larger minors vanish identically. For each evaluation expand the tensor power into piece products; ranks multiply. Apply (1) over the extension field to the resulting ordinary sum. It gives
$$
 D^{nm\|\alpha\|_2}\le(nJ+1)\left(\sum_i\prod_a R_{ia}^{\alpha_a}\right)^n.
$$
Taking $n$th roots proves (1) for the original rational pieces, with no degree term in the result. This argument uses the vanishing of all coefficients below the extracted crossing. [Interpolation in tensor degeneration](https://doi.org/10.1137/0209053)

At four terminals a direct sum of same-size crossings is exactly $\Delta_K\otimes E_D$ for $K$ summands, where $\Delta_K$ shares one label at all four sites. Additivity of $F$ gives the stronger finite bound
$$
      \sum_i\sqrt{R_{i1}R_{i2}}\ge K D^{\sqrt2}.
$$
It applies to the odd-operand crossing constrained by $xy\equiv N\pmod{2^w}$, with $K=2^{w-1}$ and $D=2^{\lambda-w}$. Its log score is therefore at least $(w-1)+\sqrt2(\lambda-w)$. The existing modular upper construction has this same leading per-piece width after adding the polynomial count of pieces, up to $O_p(\sqrt{\lambda-w}+\log(\lambda+2))$ in the log score for fixed coefficient prime $p$. For heterogeneous direct-sum blocks of square crossings of sizes $D_j$ the lower bound is $\sum_j D_j^{\sqrt2}$, by the same additivity. [Operand relabeling, arithmetic tensor and upper construction](modular-product-crossings.md#a-shared-residue-gives-a-smaller-exact-crossing)

## When only one cut is specified for each piece

Suppose $E_D$ is a sum of tensors each given at one specified axis. Group terms using the same axis. Let $R_a$ be the rank of the group at axis $a$ and write $X_a=\log_2 R_a$ for nonzero groups, using zero at an absent group. Put $L=\log_2 D$. Then
$$
       \|(X_1,\ldots,X_d)\|_2
       \ge mL-\sqrt{2d\sqrt d\,mL\log_2 d}.
$$
For a proof, assume the norm is below $mL$. Choose $\delta>0$ such that $u_a=(X_a+\delta)/(mL)$ has $\sum u_a^2=1$. Place terminals at $(\pm u_1,\ldots,\pm u_d)$, so the target costs $2mL$ and the mean width is $2\sum u_a\le2\sqrt d$. At the chosen axis of a group, factor it into two tensors at $\pm t e_a$ with an internal channel of rank $R_a$. Each external wire carries the alphabet of dimension $D$ a distance $\sqrt{1-2tu_a+t^2}\le1-tu_a+t^2/2$. A contraction then gives a price at most $2mL-2t\delta+mLt^2$. Summing at most $d$ groups costs at most $2\sqrt d\log_2 d$ beyond this price. Take $t=\delta/(mL)$, and use the triangle inequality $mL\le\|X\|_2+\sqrt d\,\delta$. In particular, a decomposition into terms of rank one at any of the $d$ specified axes needs at least $D^{m/\sqrt d-O_d(1/\sqrt L)}$ terms. This extends the [two-cut partition-rank bound](euclidean-crossing-barrier.md#asymmetric-two-piece-partitions) to the full family of antipodal cubes.

## Plane factorizations on a whole grid

Let the $g^d$ sites of a complete graph carry independent $D$-dimensional wires on all its edges. A piece may have an arbitrary tensor-network presentation after merging each of the $g$ parallel planes along axis $a$. Let $C_{ia}$ be the sum of the bit widths of all interplane wires in that presentation. For each piece assume such a presentation is available at every axis. It may couple different coordinate cubes. With $M$ pieces one has
$$
 \max_i\sum_a C_{ia}\ \ge L\sum_{\{v,w\}\subset[g]^d}\sqrt{\#\{a:v_a\ne w_a\}}
       -d\sqrt{2\pi\log g}\,\log_2 M .                                  \tag{2}
$$
The inner count in the first sum is the Hamming distance of the two grid vertices. The logarithm inside the square root is natural.

Represent each of the $g$ levels by $e_j/\sqrt2$ in its own axis subspace. In a single coordinate placement every interplane wire has length one, so the presentation bounds the price by $C_{ia}$. In the product placement the Euclidean distance of two grid sites is the square root of their Hamming distance. The support's normalized mean width is $d\sqrt\pi\,\mathbb E\max_{j\le g}G_j$ for independent standard normals $G_j$, by taking the maximum in each coordinate separately. The Gaussian exponential-moment bound gives $\mathbb E\max_jG_j\le\sqrt{2\log g}$. The seminorm and ordinary-sum rules now prove (2). In particular a fraction $g^d(g-1)^d/[g^d(g^d-1)]=(1-o_g(1))$ of edges differ in all $d$ coordinates for fixed $d$. If $\log M=o(Lg^{2d}/\sqrt{\log g})$, the maximum average over the $d$ axis costs is at least $(1/\sqrt d-o_g(1))L\binom{g^d}{2}$. This rules out a better common sum-of-widths guarantee even for coupled global decompositions in this regime. Inequality (2) controls that sum; choosing a single inexpensive plane layout for each term is a different criterion. [Plane transfer and interplane widths](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/multiaxis-cube-transfer.md#2-partition-all-generic-edges-into-antipodal-cubes)

## Finite controls

The replay checks 30 weighted rank inequalities over three finite fields, including two direct sums with a shared residue. It computes axis ranks by exact matrix elimination and uses integer roots to compare the two sides. A separate interpolation reconstructs all 65,536 entries of a tensor square with a strictly higher-order error, and direct grid enumeration checks 592,232 edge distances. The general result is the deduction from the cited tensor-price theorem. [Executable checks](../experiments/multiaxis-crossing-barrier.py)
