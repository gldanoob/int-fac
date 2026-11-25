# Nested rectangular flags for the crossing tensor

Let `E(x,y,u,v)=[x=v][y=u]` on an alphabet of size `d`. For every exact decomposition `E=Σ A_i` over a field, let `r_i,c_i` be the ranks in the cuts `xy|uv` and `xu|yv`. Discard zero pieces and put `k=#pieces` and `S=Σ√(r_i c_i)`. The following bounds hold over every field, with natural logarithms.

\[
 S\ge 2d\log d-d+2,\qquad S\ge(d-1)d^{1/k},\qquad
 S>d^{\sqrt2}\quad(2\le d\le324).
\]

The strict inequality also holds in every dimension for `k≤2`. The unrestricted asymptotic bound doubles the leading constant of the upstream harmonic bound. The exact finite range concerns the sufficient crossing-seed test of issue 52. The deterministic factoring exponent stays at `1/2`. [Upstream finite-seed criterion](https://github.com/1337isnot1337/integer-factoring/issues/52) · [Previous all-field cutoff through 97](https://github.com/1337isnot1337/integer-factoring/blob/1b33192/research/compatible-compression-budget.md) · [Previous harmonic bound](https://github.com/1337isnot1337/integer-factoring/blob/1b33192/research/weighted-cut-rank-budget.md)

## A triangular minor adds all the flag levels

Write the row matrix of a column-rank-`m` tensor `B` as `Σ P_h⊗Q_h`. Take an input basis `e_1,…,e_d` for the first leg and an output basis `f_1,…,f_d` for the first leg. Suppose `P_h e_j` belongs to `span(f_1,…,f_{w_j})` for every `h,j`, where `0≤w_1≤…≤w_d≤d`. Use the same bases in reverse roles on the second legs, so swap sends `e_j⊗f_t` to `f_t⊗e_j`.

Retain input columns `e_j⊗f_t` with `t>w_j` and the corresponding swapped output rows. Order the retained pairs by `j`. In a row belonging to `j`, all product terms vanish on columns of index `i≤j`, since their first output lies in `span(f_1,…,f_{w_i})`. The swap contributes the identity. The square minor is block upper triangular with identity diagonal. Consequently

\[
 r(E-B)\ \ge\ \sum_{j=1}^d(d-w_j).
\tag{1}
\]

For matching input and output block widths this recovers the upstream block-flag argument. Unequal widths and multiple nested quotient steps are central here. [Upstream block-flag theorem](https://github.com/1337isnot1337/integer-factoring/blob/1b33192/research/two-product-complement.md)

## Two elementary flags in opposite directions

Set `h=⌊d/(m+1)⌋`. Choose arbitrary successive input lines for the first `h` columns. Enlarge the image of their prefixes to nested output spaces of dimensions `mj` for `j≤h`. The first part of (1) gives `Σ_{j=1}^h(d−mj)`.

The induced maps on the remaining quotients have source dimension `a=d−h≥mh` and target dimension `b=d−mh≥h`. Choose `h` successive lines in the **dual target**. The images of each prefix under the `m` transpose maps fit in a nested space of dimension `mj` in the dual source. Passing to annihilators orders these constraints from the last output coordinate backwards. The `j`th terminal output coordinate vanishes on at least `a−mj` initial columns of the residual source. Each such cell adds a position to the same triangular minor, in columns distinct from the first `h`. This gives

\[
 r(E-B)\ge 2dh-(m+1)h^2-mh\ge \frac{d^2}{m+1}-d.
\tag{2}
\]

Indeed write `d=(m+1)h+e`, with `0≤e≤m`. The difference from `d²/(m+1)` is `mh+e²/(m+1)≤d`. If `h=0` the right-hand side of (2) is nonpositive. This proof uses bases over the given field throughout.

## Integrating all weighted cuts

Let `F(m)` be any nonincreasing universal lower bound for `r(E−B)` when `c(B)≤m`, with `F(0)=d²`. For `t≥0` define `G(t)=min_{m≥0}(F(m)+tm)`. For any subset of pieces, the sum of its column ranks and the sum of the complementary row ranks obey the same bound by rank subadditivity. Taking the subset with `tc_i<r_i` gives

\[
 \sum_i\min(r_i,t c_i)\ge G(t).
\]

Exchanging `y,u` fixes `E` and establishes the other orientation. Direct integration gives `4√(rc)=∫₀^∞ min(r,t c)t^{-3/2}dt`. Substitute `t↦1/t` on `[0,1]` and sum the two orientations to obtain

\[
 S\ge\tfrac12\int_1^\infty G(t)t^{-3/2}\,dt.\tag{3}
\]

By (2) and arithmetic-geometric mean, `G(t)≥2d√t−t−d`. For `t≥d²`, the choice `m=0` attains `G(t)=d²` for any nonnegative table `F`. Integrating these bounds on `[1,d²]` and `[d²,∞)` gives `S≥2d log d−d+2`.

For the piece-count bound put `z_i=log(r_i/c_i)/2` and `w_i=√(r_i c_i)`. For every `0≤v≤log d`, divide the budget at `t=exp(2v)` by `exp(v)`. Since `s+d/s≤d+1` for `1≤s≤d`, the result is `Σ w_i exp(−|v−z_i|)≥d−1`. The exchanged orientation covers negative `v`. Every point of `[−log d,log d]` must therefore lie within `log(S/(d−1))` of one of the `k` centers `z_i`. The combined length of their intervals gives `S≥(d−1)d^{1/k}`. For `k≤2` and `d≥8`, `d^{3/2−√2}≥d^{1/12}>d/(d−1)` since `√2<17/12` and `8·7^{12}>8^{12}`. The finite certificate covers the smaller dimensions.

## A stronger flag from a determinantal variety

At any quotient layer let `a,b` be the remaining source and target dimensions. Work over an algebraic closure, which preserves all matrix ranks. Among vectors `z` in the source, the `b`-by-`m` matrix with columns `P_1 z,…,P_m z` depends linearly on `z`. Choose the least `r∈[0,min(b,m)]` with

\[
 (m-r)(b-r)<a.\tag{4}
\]

A common kernel immediately supplies a source line of image rank zero. Otherwise the image of this linear matrix map has projective dimension `a−1`. The projective variety of matrices of rank at most `r` has codimension `(m−r)(b−r)`, so the projective dimension theorem gives an intersection when (4) holds. In the case `r=0`, condition (4) forces a common kernel by linear algebra. The determinantal codimension also follows by counting the rank-`r` matrix charts. [Harris, Algebraic Geometry, Lecture 12](https://www.cse.iitb.ac.in/~sohoni/CS782/Harris_AlgebraicGeometry.pdf) · [Projective dimension theorem](https://people.maths.bris.ac.uk/~malab/PDFs/Algebraic%20Geometry%20L13.pdf)

Choose the line and pad its images to `r` target dimensions. It contributes `b−r` cells to (1). Repeat on the quotient of dimensions `(a−1,b−r)`. Starting with `(d,d)` gives a certified integer table `F_d(m)`. Appending zero maps shows that its entry at `m` applies to every `B` of column rank at most `m`, irrespective of the actual rank. For the integrated bound it suffices to minimize over `0≤m≤2d−1`, since `F_d(2d−1)=0` and all entries are nonnegative. This argument replaces instance-specific Jacobian certificates with successive line intersections.

The breakpoints of `G(t)` come from consecutive vertices `(u,y),(v,z)` on the lower convex hull of `(m,F_d(m))`. When `t=(y−z)/(v−u)≥1`, the switch contributes `2√((v−u)(y−z))` to (3). Choose the last vertex `(m_0,f_0)` reached by traversing these edges in order of increasing `m`, including slope `−1`. The remaining boundary term is `f_0−m_0`. This follows by putting `x=√t` and integrating `F(m)/x²+m` on each hull interval.

The [checker](../experiments/nested-crossing-flags.py) encloses each radical by integer square roots and uses the upper Pell approximation `577/408>√2`. For each of the 323 dimensions from 2 through 324 it verifies strict separation. The certified lower bound at 324 is `3551.9177652`. At 325 the same integral is at most `3564.8974516<325^{1393/985}<325^{√2}`. This last inequality measures the reach of the calculated lower bound. The checker also tests all 65,536 binary tensors of dimension two and 89 literal triangular submatrices in characteristics 2, 3, and 5. Run `python experiments/nested-crossing-flags.py`.

## Why flag area alone cannot give a universal power improvement

For a fixed Ferrers-shaped set of `A` zero cells, changing both complete flags uses at most `d(d−1)` parameters. In adapted bases each of `m` matrices must vanish at those `A` cells, imposing `mA` independent linear conditions. The incidence variety of flags and matrix tuples therefore has dimension at most `md²−mA+d(d−1)`. There are finitely many flag shapes. Over an algebraically closed field a general tuple can have no such shape with `mA>d(d−1)`. Thus any rank bound furnished solely by a universal area in (1) is at most `d(d−1)/m` for `m≥1`.

For `d` a power of two, take two copies of each abstract pair `(d²/c,c)` over powers of two `1≤c≤d²`. Their total cost is `2d(2log₂d+1)`. For any subset of total column rank `0<m<d²`, let `c` be the least power of two above `m`. Both copies of that column rank are excluded and supply at least `2d²/c≥d²/m` complementary row rank. For `m≥d²` the trivial universal bound is zero because the full swap can be chosen. The symmetric list works after exchanging cuts and meets the ordinary rank totals. This extends the upstream scalar-profile example to **every** universal flag-area table. It certifies an order-of-growth limitation of that relaxation. Realizing such rank pairs by tensors still requires a construction. [Upstream dyadic scalar example](https://github.com/1337isnot1337/integer-factoring/blob/1b33192/research/weighted-cut-relaxation-limit.md)

There is also a matching exponent for the fixed-`k` scalar relaxation. Take `d=t^k` with `t≥2`. Use the `k` pairs `(t^{2(k-j)},t^{2(j+1)})` for `j=0,…,k−1`. Their cost is `k d^{1+1/k}`. For a nonzero subset column budget `m<d²`, let `c_j` be the smallest listed column size exceeding `m`. Since `m≥c_0`, we have `j≥1`. The excluded piece has row rank `d²/c_{j−1}≥d²/m`. The list is symmetric and has both row and column totals at least `d²`. Thus even the `k=3` scalar relaxation permits cost `3d^{4/3}` while respecting all universal flag-area constraints. This quantifies the need for information about simultaneous realizability.

The related two-partition rank in Naslund's Problem 12 counts rank-one product summands in either cut. Refining each `A_i` along its cheaper cut bounds this parameter above by `Σ min(r_i,c_i)≤S`. Karam's Question 1.2 restates the same tensor and asks for a lower bound with exponent greater than one for that parameter. The bounds above address the weighted score. [Naslund, Problem 12](https://doi.org/10.1016/j.jcta.2019.105190) · [Karam, Question 1.2](https://arxiv.org/pdf/2310.11356#page=4)
