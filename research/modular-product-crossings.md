# A crossing with a public product congruence

An odd target product gives a local crossing with a smaller two-cut width than the full crossing. Its labels must be the actual operand words. A different cut, separating both operands' low bits from both operands' high bits, can still require a bond of nearly half the operand length. These two statements distinguish a possible arithmetic saving from the work of propagating it through a multiplier.

## A shared residue gives a smaller exact crossing

Take odd words `1≤x,y,u,v<2^λ` and an odd `N`. For `1≤w≤λ`, set

\[
 T(x,y,u,v)=[x=v][y=u][xy\equiv N\pmod {2^w}].
\]

Let `K=2^(w−1)`, `D=2^(λ−w)`. Each word consists of its odd low residue and a high word in `[0,D)`. Relabel the low residues at `y,u` by the involution `r↦N/r mod 2^w`. The resulting tensor is exactly the product of the four-way diagonal `Δ_K` on the low labels and the usual crossing `E_D` on the high labels. All label conversions take polynomial bit time, even when `N` is unfactored.

In each of the cuts `xy|uv` and `xu|yv`, the diagonal has rank `K`. Its factors simply check both local low labels against a common `(w−1)`-bit channel. Tensoring it with every piece of the fixed-prime modular crossing gives, for each fixed coefficient prime `p`, polynomially many exact scale-one pieces whose two channel widths in bits sum to at most

\[
 2(w-1)+2\sqrt2(\lambda-w)+O_p(\sqrt{\lambda-w}+1). \tag{1}
\]

The construction retains the high-word family's factor-generation bound and adds the elementary low-residue checks. At `w=λ` only the diagonal is needed. A comparable unrestricted crossing has `2^(λ−1)` odd labels. If `(w−1)/(λ−1)` stays positive, (1) is strictly below its leading width `2√2(λ−1)`. The saving refers to this public congruence on these two particular input labels. The upstream grid transfer requests an unrestricted crossing at each scheduled pair of edges. Its grouping steps can put internal transform messages on those edges. [Modular half-rate family](https://github.com/1337isnot1337/integer-factoring/blob/1b331929/research/modular-half-endpoint.md) · [Grid transfer hypotheses](https://github.com/1337isnot1337/integer-factoring/blob/1b331929/research/subexponential-piece-transfer.md) · [Audited multiplier messages](https://github.com/1337isnot1337/integer-factoring/blob/1b331929/research/factoring-network-structure.md)

There is a complementary lower bound. For every finite exact decomposition of `T` into pieces of row and column matrix ranks `r_i,c_i`,

\[
 \log_2\sum_i\sqrt{r_i c_i}\ \ge
 \sqrt{(\lambda-1)^2+(\lambda-w)^2}. \tag{2}
\]

Sum out the low residue at `y,u` after the relabeling, preserving the high words there. Each common low residue still appears at `x,v`. The result is a rectangular crossing of two independent wire dimensions `D₁=KD, D₂=D`. These local maps leave the two ranks of each piece at most their original values.

For the rectangular crossing put `L_j=log₂ D_j`, `G=√(L₁²+L₂²)` and place each wire's endpoints at opposite unit coordinate vectors in the plane. The target price is `2(L₁+L₂)`. For the row cut move the two rank-factor sites from the origin to `±t(L₁,L₂)/G`. For the column cut use `±t(L₁,−L₂)/G`. The two possible layouts have the same first-order saving `2tG` on external wires. More precisely, the external cost is at most `2(L₁+L₂)−2tG+t²(L₁+L₂)`, by the square-root bound for the two distances. The internal wire costs `2t log₂ R` for the chosen cut rank `R`. Under tensor powers group summands by their multiplicities. At least one cut rank in each nonzero type is at most `(Σ√(r_i c_i))^n`, since their geometric mean is at most that quantity. An exponential gap below `G` then contradicts the target price for small fixed `t`, after charging the polynomially many types. The zero-dimensional logarithm case `G=0` is immediate. This proves (2) using the same all-field Euclidean price theorem as for the square crossing. [Type and ordinary-sum bounds](euclidean-crossing-barrier.md) · [Primary Euclidean price theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/build/intro.tex#L34-L53)

## A low/high cut in the modular product table

The complete modular relation at precision `k+h` has both operand words free in `[0,2^(k+h))`. Write `x=a+2^k X` and `y=b+2^k Y`. Index rows by the two low words `(a,b)` and columns by the high words `(X,Y)`. The entry is `[xy≡N mod 2^(k+h)]`. Put `m=min(k,h)≥3` and `H=2^m`. Over every field the matrix has rank at least `M`, where

\[
 M=2^t,\qquad t=\max\{0\le j\le m-3:4j2^j<H\}. \tag{3}
\]

In particular the rank is `Ω(2^m/m)`. In characteristic other than two it is at least `2^(m−3)`.

Use each odd `a` with the unique `b=N/a mod 2^k`. Restrict `X` to `[0,H)` and sum columns over all `Y` in one residue class modulo `H`. For each `X` there is exactly one original `Y mod 2^h`, since `a+2^k X` is odd. Thus the reduced row is the indicator of an affine line

\[
 Y=\alpha_a X+\beta_a\pmod H,\qquad
 \alpha_a=-b/a=-N/a^2,\qquad
 \beta_a=((N-ab)/2^k)/a\pmod H. \tag{4}
\]

Here `2^k=0 mod H`. The slopes run through the residue class `−N mod 8` in `Z/H`. Indeed the squaring map on the odd units has exactly four elements in its kernel for `m≥3`. For an odd `u`, one of `u−1,u+1` has 2-adic valuation one, so a square root of one is `±1 mod 2^(m−1)`. Every odd square is one modulo eight. The image therefore has precisely the required `H/8` elements.

Choose one row per slope `α₀+8j` for `0≤j<M`. Two lines of slopes `α_i,α_j` meet at most `gcd(α_i−α_j,H)` times regardless of intercept. For each selected `i`, exactly `M/2^(v+1)` other indices have `v₂(i−j)=v`, for `0≤v<t`. The total of these pairwise intersection bounds equals `4tM`, which is below `H`. Every selected line has a private point, giving an identity minor of size `M` in the projected matrix. Taking a power of two at most `H/(8m)` gives the stated asymptotic size. For the characteristic-specific improvement, extend scalars to include a primitive `H`th root of unity. The Fourier coefficient of a slope-`α` line at `(-α,1)` is a nonzero scalar, whereas every line of a different slope has zero coefficient there. Thus one row for each of the `H/8` slopes is linearly independent. Field extension preserves matrix rank.

An exact tensor train reading the low blocks of both operands before their high blocks therefore needs at least `m−O(log m)` bond bits at this cut. A deterministic representation carrying the entire residual truth table as one of several states has at least `H/8` distinct such states, independently of field. Both conclusions use the full high-word ranges at modular precision `k+h`.

For the exact integer relation with bounded operands, the crossing is supported only on `s` genuine ordered factor pairs `(x,N/x)`. Relabeling each leg on its support makes it the four-way diagonal of size `s`. Its minimum finite score `Σ√(r_i c_i)` is exactly `s`. The single diagonal tensor attains `s` in both cut ranks. Summing out the `y,u` legs of any decomposition gives an ordinary diagonal matrix of rank `s` between `x,v`, and each projected piece has rank at most `min(r_i,c_i)`. Exact integer bounds can consequently remove the large modular minor. Generating the optimal diagonal labels by listing the pairs already reveals the factors. Constructing a circuit that evaluates the constrained contraction from `N` remains the algorithmic question.

The [exact checker](../experiments/modular-product-crossings.py) compares 63,281 literal entries in 26 masked tensors, constructs 1,008 projected arithmetic rows by direct enumeration, checks 49 private-point minors, and computes the ranks of 147 finite-field matrices. Run `python experiments/modular-product-crossings.py`. The general bounds are the deductions above. No factoring runtime improvement is claimed.
