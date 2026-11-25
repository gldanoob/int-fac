# The Euclidean tensor-price theorem closes the two-cut crossing test

Let `E_d(x,y,u,v)=[x=v][y=u]` on `d≥2` labels. For every finite exact decomposition `E_d=Σ A_i` over any field, write `r_i,c_i` for the ranks of the nonzero pieces in the cuts `xy|uv` and `xu|yv`. Then

\[
 \boxed{\displaystyle\sum_i\sqrt{r_i c_i}>d^{\sqrt2}.}\tag{1}
\]

Consequently no dimension supplies the strict finite seed sought by issue 52. More generally, on `2^λ` labels, every exact crossing family with `P_λ` nonzero pieces satisfies

\[
 \max_i (\log_2 r_i+\log_2 c_i)
 \ \ge\ 2\sqrt2\,\lambda-2\log_2 P_\lambda.\tag{2}
\]

For `P_λ=2^{o(λ)}`, the existing width bound `4ρλ+o(λ)` therefore requires `ρ≥1/√2`. This applies after any tensor-power regrouping or label restriction that gives the full exact crossing at the displayed output dimension. It also applies to a nonzero field multiple of the crossing, by rescaling the pieces. The bound concerns this specific two-cut interface. The deterministic factoring running time itself has no lower bound here. [Upstream finite-seed criterion and amplification](https://github.com/1337isnot1337/integer-factoring/blob/1b33192/research/finite-seed-amplification.md) · [Issue 52](https://github.com/1337isnot1337/integer-factoring/issues/52)

The proof applies Theorem 1.1 of OpenAI's November 24, 2026 manuscript *Euclidean geometry in the asymptotic spectrum of tensors*, pinned to `3344da59991ed94f9ba711217b29c1d760badfa6`. Its authors report a Lean development for Euclidean tensor prices in finite dimension. The application below is a mathematical deduction from the preprint. The local experiment checks its tensor and geometric accounting. We have not independently rebuilt the upstream Lean development or formalized the deduction in this repository. [Theorem 1.1 and the ordinary-sum rule](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/build/intro.tex#L34-L53) · [Full manuscript](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/paper.pdf) · [Authors' description of the Lean scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/379.md#L10-L13)

The [coordinate-placement proof](multiaxis-crossing-barrier.md#one-spectral-inequality-for-every-piece) also gives the weighted two-cut inequality directly and extends it to every fixed number of cube axes.

## Two rank factorizations at four sites

All logarithms below are base two. A tensor price is additive on independent wire products, monotone under linear maps local to each site, and compatible with adjoining unused sites. A wire of dimension `D` between two sites costs their distance times `log D`. If `L` tensors share four output sites forming a set `Z`, their ordinary sum costs at most their largest price plus `W(Z) log L`, where `W` is normalized Gaussian mean width. Indeed the ordinary sum is a restriction of the direct sum. In the plane `W` is half the perimeter for a convex polygon. [Pricing rules and sum inequality](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/build/intro.tex#L77-L118)

Choose two unit vectors `a,b` with angle `θ∈(0,π)`. Put the four legs `x,y,u,v` at `a,b,−b,−a`, respectively. The target is exactly the product of the two opposite `D`-dimensional wires. Its price is `4 log D`.

Suppose a piece has row rank `R`. Put its left factor at `t(a+b)/||a+b||` and its right factor at the negative of that point. A wire of dimension `R` joins the sites, and four wires of dimension `D` carry the external indices to their terminals. Contracting these wires with the two rank factors is a local linear construction. All four external distances equal `√(1−2ht+t²)` with `h=cos(θ/2)`. For column rank `C`, use `a−b` as the direction, giving `h=sin(θ/2)` and an internal wire of dimension `C`. Thus each available rank `K` has a layout of price at most

\[
 4\sqrt{1-2ht+t^2}\log D+2t\log K
 \ \le\ 4\log D+2t(\log K-2h\log D)+2t^2\log D.\tag{3}
\]

The second inequality follows directly from `√(1+z)≤1+z/2` for `z≥−1`. Compatibility permits distinct internal sites for each layout while charging the sum only at the four common terminals.

The source manuscript uses these two factor sites and their first-order movement in its proof of nonpositive curvature. Here we apply its resulting Euclidean price theorem in the other direction to bound the upstream rank sum. [Original two-site layout argument](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/build/curvature.tex#L104-L140)

## Tensor powers remove the cost of choosing a layout

Fix `0<α<1`, put `β=1−α` and `S_α=Σ r_i^α c_i^β`. For every positive integer `n`, `E_d^{⊗n}=E_{d^n}` after pairing the word indices. Group words in the seed pieces by their multiplicities `h_1,…,h_k`. There are at most `(n+1)^k` groups. For a nonzero group with ranks `R,C` and multinomial coefficient `M`, rank subadditivity and the tensor-product rule give

\[
 R^\alpha C^\beta
 \le M\prod_i(r_i^\alpha c_i^\beta)^{h_i}
 \le S_\alpha^n.\tag{4}
\]

Choose the angle by `cos(θ/2)=α/√(α²+β²)` and `sin(θ/2)=β/√(α²+β²)`. Suppose `log S_α=2√(α²+β²) log d−δ` with `δ>0`. By (4), every nonzero group has at least one available cut `K` obeying

\[
 \log K\le n(2h\log d-\delta),
\]

with `h` the corresponding cosine or sine. Otherwise the weighted mean of the two log ranks would exceed `n log S_α`. With `D=d^n`, (3) bounds the price of that group by `4n log d−2ntδ+2nt² log d`. Summing incurs only `W(Z)k log(n+1)`. Fix `t=δ/(2log d)>0` and divide by `n`. The strictly positive saving `δ²/(2log d)` persists as `n→∞`, contradicting the target price. We obtain the full family

\[
 \boxed{\displaystyle
  \sum_i r_i^\alpha c_i^{1-\alpha}\ \ge\
   d^{2\sqrt{\alpha^2+(1-\alpha)^2}}\quad (0\le\alpha\le1).}\tag{5}
\]

The two endpoints are the ordinary full-rank budgets. At `α=1/2` this gives `Σ√(r_i c_i)≥d^{√2}`. The left side is algebraic. By Gelfond–Schneider, an integer `d≥2` raised to the algebraic irrational `√2` is transcendental. Equality is impossible. Finally `Σ√(r_i c_i)≤P_λ max_i √(r_i c_i)` gives (2). [Gelfond's original theorem](https://www.mathnet.ru/eng/im4924)

## Asymmetric two-piece partitions

There is also a bound when only **one** rank per piece is recorded. Suppose `E_d=B+C`, both pieces nonzero, and put `X=log r(B)`, `Y=log c(C)`, `L=log d`. Then

\[
 \sqrt{X^2+Y^2}\ \ge\ 2L-4\sqrt L.\tag{6}
\]

If the left side is below `2L`, choose `δ>0` with `||(X+δ,Y+δ)||₂=2L`, and place the terminals so `2L(cos(θ/2),sin(θ/2))=(X+δ,Y+δ)`. The triangle inequality gives `2L−||(X,Y)||₂≤√2 δ`. For the two eligible layouts the linear saving in (3) is the same. The rhombus has mean width at most four, so their sum costs at most `4L−2tδ+2t²L+4`. The price of `E_d` requires `δ²≤8L` by taking `t=δ/(2L)`. This gives (6). In particular, if `r(B)≤d^{p+o(1)}` and `c(C)≤d^{q+o(1)}`, then `p²+q²≥4`.

Grouping rank-one terms according to their cut shows that the two-partition rank in Naslund's Problem 12 is at least `d^{√2−O(1/√(log d))}`. When only one of the two groups is used its rank is `d²` immediately. This conclusion uses the November 24 tensor-price theorem. [Naslund's Problem 12](https://doi.org/10.1016/j.jcta.2019.105190) · [Karam's precise restatement, Question 1.2](https://arxiv.org/pdf/2310.11356#page=4)

The source manuscript's shifted-crossing construction supplies the matching leading two-piece tradeoff. With its two target wire exponents both equal to one and shift `−2<Δ<2`, its integral factors have respective exponents at most `√(2+Δ)` and `√(2−Δ)`. Restrict both terminal alphabets to their smaller size to obtain square crossings of dimension `d=2^{n+o(n)}` along the construction. Thus the interior arc `p²+q²=4` is attained asymptotically when recording one specified cut per piece. This upper construction and (1) measure different costs. [Shifted crossing theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/build/curvature.tex#L17-L34)

The [exact checks](../experiments/euclidean-crossing-barrier.py) verify the two terminal layouts for rational points on the unit circle, reconstruct literal finite-field tensor-power groups, and test the bounds with integer arithmetic. Run `python experiments/euclidean-crossing-barrier.py`. The all-field conclusion follows from (3)–(5) and the cited price theorem.
