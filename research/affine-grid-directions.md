# Trying more directions on a lower-dimensional grid

Place the vertices of a complete graph at $V=\mathbb F_g^k$, with prime-power $g$ and fixed $k\ge2$. Consider any family of nonconstant affine maps $\ell_a:V\to\mathbb F_g$ whose linear parts span the dual space. Direction $a$ groups the vertices into its $g$ parallel planes. One might try to use $d>k$ such directions while keeping the recursion's growth base $k$. For this two-layer construction, almost every edge admits exactly the corners of a cube in at most $k$ genuinely independent directions. This applies to any number of directions. A minimax argument also gives an actual piece assignment for which even the cheapest direction retains the stated volume. The result concerns decomposing the independent equality wires in their local plane boxes. [Upstream grid transfer](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/multiaxis-cube-transfer.md) · [Earlier sparse rectangular geometry](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/past-half-sparse-grids.md) · [Earlier two-axis profile minimax](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/rectangular-grid-frontier.md)

## The corners determined by an edge

For an edge $u,v$ put $\xi=v-u$. Its box consists of all $w$ such that $\ell_a(w)\in\{\ell_a(u),\ell_a(v)\}$ for every selected direction. Use $k$ independent linear parts from the family as coordinates, so every other linear part has a unique coefficient row in this basis. Make a graph on the $k$ coordinate indices by joining two whenever they occur together in the nonzero support of a row. Write $B_1,\ldots,B_c$ for its connected components. Each row is supported in exactly one component. In particular $c\le k$. Equality requires every row to be parallel to a basis direction.

For all but at most $(k+2^{k+1})g^{k-1}$ choices of $\xi$, the full box is precisely
$$
        \left\{u+\sum_{j\in J}\xi|_{B_j}:J\subseteq\{1,\ldots,c\}\right\}.    \tag{1}
$$
Here the restriction of a vector sets its other coordinates to zero. To see this, first discard the $k$ hyperplanes where a basis coordinate of $\xi$ is zero. Any remaining corner has the form $u+\xi|_I$ for a subset of the basis coordinates. Every union of connected components works. For each other $I$, choose one row $h$ having nonzero coefficients on both sides of $I$. Validity of the corner forces $h(\xi|_I)=0$ or $h(\xi|_{I^c})=0$. Each is one proper hyperplane of differences. The union bound over the $2^k$ subsets proves (1), uniformly even if the list of plane directions is long. The constants in the affine maps cancel.

The box in (1) has exactly $m=2^{c-1}$ opposite edges, including the defining edge. The pairs switch complementary component subsets. Their unordered pairs of plane labels are the same in every direction, hence they define the same box. Conversely any edge defining that box must be opposite because each basis coordinate takes two distinct values. These regular boxes partition their regular edges, possibly including some additional edges from the coarse union bound. The fraction of actual irregular edges is $O_k(1/g)$. At direction $a$ in component $j$ the two layers of a regular box give just the $j$th cube cut if $\ell_a(u)\ne\ell_a(v)$, and give one merged plane otherwise. In the plane $k=2$, adding any third nonparallel direction leaves only the original edge for generic differences. In fact in this case a mixed corner with two nonzero basis increments is impossible, because each of the two terms of the third row's split has one nonzero summand.

## Width after choosing the cheapest direction

Suppose every regular box admits its own exact decomposition of its $m$ independent $D=2^\lambda$-label wires into at most $M$ nonzero pieces. The decompositions may vary with the box. At each direction use channels for that piece across its two planes, charging no channel for one merged plane. It suffices to use the actual minimum log ranks, at most $m\lambda$ each. The estimate remains a lower bound if an implementation declares larger channel widths. When it enumerates independent choices of a piece for each box, there is a complete assignment such that **simultaneously for every direction** the sum of its regular-box channel widths, divided by the original number of edge bits $\binom{g^k}{2}\lambda$, is at least
$$
 \frac1{\sqrt c}-O_k\!\left(\frac1g+
               \frac{\log_2 M}{\lambda}
               +\sqrt{\frac{\log(2d)}{g^{2k}}}\right).                         \tag{2}
$$
Repeated parallel directions yield identical minimum ranks and can be identified, so $d$ may in particular be bounded by $(g^k-1)/(g-1)$ for this estimate.

Fix any probability distribution $\alpha$ on the selected directions. For a regular box $b$, let $\beta_j$ be the total $\alpha$-weight of directions in $B_j$ which have two distinct layers on $b$, and $s_b=\sum_j\beta_j$. By the [weighted antipodal inequality](multiaxis-crossing-barrier.md#one-spectral-inequality-for-every-piece), some piece in the box has weighted width at least
$$
        m\lambda\|\beta\|_2-s_b\log_2 M
        \ \ge\ m\lambda s_b/\sqrt c-\log_2 M.
$$
Apply the inequality to $\beta/s_b$ when $s_b>0$. At $s_b=0$ all weights on distinct layers vanish. Each direction has exactly a fraction $(g^{k-1}-1)/(g^k-1)\le1/g$ of all edges within a plane. Dropping irregular edges costs $O_k(1/g)$ more. Consequently $m\sum_b s_b\ge(1-O_k(1/g))\binom{g^k}{2}$ for every $\alpha$.

For each regular box take the convex hull of its piece width vectors, and add these hulls as sets of possible sums. For the resulting compact convex polytope $S$, the finite minimax identity is
$$
       \max_{x\in S}\min_a x_a
            =\min_{\alpha\text{ a probability vector}}\max_{x\in S}\alpha\cdot x .
$$
It follows from linear programming duality, or by treating a full piece assignment and a direction as a finite zero-sum game. For each $\alpha$ the inner maximum is the sum of the box maxima just bounded. Thus choose an independent random piece in each box whose mean cost vector realizes the maximizing $x$. In each axis the total deviates below its mean by more than $m\lambda\sqrt{B\log(2d)/2}$ with probability at most $1/(2d)$, by Hoeffding's inequality on the $B$ independent box choices. Some actual assignment meets all $d$ bounds. Since $B\asymp_k g^{2k}$, normalization proves (2). This last sampling argument certifies an adverse assignment, and requires no randomness in the evaluator. [Hoeffding's inequality](https://doi.org/10.1080/01621459.1963.10500830)

With subexponential piece count in the label bits and $g\to\infty$, the worst assignment's cheapest plane therefore retains fraction at least $1/\sqrt c-o(1)\ge1/\sqrt k-o(1)$. Combining independent box choices before choosing the global axis cannot yield the fixed contraction below $1/\sqrt k$ needed by this growth-base-$k$ accounting. Even if the same piece has an exceptionally cheap direction in every box, those directions need not coincide on the adverse assignment. The conclusion bounds channel volumes in the declared tensor contraction. Algorithms that exploit additional identities among complete assignments or the actual factor-specific terminal tensors require their own analysis.

## Nonlinear polynomial directions

Keep the $k$ coordinate projections and allow any further nonconstant polynomials $f_a:V\to\mathbb F_g$ of total degree at most $t<g$. Each direction partitions vertices by its value, including when the fibers have unequal sizes. Join two coordinates if a polynomial depends on both. Then (1) holds outside an $O_k(t/g)$ fraction of **ordered pairs** $(u,v)$. Repeated endpoints can be discarded at cost $g^{-k}$. The constants are independent of how many polynomials were chosen.

In detail, for a mask $I$ form the mixed corner $w_I=(v_I,u_{I^c})$. If $I$ cuts a connected component, choose one polynomial $f$ depending on a variable on each side. Both $f(w_I)-f(u)$ and $f(w_I)-f(v)$ are nonzero formal polynomials in the independent $2k$ coordinates of $u,v$. In the first difference, a monomial involving a switched variable produces a monomial in a fresh variable that has no counterpart in $f(u)$. The other difference uses an unswitched variable in the same way. The substitution defining each mixed corner is injective on monomials. Each equality therefore holds on at most a $t/g$ fraction of pairs by the polynomial zero bound. Validity of this corner requires one of the two equalities. Union over at most $2^k$ masks and over the $k$ equal-coordinate events. All unions of complete components still work for every pair. [Schwartz's polynomial zero bound](https://doi.org/10.1145/322217.322225)

A regular box still partitions its antipodal edges, because the two endpoint values of each $f_a$ depend on a single component. The two sides of the corresponding component cut either have distinct labels or have the same label in that direction. The latter event has probability at most $t/g$ for each fixed nonconstant $f_a$, by applying the same bound to $f_a(u)-f_a(v)$. The minimax and rounding proof therefore gives (2) with $1/g$ replaced by $t/g$, for $t=o(g)$ and fixed $k$. There are at most $g^{\binom{k+t}{k}}$ distinct polynomials of the allowed degree. In particular if $t=o(g)$ the rounding error still tends to zero even if every such polynomial is used. A family containing an invertible polynomial change of basis has the same conclusion whenever the remaining directions in those coordinates have the required degree bound.

## Finite checks

The affine replay compared predicted boxes to literal intersections in seven prime-field grids. It found 632 regular and 1,048 irregular differences, with 268 regular boxes containing more than two vertices. Four nonlinear fixtures gave 1,776 regular and 8,677 irregular unordered pairs, including 894 regular pairs with extra corners. For each regular box the replay checked the complete label sets of all its opposite edges. It also enumerated every assignment in 21 finite games in which different pieces favor different directions. [Exact box and assignment replay](../experiments/affine-grid-directions.py)
