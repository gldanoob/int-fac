# Order rank from rational evaluation labels

Consider clean totally real charts with a common integer evaluation $m$ and marks $a$ in an interval of $A$ consecutive integers. Use signed field exponents with the usual separate chart balance when the fields are nonmonic, and allow rational scalar columns supported on primes in a set $P$. The scalar columns use complete ideal valuations. In the clean Cogentic schedule $P$ can be the smoothness band. The goal is to express certified products on $P$ and on a disjoint list $J$ of small public target primes, such as the Bach generators. The following reduction applies to any explicit pool of charts and retained marks. [Projected order rank](cogentic-projected-order-rank.md) · [Saturated product certificates](cogentic-saturated-product-certificates.md)

## Private factors force exact shared cancellation

Choose $C\ge A$ covering the primes of $P\cup J$. Remove primes at most $C$ from every nonzero $|m-a|$. The remaining factors for distinct marks are pairwise coprime, since a prime dividing both labels divides their nonzero difference of magnitude less than $A$. All marks are required to evaluate to units modulo $N$.

Let $s_a$ be the sum of the mark exponents at $a$ over all charts. Every rational word supported on $P\cup J$ must have $s_a=0$ whenever $|m-a|$ has a nontrivial remaining factor. The same conclusion holds if that factor is a perfect power, because the rational equation is on full valuations. Thus only the set $S$ of $C$-smooth evaluation labels can contribute to a relaxation of shared cancellation. One bounded sieve through $C$ finds $S$ and the full valuations of its labels. For $I$ a subset of the primes up to $C$, write $D_I$ for the corresponding matrix of valuations of $|m-a|$ on $S$.

The restriction also applies when charts have different admissible subsets of the common grid. It does not rely on any independence of the coefficient samples. When $ℓ$ is planted in the field construction, its ordinary scalar direction is already allowed in $P$. By contrast a Bach prime below the band contributes no scalar direction in a clean chart. A scalar column there has a nonzero valuation at some prime ideal, with no compensating mark valuation. All small target directions outside $P$ must come from the rational labels.

For distinct primitive projective marks $(a,b)$ with $b>0$, replace $|m-a|$ by $|a-bm|$ and take $C$ at least the maximum determinant $|ab'-a'b|$. The same argument applies because a prime dividing two labels divides that determinant. On a height-$A$ grid, $2A^2$ suffices. [Projective evaluation labels](cogentic-rational-root-matching.md#joining-a-sheared-grid-to-arbitrary-public-witnesses)

## Quotient by the relations already obtained from shared marks

First compute the rational span $K$ of the exact field torsion identities with their scalar exponents, imposing zero finite valuations, balance where required and zero trace-zero logarithms separately in each chart. This uses the lattice precision and rational reconstruction in projected order rank. Do this before constraining label sums. For $x\in K$, write $s(x)$ for its mark-sum vector and $b(x)\in\mathbb Q^P$ for its total scalar exponent vector. A denominator-cleared $x$ yields the modular relation with rational exponent direction $b(x)+D s(x)$, after the global sign is removed by squaring. Here the full rational evaluation valuation map $D$ includes the large private factors when present.

Let $L_0=b(K\cap\ker s)$ be the shared-cancellation rank space and let $R$ be the primes at most $C$ outside $P\cup J$. Put
\[
 M=\{s\in s(K):\operatorname{supp}(s)\subseteq S,\ D_Rs=0\}.
\]
The linear map $s\mapsto\beta(s)=[b(x)]\in\mathbb Q^P/L_0$ for any lift $x\in K$ of $s$ is well-defined. Two lifts differ by a shared-cancellation identity. The exact exponent span on $P\cup J$, modulo $L_0$, is the image of
\[
 M\longrightarrow(\mathbb Q^P/L_0)\oplus\mathbb Q^J,
 \qquad s\longmapsto\bigl(\beta(s)+[D_Ps],\ D_Js\bigr).
\]
The private factors and the other bounded prime rows impose precisely the restrictions defining $M$. Conversely each lift of an $s$ in $M$ has a word supported on $P\cup J$. To isolate products on $J$ alone, restrict this map to the kernel of its first component. Whenever that component vanishes, an identity from $K\cap\ker s$ cancels the residual exponent on $P$. Elimination, denominator clearing and modular verification give the resulting relations. The overall bit cost is $\exp(O(H))$ for explicit chart data and cutoff $C$ of that size, under the clean extraction precision bounds.

The gain in rank over $L_0$ is at most $\dim M$. If each chart is balanced, this is at most $\max(0,|S|-1)$. In particular an input grid without $C$-smooth evaluation labels admits no rank gain. The rank on $J$ alone is at most $\operatorname{rank}D_J$ and can be smaller if the band correction is unavailable. This upper bound remains the same when adding coefficient tuples on the same evaluation grid. The field moment estimates concern the smoothness of the polynomial values. Applying them to this rank bound requires information about the separate labels $|m-a|$ or their attainable aggregate mark directions. [One-intercept moment tests](cogentic-one-intercept.md#which-moments-the-comparison-transfers)

## A productive rank increase in one exact chart

Take $N=12599$, $m=32$, and the monic real quadratic $f(X)=X^2-30X-1171771$. Its discriminant $4687984$ is positive and nonsquare, $f(32)=-93N$, and $f'(32)=34$ is a unit modulo $N$. For a root $\theta$ the paired marks give
\[
 (1-\theta)(29-\theta)=1171800,\qquad
 (4-\theta)(26-\theta)=1171875.
\]
Use $P=\{2,3,5,7,31\}$, which contains every prime divisor of the two scalar values and all four evaluation labels. With one chart, imposing all mark-sum rows leaves no nontrivial balanced identity with scalar valuations. Allowing the rational evaluation labels instead certifies
\[
 \frac{(32-1)(32-29)\cdot1171875}{(32-4)(32-26)\cdot1171800}
      =\left(\frac{125}{168}\right)^2\equiv1\pmod{12599}.
\]
All factors on both sides are units. The primitive exponent direction represents $125/168$, and $\gcd(125-168,12599)=43$. This fixture uses exact quadratic identities with repeated norm factors. It establishes a rank gain for the label relaxation with full valuations, without invoking the source's squarefree smoothness assumptions or a sampler for growing field degrees.

## Shifted windows with one large residual prime

Now let distinct grids use disjoint positive label windows $I_i=[m_i,m_i+A]$, with $M=\min_i m_i$ and $X=\max_i(m_i+A)$. Aggregate exponents separately by distinct label within each window, and require that their sum in each window is zero. This follows from separate chart balance when each chart uses just one of the windows. Choose $C\ge A$ covering every scalar and target prime. Suppose every retained label either is $C$-smooth or has the form $p u$ with $u$ $C$-smooth and $p>\max(C,\sqrt{2AX})$ prime. This hypothesis can be checked by removing the bounded primes and testing the remaining integers for primality and size. The argument concerns the rational label equations on the retained domain.

Each residual prime occurs in at most one label per window. Make a graph on windows, joining $i$ and $j$ when some residual prime divides both a label $n_i\in I_i$ and a label $n_j\in I_j$. Give oriented edge $ij$ the ratio $r_{ij}=n_j/n_i$. The ratio is independent of which shared prime gives the edge. For matches $(n_i,n_j)$ and $(n_i',n_j')$ from distinct primes $p,p'$, the determinant $n_i n_j'-n_i' n_j$ is divisible by $pp'>2AX$, whereas its absolute value is at most $2AX$. Matches from the same prime already coincide in each window. Thus all prime overlaps of that pair give the same rational direction, even if each overlap uses different integers.

First suppose all retained labels are rough. For each residual prime $p$, its exponents sum to zero. Write these exponents as transfers among the windows containing $p$, by choosing one of those windows as an origin. A unit transfer from $i$ to $j$ adds the bounded valuation vector of $r_{ij}$. Aggregate the transfers over primes. Their divergence at each window is the sum of its exponents, so the resulting flow is a circulation. Conversely, realize any integral circulation by choosing one shared prime for each edge and taking the prescribed transfers along those two labels. This realizes both the large-prime cancellation and the window balances. It follows that the rough-only label directions are exactly the span of the bounded valuation vectors of the products of edge ratios around cycles. The rank is at most $e-v+c$ for a graph with $e$ edges, $v$ windows and $c$ connected components. A spanning forest and its fundamental cycles compute the span. Chart torsion conditions may restrict the attainable directions further.

If smooth labels are also present, fix their exponents first. In each connected component their total exponent must vanish, since every rough transfer stays inside the component. For a fixed permitted vector on the smooth labels, the rough flows have prescribed divergences. A spanning forest produces one such flow, and every difference between two flows is a circulation. Hence the rank contribution beyond the smooth label directions and their fixed forest corrections still comes only from the cycle products. In a forest with no smooth labels, all rough-only label directions vanish regardless of the number of overlapping primes. This condition does not constrain the scalar relation space with zero aggregate mark exponents.

There is an additional bound when the smooth cofactors $u$ are at most $T$. On a cycle of length $k$, the center ratios $m_j/m_i$ telescope, and each actual edge ratio differs from its center ratio in absolute log by at most $\log(1+A/M)$. The cycle product therefore has absolute log at most $kA/M$. Its numerator and denominator are at most $T^k$ before reduction. A nontrivial positive ratio of integers at most $T^k$ has absolute log at least $T^{-k}$. Thus the cycle direction vanishes whenever $k A T^k<M$. If $\log M=\Theta(V)$ and $\log A,\log T=O(H)$, this includes every cycle of bounded length for sufficiently large inputs. Overlap graphs whose cycle spaces are generated by bounded-length cycles provide no rough-only label directions in that regime.

For a finite nontrivial cycle use the rough primes $100003,132151,113797$ and the three pairs of labels
\[
 (37\cdot100003,28\cdot132151),\quad
 (31\cdot132151,36\cdot113797),\quad
 (29\cdot113797,33\cdot100003).
\]
They lie in disjoint width-$117$ windows, and each residual prime exceeds $\sqrt{2AX}$ for their maximum window endpoint. The exponent vector $+1,-1$ in each window cancels every large prime and gives $33263/33264$. The label rank is one, although there are no equal labels between windows. Deleting either label of any shared-prime pair removes its edge and reduces the rough-only rank to zero. This is a rational label fixture. It supplies no field torsion identities for the chosen windows.
