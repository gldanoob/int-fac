# A hidden kernel in sparse incidence Grams

Let $n=2h$ and $1\le t\le h$. There is a distribution of $n\times ht$ binary matrices $M$ having exactly two ones per column and $t$ ones per row. Put $G=MM^T/t$. The mean Gram has least eigenvalue $1-1/(n-1)$, while every realization has an exact signed left dependency. For $i\ne j$,
$$
 \mathbb E G_{ij}=\frac1{n-1},\qquad
 \operatorname {Var}G_{ij}=\frac1{t(n-1)}-\frac1{(n-1)^2}.
$$
Every row of every realization has squared distance $1/t-1/(n-1)$ from its mean row. In particular the maximum row distance tends to zero for any $t\to\infty$. At $t=h$ every entry variance is $O(n^{-2})$.

Take any simple bipartite $t$-regular graph on two halves of size $h$. For instance, left vertex $j$ has right neighbors $j,j+1,\ldots,j+t-1\pmod h$. Randomly permute all vertices and let $M$ be the two-endpoint incidence matrix of its edges. A fixed vertex pair is an edge with probability $t/(n-1)$ by symmetry. The Gram diagonal is one identically and its off-diagonal entries are $1/t$ on edges and zero on the other pairs. This proves the formulas. The mean has the constant vector as a $2$-eigenvector and acts by $1-1/(n-1)$ on its orthogonal complement. The signed bipartition vector $s$ satisfies $s^TM=0$, even though $s$ is orthogonal to the constant vector. In particular $\|G-\mathbb E G\|_{\mathrm{op}}\ge 1-1/(n-1)$ in every realization. If any rows and all their incident columns are deleted, the surviving signs still annihilate every surviving column. The restricted matrix is rank deficient whenever any row survives.

The same obstruction accommodates $2k$ ones per column. For $1\le k<h$, choose a uniform balanced bipartition and use every column selecting exactly $k$ positions on each side, normalizing the common Gram diagonal to one. Its distinct entries within a side and across sides are $(k-1)/(h-1)$ and $k/h$, respectively. The unconditional common off-diagonal mean is $(2k-1)/(2h-1)$, and each entry variance is
$$
 \frac{h(h-1)}{(2h-1)^2}
 \left(\frac{h-k}{h(h-1)}\right)^2.
$$
For $k=o(h)$ the mean gap tends to one, all off-diagonal entry variances are $O(n^{-2})$, and every realization again has the balanced signed kernel.

In the two-field factoring argument, a reduction of the relation supply condition must account for coherent signed errors across rows. The examples disprove an inference of full row rank from a well-conditioned mean plus uniformly vanishing squared row errors, including after the stated row-and-column deletion. They give no lower bound on the number of actual smooth relations, whose arithmetic structure supplies additional information. The paper controls the operator error using a stronger summed off-diagonal estimate. [Cogentic, Proposition 10.1](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/deterministic_factoring_l34/paper.pdf#page=52)

The finite check computes 1,298 individual row errors from 77 regular graphs and 630 pair entries from 15 balanced hypergraphs, using exact rational arithmetic. [Replay](../experiments/cogentic-hidden-gram-kernel.py)
