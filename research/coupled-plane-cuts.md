# Complete-graph tensors with a different plane layout for each summand

Let $n$ vertices carry independent equality wires of dimension $D\ge2$ on all $\binom n2$ edges. Write $L=\log_2D$ and $B=\binom n2 L$ for their total bit width. Fix $d$ partitions of the vertices, each into $g$ equal planes. They can be arbitrary and need not be independent. Suppose the full tensor is the ordinary sum of $M$ nonzero tensors. Each summand may choose any one of the $d$ partitions and, after merging sites within each plane, give any tensor network on the planes. Charge its total interplane channel cost $C_i$ in bits, once per edge in that network. For fixed $d$ and $g\to\infty$,
$$
              \log M=o(g)\quad\Longrightarrow\quad
                          \max_i C_i\ge(1-o(1))B.                         \tag{1}
$$
The summands may couple the entire graph, with the layout chosen separately for each. More quantitatively, any fixed fractional saving at every summand requires $M\ge\exp(\Omega_d(g))$. The graph itself, in any of these layouts, has $(1-(n/g-1)/(n-1))B$ interplane bits. This gives the matching asymptotic upper bound when $M=1$. The result addresses a different range of piece counts from the [independent cube argument](affine-grid-directions.md) and the [coupled sum over axes](multiaxis-crossing-barrier.md#plane-factorizations-on-a-whole-grid). It uses only matrix rank.

## One cut for all summands

Let $K=2B/g$ be the total external log dimension of each plane, and choose $1\le r\le g$. Independently in each of the $d$ layouts select a uniformly random $r$-subset of its planes. One summand $i$ uses layout $a$. For plane $j$ in that layout let $w_{ij}$ be the smaller of $K$ and the sum of its incident channel widths. The flattening rank across plane $j$ is at most $2^{w_{ij}}$ by its external dimension and the network cut. Across the union $U_a$ of the selected planes its log rank is at most $\sum_{j\text{ selected}}w_{ij}$. Indeed the tensor is supported in the tensor product of the individual image spaces on the selected planes, tensored with the complementary spaces. This reasoning allows widths to concentrate at a few hubs. Moreover $\sum_j w_{ij}\le 2 C_i$.

A sample without replacement of $r$ numbers in $[0,K]$ has probability at most $\exp(-2s^2)$ of exceeding its expected sum by $K\sqrt{r}\,s$. Taking $s=\sqrt{\log(2M)/2}$ and a union bound gives one choice of planes such that for every summand, in its own layout,
$$
     \log_2\operatorname{rank}_{U_a}T_i
       \le (2r/g)C_i + K\sqrt{r\log(2M)/2}.
$$
This application of Hoeffding's sampling-without-replacement bound uses no independence between the events for different summands. [Hoeffding, §6, Theorem 4](https://doi.org/10.1080/01621459.1963.10500830)

Put $U=\bigcup_{a=1}^d U_a$ and $u=|U|$. Moving one more vertex to the selected side multiplies the flattening rank by at most its full external dimension $D^{n-1}$. A rank decomposition across the old cut proves this by expanding the moved vertex in a basis. Therefore the log rank of $T_i$ across $U$ is at most its bound across $U_a$ plus $(u-rn/g)(n-1)L$. This same correction is valid for every layout because all $U_a$ have size $rn/g$. The target has exact rank $D^{u(n-u)}$ across $U$, the product of the sizes of its independent crossing wires. Matrix rank is subadditive under ordinary sums, so
$$
    \frac{\max_i C_i}{B}
      \ge 1-
            \frac{u(u-1)}{(rn/g)(n-1)}
            -\sqrt{\frac{\log(2M)}{2r}}
            -\frac{g\log_2 M}{2r B}.                                    \tag{2}
$$
In particular $u\le drn/g$, bounding the first error by $2d^2r/g$ for $n\ge2$. Choose $r/g\to0$ and $r/\log(2M)\to\infty$ to prove (1). For example, when $\log(2M)=o(g)$, taking $r$ on the scale $g^{2/3}(\log(2M))^{1/3}$ makes the error $O_d((\log(2M)/g)^{1/3})$, since $B\gg g^2$. If every plane of every summand has incident cost at most $\rho K$, the sampling error vanishes, as the selected sum is always at most $r\rho K$. The same rank argument then forces $\rho\ge 1-o(1)$ already for $\log M=o(B)$, by choosing $r/g\to0$ with $g\log M/(r B)\to0$.

At the piece counts allowed by the general factoring transfer this estimate alone does not rule out a saving. Its conclusion is a restriction on how economically a small number of whole-graph summands can change layout. [Upstream transfer and cost of the piece list](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/multiaxis-cube-transfer.md)
