# Restricted energy for unit square roots modulo a composite

Baier's restricted second-energy bound holds for unit radicands after three corrections to its proof. This gives a uniform bilinear saving for two intervals of radicands, with arbitrary complex weights on any chosen roots. Write $q^{o(1)}$ for a factor bounded by $O_\epsilon(q^\epsilon)$ for each $\epsilon>0$. None of the counting arguments requires the factorization of the modulus to be known to the algorithm. [Baier, Theorem 4 and §§2.2.3–2.2.8](https://arxiv.org/html/2601.15448v4#S2.SS2)

## Restricted second energy

Fix a modulus $q\ge2$, a unit $j$ modulo $q$, and an integer interval of length $M\le q$. For every unit radicand $m$ in the interval, allow any subset of its roots $x^2\equiv jm\pmod q$. For $1\le H\le M$, let $I(d)$ count ordered pairs of allowed roots with $x_1-x_2\equiv d\pmod q$ and $1\le |m_1-m_2|\le H$. Then

\[
 \sum_{d\bmod q} I(d)\ll q^{o(1)}HM,
 \qquad
 \sum_{d\bmod q} I(d)^2\ll q^{o(1)}\left(HM+\frac{H^3M^2}{q}\right).
\]

The first bound counts radicand pairs and uses the $q^{o(1)}$ root multiplicity of a unit modulo $q$. With $k=j^{-1}\pmod q$, set $h=m_1-m_2$ and $s=2(m_1+m_2)$. Squaring twice gives

\[
 h^2+k^2d^4\equiv kd^2s\pmod q.
\]

The factor two in $s$ is needed in Baier's (28). The variable $s$ belongs to an interval of length at most $4M$ even when the original radicand interval is translated. Once $(h,s)$ is fixed, so are the two radicands, and there are at most $q^{o(1)}$ choices of the two roots. Thus $I(d)$ is bounded by $q^{o(1)}$ times the corresponding congruence count. [Baier, §2.2.3](https://arxiv.org/html/2601.15448v4#S2.SS2.SSS3)

### Reduction of nonunit differences

Let $t$ be the gcd of $d$ and the square root of the largest square dividing $q$. The congruence implies $t\mid h$. After dividing by $t^2$, put $u=((d/t)^2,q/t^2)$. This is squarefree, divides $d/t$ and $h/t$, and is coprime to $R=q/(t^2u)$. These assertions follow prime by prime. A prime with exponent $e$ in $q$ can survive in $u$ only when $e$ is odd and its exponent in $d$ is at least $(e+1)/2$. Put $d'=d/(tu)$ and $h'=h/(tu)$. Then $(d',R)=1$ and

\[
 (h')^2+k^2t^2u^2(d')^4\equiv k(d')^2s\pmod R,
 \qquad 1\le |h'|\le H'=H/(tu).
\]

Write $J$ for the number of these pairs $(h',s)$. Only $tu\le H$ contributes. Each original $d$ is assigned a unique triple $(t,u,R)$, and within the triple there are at most $t$ representatives $d'$ of each class modulo $R$. When $R=1$, replace $I(d)$ by $q^{o(1)}J$ and sum $J^2\ll (H'M)^2$ over the at most $t$ representatives. This gives $t(H'M)^2\le H^3M^2/q$. The zero difference cannot arise from distinct radicands in the stated interval. This reduction uses the modulus only in the proof. [Baier, §§2.2.3–2.2.4](https://arxiv.org/html/2601.15448v4#S2.SS2.SSS4)

### Counting on the reduced lattices

For $R>1$, differences of two representatives lie in the lattice $x\equiv k(d')^2y\pmod R$, in the box $|x|\le (H')^2$, $|y|\le4M$. The lattice has determinant $R$. If the lattice points in the box have rank zero, there are at most two representatives, from $h'$ and $-h'$. Charge their contribution to $\sum I(d)$.

In rank one, all differences are multiples of a shortest vector $(a,b)$ generating the lattice along its line. Both coordinates are nonzero. For example, the presence of the vertical vector $(0,R)$ would imply $4M\ge R$, and then the box also contains a lattice vector with first coordinate one. The horizontal case is analogous. Given any representative $(h_0,s_0)$, one has $a\mid(h')^2-h_0^2$ and $b\mid s-s_0$. Each factorization $a_1a_2=|a|$ imposes the two residue constraints $h'\equiv h_0\pmod{a_1}$ and $h'\equiv-h_0\pmod{a_2}$. Their compatible intersection has at most $1+O(H'/[a_1,a_2])$ elements in the box. In particular,

\[
 J\ll \tau(|a|)+\frac{H'}{|a|}\sum_{a_1a_2=|a|}(a_1,a_2),
 \qquad J\ll M/|b|.
\]

The second bound uses at most two possible $h'$ for each $s$. To retain the additive one missing in Baier's (44), split off all $J\le C_\epsilon q^\epsilon$ with a constant large enough to absorb twice the first term. Their contribution to $\sum I(d)J$ is at most $C_\epsilon q^\epsilon\sum I(d)$. For larger $J$, the second term in the first bound absorbs the first. Squaring, applying the divisor bound, and taking the minimum with the $b$-bound gives

\[
 J^2\ll q^{o(1)}\sum_{a_1a_2=|a|}
 \min\!\left\{\left(\frac{H'(a_1,a_2)}{|a|}\right)^2,\frac{M^2}{b^2}\right\}.
\]

For fixed $(a,b)$, the unit classes $d'$ with $k(d')^2b\equiv a\pmod R$ number at most $q^{o(1)}(a,b)$. Indeed, $(b,R)$ must divide $a$, and after dividing by it there is a unit square-root congruence modulo $R/(b,R)$. Each solution there has at most $(b,R)$ lifts. To sum over $b$, for every $z>0$ use

\[
 \sum_{1\le b\le 4M}(a,b)\min\{z^2,M^2/b^2\}
 \le \sum_{f\mid a} f\sum_{n\ge1}\min\{z^2,M^2/(fn)^2\}
 \ll \tau(|a|)Mz.
\]

The inner sum follows by splitting at $M/(fz)$, including the case when that point is below one. Inserting $z=H'(a_1,a_2)/|a|$ leaves the sum of $(a_1,a_2)/(a_1a_2)$ over $a_1a_2\le (H')^2$, bounded by $O(\log^3(2H'))$ after extracting their gcd. Charging $I(d)\ll q^{o(1)}J$ on the large-$J$ part, with the factor $t$ for lifts of $d'$, gives $q^{o(1)}tH'M\le q^{o(1)}HM$ per triple. [Baier, §2.2.7](https://arxiv.org/html/2601.15448v4#S2.SS2.SSS7)

In rank two put $A=1+M/R$. For each fixed $h'$, there are $O(A)$ choices of $s$. Pairs of representatives with equal squared $h'$ therefore contribute $O(AJ)$ to $J^2$. This term is needed in Baier's (48). If the two squares differ, fix their nonzero difference and the difference of the two $s$ values. There are at most $q^{o(1)}$ choices of the signed $h'$ pair by integer factorization of the nonzero difference, and $O(A)$ choices of the first $s$. Since the box contains two independent lattice vectors, its lattice point count is $O((H')^2M/R)$ by the successive-minima bounds. Consequently,

\[
 J^2\ll AJ+q^{o(1)}A(H')^2M/R,
 \qquad J\ll A+q^{o(1)}\sqrt{A(H')^2M/R}.
\]

Here $M/R=Mt^2u/q\le H^2M/q$, $H'\sqrt{M/R}\le H\sqrt{M/q}$, and $H'M/R=tHM/q\le H^2M/q$. Multiplying by the first-moment sum of $I$ gives a total of at most $q^{o(1)}(HM+H^2M^{3/2}/\sqrt q+H^3M^2/q)$. The middle term is the geometric mean of the other two. There are only $q^{o(1)}$ possible triples in the reduction. This proves the restricted second-energy estimate, including composite moduli with nonunit differences. [Baier, §§2.2.8–2.2.9](https://arxiv.org/html/2601.15448v4#S2.SS2.SSS8)

## Bilinear cancellation by two block decompositions

Let the two radicand intervals have lengths $M_1,M_2$, with unit class multipliers $j_1,j_2$. Write their root records as $x,y$, each record carrying its radicand. Assign arbitrary complex weights $\alpha_x,\beta_y$, even when different roots of one radicand have different weights. For $S=\sum_{x,y}\alpha_x\beta_y e_q(a xy)$, put $g=(a,q)$ and $r=q/g$. If $r>1$, then $e_q(a xy)=e_r((a/g)xy)$ with a unit multiplier modulo $r$. The reduced roots still have unit radicands and multipliers. When distinct original root records coincide on reduction, the multiplicity over one radicand is at most $q^{o(1)}$, by the unit square-root bound at $q$.

Suppose $H=\lfloor r^{1/3}\rfloor\le M_i\le r$. Partition each radicand interval into blocks of length at most $H$. There are $K_i=O(M_i/H)$ blocks. Let $R_i(d)$ count all ordered differences of root records within the same block of interval $i$, measured modulo $r$. The restricted energy bound controls pairs with different radicands. The pairs with equal radicand have total number at most $q^{o(1)}M_i$, so their second energy is at most $q^{o(1)}M_i^2$. Applying the triangle inequality in $\ell^2$ gives $\sum_d R_i(d)^2\ll q^{o(1)}M_i^2$.

For the weighted step set $A_0=\|\alpha\|_\infty$ and $B_0=\|\beta\|_\infty$. Cauchy in the second root and across the first blocks bounds $|S|^2$ by $q^{o(1)} M_2 B_0^2 K_1$ times

\[
 \sum_{x,x'\ {m same\ block}}\alpha_x\overline{\alpha_{x'}}
 \sum_y e_r((a/g)(x-x')y).
\]

This sum is nonnegative, by its expression as a sum of squares. Cauchy over the at most $q^{o(1)}M_1H$ first-side pairs bounds its square by $q^{o(1)}M_1H A_0^4$ times the sum of the squared inner sums. In each inner sum apply Cauchy across the $K_2$ second blocks. Expanding the block squares then gives

\[
 |S|^4\ll q^{o(1)} A_0^4 B_0^4\frac{M_1^3M_2^3}{H^2}
 \left|\sum_{d,e\bmod r}R_1(d)R_2(e)e_r((a/g)de)\right|.
\]

The Fourier matrix in this last expression has operator norm $\sqrt r$, since $a/g$ is a unit. Its contribution is bounded by $q^{o(1)}\sqrt r M_1M_2$. We obtain

\[
 |S|\ll q^{o(1)} A_0B_0 M_1M_2 r^{-1/24}.
\]

This estimates cancellation relative to the full radicand interval lengths. A sparsity-sensitive bound relative to the actual support is not asserted. If $q\ge N^{.97}$, $q\le N^{1+o(1)}$, and $g\le N^{.031}$, then $r\ge N^{.939}$ and the saving is $N^{-.039125+o(1)}$. The block length fits the intervals of sizes $N^{.437+o(1)}$ through $N^{.533+o(1)}$, and more generally the range $N^{.35}$ to $N^{.64}$. For a multiplier equal to $\ell$ times a unit modulo $q$, one has $g\le |\ell|$. Multipliers with no bound on $g$ cannot give a uniform saving, as $a\equiv0\pmod q$ makes the phase constant.
