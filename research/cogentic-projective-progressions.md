# Primitive normalization preserves the private-row obstruction

A single rational projective change of coordinates cannot make a short equispaced list support a Cogentic target relation by increasing the supply of repeated band rows. This holds even when there is no height restriction on the matrix of the projective transformation. The relevant height bound is on the primitive output marks.

## Determinant bounds after normalization

Let $S\ge3$ and let $u_1,\ldots,u_S$ be primitive integer parameter directions, pairwise distinct in $\mathbb P^1(\mathbb F_p)$ for every prime $\sqrt B<p\le B$. This holds for $u_i=(i,1)$ at $S$ consecutive indices when $S\le\sqrt B$. An equispaced rational parameter progression can be absorbed into the projective transformation. It also holds for primitive parameter marks of height $A_0$ with $2A_0^2\le\sqrt B$.

Let the transformation have an invertible rational $2\times2$ matrix. Clear denominators and divide out the common content to obtain a primitive integral matrix $M$. Write $M u_i=g_i v_i$ with $g_i>0$ the common divisor of the two output coordinates and $v_i$ primitive. Signs of the $v_i$ do not affect the proof. Assume only that $v_i$ has both coordinates of absolute value at most $A$. Put
\[
   C=\max_{i<j}|\det(v_i,v_j)|\le 2A^2 ,
\]
which is positive because the projective outputs are distinct over $\mathbb Q$. Let $\mathcal P$ consist of the band primes dividing some $\det(v_i,v_j)$. A prime in $\mathcal P$ must divide $\det M$, by
\[
   g_i g_j\det(v_i,v_j)=\det M\det(u_i,u_j)
\]
and the input distinction condition modulo $p$.

At such a prime $M\bmod p$ has rank one. Rank zero is impossible for a primitive matrix. Its projective kernel contains at most one of the input directions, so at most one $g_i$ is divisible by $p$. Among all other indices, the images reduce to the same projective direction and their output pair determinants are divisible by $p$. Thus each $p\in\mathcal P$ divides at least $\binom{S-1}{2}$ of the output pair determinants. Multiplying the pair determinants and using $|\det(v_i,v_j)|\le C$ yields
\[
                \prod_{p\in\mathcal P}p\ \le\ C^{S/(S-2)} .
\]

There is a sharper bound for the rows of one mark. Let $\mathcal P_i$ be the band primes dividing $\det(v_i,v_j)$ for some $j\ne i$. If $i$ is nonexceptional for such a prime, the prime divides the determinant to every other nonexceptional index. If $i$ is exceptional, the determinant identity gives
\[
     v_p(\det(v_i,v_j))=v_p(\det M)-v_p(g_i)
         \qquad\text{for all }j\ne i
\]
because $p\nmid \det(u_i,u_j)g_j$. This valuation is positive for all the neighbors as soon as it is positive for one. In either case each $p\in\mathcal P_i$ divides at least $S-2$ of the $S-1$ determinants incident to $i$. Thus
\[
   \prod_{p\in\mathcal P_i}p\ \le\ C^{(S-1)/(S-2)},\qquad
   |\mathcal P_i|\ \le\ \frac{2(S-1)}{S-2}\frac{\log(2A^2)}{\log B}.
\]
The bounds use only primitive output determinants, so a large determinant before normalization cannot increase the repeated-prime budget.

## Ordinary rows and target cancellation

A projective ordinary row at a prime $p$ is tied to a fixed projective residue direction above $p$. Therefore two incidences in the same row imply $p\mid \det(v_i,v_j)$. This is the usual simple-root label for clean squarefree band norms. It also holds for an actual fixed prime ideal dividing both linear elements $a_i-b_i\alpha$ and $a_j-b_j\alpha$, because their linear combination with coefficients $b_j,-b_i$ is the integer determinant. The matrix-rank-one argument handles singular reduction of the coordinate change, including cancellation of arbitrary powers of $p$ during normalization. No assumption that the transformed direction remains finite modulo $p$ is needed for the determinant bounds.

For a field with squarefree marked norms, each band prime contributes at most one ideal row to a column. Hence at most $|\mathcal P_i|$ ordinary rows at mark $i$ can recur anywhere within the chart in that field. In the conservative Cogentic schedule $\log A/\log B=O(1)$ while a clean norm has $\Omega(V/H)$ ordinary factors after omitting its possible protected prime. Consequently every clean column has a private ordinary row within any such chart. The ordinary row cancellation equations then force every selected coefficient to vanish, so this chart alone cannot feed a protected target relation. This applies equally to an adaptively selected subset of the chart, since the private rows remain private within the subset. It does not apply if an incidence is allowed to cancel with marks outside the chart, or if parameter directions collide at band primes before the coordinate change. [Ordinary cancellation and target equations](cogentic-postselected-mark-rank.md)

## Exact checks

Take $M$ with columns $(1,115)$ and $(-343,-637)$ and parameters $0,1,2$. The three directions, up to sign and after dividing out their gcds, are $(7,13)$, $(19,29)$ and $(31,37)$. The matrix is primitive with determinant $38808$, exceeding $2\cdot37^2$. For band $(\sqrt{47},47]$ the repeated primes are $7$ and $11$. The mod-$7$ exceptional index is $0$, leaving the pair $(1,2)$ with determinant divisible by $7$. The mod-$11$ exceptional index is $2$, leaving $(0,1)$ with determinant divisible by $11$. A seeded exact check on 256 nonsingular primitive matrices with between three and ten consecutive parameters also verified the column and chart bounds, including 159 repeated-prime cases.
