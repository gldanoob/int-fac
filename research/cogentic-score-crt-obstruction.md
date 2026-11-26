# A CRT-query obstruction for an actual smooth-relation test

On the fixed Cogentic schedule, consider an actual two-field relation predicate $F=I_1(a)I_2(a)$ at an admitted mark $a$ away from the target-prime roots. An adaptive computation that only reads affine residues of one field's intercept cannot approximate $F$ to arbitrary $\exp(-CH)$ accuracy while its cumulative CRT modulus leaves a long progression. This applies to the Boolean tests in the sufficient score used by the mean-time driver. [Fixed-schedule score](cogentic-conditional-score.md) · [Existence and mass of the admitted test](cogentic-read-once-score-obstruction.md#distinguishing-the-intercept-prefixes) · [Mean-time driver](cogentic-universal-score-sampler.md)

## The intercept leaves

Fix the slope in the first field and both coordinates in the second field. The absolute value tested by the first field is
\[
 \bigl|C+D(u+a v)\bigr|,\qquad D=P_0\ell(a-m),
\]
where $v$ is the fixed first-field slope and $u$ is uniform in a consecutive interval of $M=4UA$ integers. Let an observer know the other coordinates and query residues $c+d u\bmod q$. Each query can depend on the other coordinates and all earlier replies. Once a reply is fixed, its constraint is a single congruence modulo $q/\gcd(d,q)$, including the constant-query case. The inputs giving a complete, attainable transcript therefore form one residue class modulo the least common multiple $Q$ of the effective moduli along that transcript, intersected with the interval for $u$.

Suppose every attainable leaf satisfies $Q\le M/(16P)$ for some $P\ge2$ with $2P<\sqrt B$. Suppose also that
\[
 \sum_{P<p\le2P}\log p>\log|DQ|
\]
at every such leaf, with the sum taken over primes. There is then a prime $p\in(P,2P]$ that divides neither $D$ nor $Q$. Write the leaf as $u=u_0+Qj$ over consecutive indices $j$. At least one index class modulo $p$ makes $p$ divide the displayed norm, since $DQ$ is a unit modulo $p$. The norm cannot pass the smoothness predicate on that class because $p<\sqrt B$. There are at least $\lfloor M/Q\rfloor\ge2p$ consecutive indices, so at least $1/(2p)\ge1/(4P)$ of the leaf has $F=0$.

If the observer predicts $1$ on a leaf, its conditional error is at least $1/(4P)$. If it predicts $0$, its conditional error is the entire positive mass in the leaf. In either case the conditional error is at least the leaf's conditional positive mass divided by $4P$. Average this inequality over the leaves and the fixed coordinates. Every such predictor has uniform Boolean error at least
\[
 \frac{\mathbb P(F=1)}{4P}.
\]
The argument also holds with randomized query choices or predictions if the same modulus bounds hold on each realization.

## The fixed factoring schedule

On the conservative schedule, $\log M=(100000+o(1))V$, $\log|D|=O(V)$, and $\log B\asymp H$. Take $P=V^2$. The prime number theorem gives $\sum_{P<p\le2P}\log p\asymp V^2$, whereas $\log|DQ|=O(V)$ throughout the allowed range $Q\le M/(16V^2)$. The cutoff $2V^2<\sqrt B$ holds for large inputs. The established smooth-window lower bound gives $\mathbb P(F=1)\ge\exp(-cH)$ for a fixed $c$, so the error at these leaves is at least $\exp(-(c+o(1))H)$. In particular every observer with $\log Q=O(H)$ obeys the obstruction, including one that changes its moduli after seeing earlier replies.

This is a limit on replacing a genuine relation predicate by a CRT-only Boolean classifier. The same residue classes can still be used to count or average the predicate arithmetically. The bound also leaves open deterministic lists whose individual trial words are evaluated exactly, and it does not imply that the factorer times out on a specified padded input.
