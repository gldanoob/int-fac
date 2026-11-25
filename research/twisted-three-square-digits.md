# Computing three-square digits on twists of every fixed integer

Fix an odd $b$-bit integer $n$ coprime to $3,5,7$ and a constant $A\ge1$. On a family of twists and norm multipliers of **each individual $n$**, an unconditional deterministic calculation from the resulting index $M$ obtains the quotient

$$
\left\lfloor C(M)/2^{\lfloor(\log_2 M)/2\rfloor-t}\right\rfloor
$$

with failure proportion $O_A(b^{-A})$. The time for one index is $2^{O(t)}b^{O_A(1)}$, where $0\le t\le b$. In particular, polynomial time obtains the middle digit and any fixed multiple of $\log b$ additional leading digits on almost all members of this family. The exceptional prime twists can be chosen independently of the odd power in the reduction. The guarantee uses the following measure.

1. Put $V=2^t b^{A+10}$, $D=V^5 b^{12}$, and choose uniformly among the primes $D/2<q\le D$ congruent to $1\bmod8$ and coprime to $7!\,n$.
2. Put $a_0=3n\bmod8$ in $\{1,3,5,7\}$. Choose any $0\le h\le8b$ and set $u=a_0q n^{2h+1}F^2$. Here $F$ can be $1$ or the product of the odd primes through $b$.
3. Put $K=8\,\mathrm{bits}(u)+16$. For $s_j=1+4uj^2$, choose $j$ uniformly among the integers with $2^K\le s_j\sqrt u<2^{K+1}$ and take $M=us_j^2$.

The choices specify proportions in finite sets. Given $M,t$, the calculation itself is deterministic and receives no factorization or twist data. This addresses a different population from the [ordinary dyadic interval theorem](typical-three-square-digits.md). The adaptive last few queries of the [exact-count reduction](middle-three-square-bit.md) choose specific change points inside each family.

## Prime twists and an unconditional short Euler product

In the proof let $\chi_0$ denote the fundamental quadratic character of $-a_0\operatorname{core}(n)$, with $\operatorname{core}$ the squarefree kernel. The character of $-u$ and of $-M$ is $\chi_q=\chi_0(\cdot)(\cdot/q)$ by quadratic reciprocity. Its conductor is $O(Dn)$ with logarithm $O_A(b)$, even when $t=b$. Set $s=1+\delta$, $\delta=1/(Vb^4)$. For a dyadic cutoff $Y\ge D^2$ consider the tail

$$
 T_q(Y)=\sum_{p>Y}\chi_0(p)(p/q)p^{-s}.
$$

On an interval $H<p\le2H$, $H\ge Y$, take the coefficients $\chi_0(p)p^{-s}$ at primes and zero elsewhere. The multiplicative large sieve for primitive characters to moduli at most $D$, followed by the elementary upper bound for the prime count, gives

$$
\sum_q\left|\sum_{H<p\le 2H}\chi_q(p)p^{-s}\right|^2
\ll (H+D^2)\sum_{H<p\le2H}p^{-2s}
\ll H^{-2\delta}/\log H.
$$

The restriction to one quadratic character per prime modulus only decreases the left side. The triangle inequality for the Euclidean norm and $\sum_{i\ge1}e^{-c\delta i}/\sqrt i=O(\delta^{-1/2})$ bound $\sum_q|T_q(Y)|^2$ by $O(1/\delta)$. The fixed-progression prime number theorem gives $\gg D/\log D$ permitted primes after removing the $O(b)$ divisors of $7!n$. The fraction with $|T_q(Y)|>1/V$ is therefore $O(V^2\log D/(D\delta))$. [Montgomery and Vaughan, multiplicative large sieve](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf)

The algorithm uses $\beta=\mathrm{bits}(M)$ and the smallest power of two $Y\ge 2^{10t}\beta^{10A+130}$, taking $A$ integral by rounding it up. Since $b\le\beta=O_A(b^2)$, this cutoff is at least $D^2$. There are only $O_A(b)$ possible dyadic cutoffs as all $q,h,j,F$ vary. A union bound gives an exceptional fraction

$$
 O_A\left(\frac{b V^2\log D}{D\delta}\right)
 =O_A\left(\frac{1}{V^2 b^6}\right).
$$

For every other $q$, write $B_Y(\chi_q)=\prod_{p\le Y}(1-\chi_q(p)/p)^{-1}$. In the log Euler product at $s$, terms from prime powers $p^v$ with $p>Y,v\ge2$ cost $O(1/Y)$. Moving the finite product from $s$ to 1 costs $O(\delta(\log Y)^2)$. Consequently $L(s,\chi_q)/B_Y(\chi_q)=1+O(1/V)$ uniformly over these cutoffs. For a nonprincipal character of conductor $d$, summing through $d$ and then using partial summation with partial sums bounded by $d$ gives $|L'(w,\chi_q)|\ll(1+\log d)^2$ on $1\le w\le2$. Mertens' bound gives $B_Y(\chi_q)\gg1/\log Y$. Since $\log Y=O_A(b)$, the change from $s$ to 1 costs $O_A(1/(b V))$ relative to $B_Y$. Thus, simultaneously over the relevant cutoffs,

$$
 L(1,\chi_q)=B_Y(\chi_q)\bigl(1+O_A(1/V)\bigr).
$$

For $F$ the product of the odd primes through $b$ and $t=O(\log b)$, this also shows that almost all these prime twists amplify the normalized count beyond $1/2$ at every power. Indeed the combined Euler and conductor factors through $b$ are $\gg\log b$, the reciprocal Euler product from $b$ to $Y=b^{O_A(1)}$ is bounded below by a positive constant depending on the exponent, and remaining conductor factors are at least one. [Small-prime local product](middle-three-square-bit.md#raising-the-normalized-count-on-demand)

## Evaluation using only the padded integer

For each odd $p\le Y$ compute $v_p(M)$, $w=\lfloor v_p(M)/2\rfloor$ and $\chi_q(p)=(-M/p^{2w}\mid p)$. At 2 use $\chi_q(2)=-1$. The normalized count equals $(3/\pi)L(1,\chi_q)\prod g_w(p)$ with $g_w(p)=1+(1-\chi_q(p))\sum_{i=1}^w p^{-i}$. The omitted conductor factors have total log at most $2\beta/(Y-1)$. Replace $L(1,\chi_q)$ by the finite product $B_Y$ and use the exact local corrections at primes through $Y$. The character, its conductor and the chosen norm multiplier need not be supplied. The rational Euler factors have polynomial total bit length in $Y,\beta$. Integer square roots and a rational interval for $\pi$ give a rational approximation to the resulting count with additional relative error at most $2^{-t}\beta^{-A-12}$. Return its quotient at position $K-t$ by exact rational division. This takes time polynomial in $Y,\beta$, and hence $2^{O(t)}b^{O_A(1)}$. The Hurwitz formula implies a relative count error $O_A(1/V)$ for every good twist. [Three-square formula and effective arithmetic](typical-three-square-digits.md#a-calculation-from-the-unfactored-index)

To count wrong quotients, put $R=C(u)/\sqrt u$ and $x_j=s_j\sqrt u/2^K$. The true scaled quotient before taking its floor is $2^tR x_j$ since $C(us_j^2)=s_jC(u)$. The values of $x_j$ run from 1 to 2 on a mesh with spacing bounded above and below by absolute positive multiples of $1/L$, where $L$ is the number of permitted $j$. Indeed the real endpoints in $j$ are comparable to $2^{K/2}u^{-3/4}$, and their difference is a fixed positive fraction of that scale. Differentiating $x_j$ proves the spacing bounds. In particular $L\gg 2^{3\,\mathrm{bits}(u)}$.

For any relative approximation error at most $\epsilon<1/4$, a wrong floor requires $x_j$ to be within $O(\epsilon)$ of one of $O(2^t R+1)$ real thresholds. These intervals contain a fraction

$$
 O\bigl((2^tR+1)(\epsilon+1/L)\bigr)
$$

of the permitted indices. The elementary bound $R\ll(1+\log u)^3=O_A(b^6)$, the chosen $\epsilon=O_A(1/V)$ and $t\le b$ give the stated $O_A(b^{-A})$ failure proportion. The same bound applies after fixing any good twist and any permitted power. It also permits choosing the power as a function of the twist. [Elementary bound for the normalized count](middle-three-square-bit.md#raising-the-normalized-count-on-demand)

## What survives at the last comparisons

On a base with $R>1/2$, hypothetical counts $C(u)$ and $C(u)+g$, for any fixed positive integer $g$, give different midpoint quotients on at most

$$
 O_g\left(\frac{R+1}{C(u)}+\frac{R+1}{L}\right)=O_g(u^{-1/2})
$$

of its norm multipliers. This follows from the same threshold calculation with relative change $g/C(u)$. The statement compares integer-valued hypotheses about one count. A uniformly random pad therefore has exponentially small distinguishing probability, even within a fixed base with known norm-transfer law. The exact-count reduction deliberately bisects to those locations.

There is an explicit arithmetic example. For $n=pz$ with distinct odd primes $p\equiv2\bmod3,\ z\equiv1\bmod3$, one has $C(3n^2)=(p+2)z=n+2z$ by the fixed fundamental character of $-3$. For standard norm pads of $u=3n^2$, the inequality defining any quotient threshold $H$ is exactly $z\ge(H2^K/s_j-n)/2$. This family has known fundamental class number and a single unknown prime in the last comparison.

The actual finite Euler approximation has a second limitation on squarefree inputs. Suppose every prime factor of $n$ exceeds a common cutoff $Y$ and put $u_0=a_0 q n F^2$, $u_1=n^2u_0$, with $(a_0 qF,n)=1$. The estimated counts before numerical rounding obey $E_Y(u_1)=n E_Y(u_0)$ exactly. Their primitive characters are identical and every conductor valuation through $Y$ is identical. In contrast, the exact local factors give $C(u_1)=\sigma(n)C(u_0)$. Writing $p$ for the least prime of $n$, the two estimates therefore satisfy

$$
 \max_{i=0,1}\left|E_Y(u_i)/C(u_i)-1\right|
 \ \ge\ \frac{\sigma(n)-n}{\sigma(n)+n}
 \ \ge\ \frac1{2p+1}.
$$

Indeed, if both estimates have relative error at most $\epsilon$, their ratios force $\sigma(n)(1-\epsilon)\le n(1+\epsilon)$. The last inequality uses $\sigma(n)/n\ge1+1/p$. This holds separately at every twist, and the finite-product transfer to norm pads is exact too. Changing the prefix cutoff between the two indices changes the predictor and falls outside this identity.

For an amplified pair with both normalized true counts $R_i\ge8$, one of the two powers has wrong midpoint **quotients** on a fraction $\gg\min(1,R_i/p)-(O(R_i+1)/L)$ of its full pad interval at this common cutoff. To see this, the preceding bound gives an absolute normalized error of at least $R_i/(2p+1)$ in one row. Move the estimate toward $R_i$ until its distance $d$ is at most $1/8$. This can only shrink the set of wrong floors and leaves $d\gg\min(1,R_i/p)$. For the integers between $5R_i/4$ and $7R_i/4$, the two crossings in $x_j$ both lie in $(1,2)$, are separated by $\gg d/R_i$ and give disjoint intervals. There are $\gg R_i$ such integers. The lower mesh-density estimate proves the bound after allowing one lost mesh point per interval. For a reduced error $d\le1/8$, each discrepancy is also visible in parity. A larger original error can change a quotient by several units.

There is a separate sparsity estimate for transferring ordinary-index results. Every standard pad $M=u(1+4uj^2)^2$ in $[X,2X]$ has $u\ll X^{1/16}$ because $M\ge 2^{2K}$. At each $u$ there are $O(1+X^{1/4}u^{-3/4})$ possible $j$. Thus all the standard sweeps together occupy $O(X^{17/64})$ ordinary indices in this dyad. An error set of that size can cover the whole construction. The positive result above estimates errors using the twist and padding parameters themselves.

## Finite check

Run the [PARI/GP replay](../experiments/twisted-three-square-digits.gp) from the repository root. It uses 192 bases over $n=143,187,11^3 13^2$, three odd powers, two choices of known square multiplier, and eligible twist primes through 257. It gets the reference from the factored base and fundamental class number, with separate PARI Hurwitz checks at small indices. For each base it rounds the numerical short-product estimate to a rational with 80 fractional bits. Integer threshold endpoints count exactly the entire set of norm pads where this estimate and the reference have different quotients. The program checks that union-of-intervals calculation against 45 literal finite enumerations, and evaluates 96 padded indices directly through 450 bits to check the Euler-prefix transfer.

The table averages the wrong-quotient fraction with equal weight per tested base. It uses finite cutoffs substantially below the asymptotic prescription. Adjacent hypothesized counts have a nonempty discrepancy set on 179 of the 192 bases.

Six further prime twists of $263\cdot269$ beyond the common cutoff 257 check the exact local ratio and the relative-error lower bound $533/142027$.

| Prime cutoff | Middle quotient wrong | Quotient with two extra bits wrong |
| ---: | ---: | ---: |
| 257 | 3.3578% | 13.4181% |
| 1,021 | 1.2100% | 4.9358% |
| 4,093 | 0.6606% | 2.5470% |
