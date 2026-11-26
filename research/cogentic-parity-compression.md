# A parity summary does not preserve arithmetic score tests

The arithmetic test class used by the coefficient-word construction cannot in general be evaluated from the parity of the input bits alone, even for one affine norm and one band prime. This rules out the specific compression that replaces a coefficient word by its total parity while claiming exact preservation of every score test. It does not rule out a pseudorandom generator or other restricted-class compression.

Take two bits $x_1,x_2$, the affine norm $n(x)=1+x_1+x_2$, and the allowed prime set $J=\{2\}$. The smoothness indicator accepts exactly the squarefree products of primes in $J$, namely $|n|\in\{1,2\}$. Its truth table is

| word | parity | norm | accepted |
|---|---:|---:|---:|
| 00 | even | 1 | yes |
| 01 | odd | 2 | yes |
| 10 | odd | 2 | yes |
| 11 | even | 3 | no |

The two words in the even parity fiber receive different answers. Therefore no function of total parity alone can agree pointwise with this permitted arithmetic test. Moreover, the uniform acceptance probability is $3/4$, while the uniform distribution on the even-parity support has acceptance probability $1/2$: this support restriction changes the test mean by $1/4$.

This is a finite obstruction to parity-only compression, not an asymptotic lower bound on seed length. It also does not establish that parity compression would fail after cancellation in the full signed score; the claim is only about preserving the individual nonnegative tests used in its expansion.

## Asymptotic bias for modular predicates

There is a useful positive result for the modular part of the test class. Let $X$ be uniform on $\{0,\ldots,2^k-1\}$, and condition on its binary digit sum being even. Write $\tau(x)=(-1)^{s_2(x)}$. For every modulus $q\ge1$ and residue $r$, the conditional probability of $X\equiv r\pmod q$ differs from its unconditioned probability by at most
\[
                 \left(\frac{4}{3\sqrt3}\right)^{\lfloor k/2\rfloor}.
\]
Indeed the even-parity indicator is $(1+\tau(x))/2$, and $\sum_{x<2^k}\tau(x)=0$ for $k\ge1$. The conditional bias is therefore exactly
\[
  2^{-k}\left|\sum_{x<2^k}\tau(x)1_{x\equiv r\ (q)}\right|.
\]
By additive-character orthogonality, this is at most $2^{-k}q^{-1}\sum_{a\bmod q}|\prod_{j=0}^{k-1}(1-e(a2^j/q))|$, hence at most $2^{-k}\max_{a\bmod q}|\prod_{j=0}^{k-1}(1-e(a2^j/q))|$, where $e(t)=e^{2\pi i t}$. Pair consecutive factors and use
\[
 |(1-e(t))(1-e(2t))|=4|\sin(\pi t)\sin(2\pi t)|\le\frac{16}{3\sqrt3}.
\]
An unpaired factor is at most $2$. Thus the bound is $\rho^{\lfloor k/2\rfloor}$, where $\rho=4/(3\sqrt3)<1$. Since the interval $\{0,\ldots,2^k-1\}$ is not always equidistributed modulo $q$, its unconditioned residue probability can differ from $1/q$ by at most $2^{-k}$; consequently the conditional probability differs from $1/q$ by at most $\rho^{\lfloor k/2\rfloor}+2^{-k}$.

The same bound controls any conjunction of affine modular predicates in the word, with arbitrary integer coefficients and constants. For one predicate $c+dx\equiv a\pmod q$, put $g=\gcd(d,q)$. If $g\nmid(a-c)$ the solution set is empty. Otherwise it is one residue class modulo $q/g$; the case $q/g=1$ is the whole set and has zero bias. Intersect several predicates successively: each nonempty intersection is either empty or a single residue class modulo the lcm of their reduced moduli, so the same estimate applies. This also handles a binary coefficient-word offset: if the tested integer is $c+d(b+x)$ for a fixed offset $b$, replace $a-c$ by $a-c-db$ in the solvability test. No invertibility assumption on $d$ is used.

For $k\asymp V$, $\rho^{\lfloor k/2\rfloor}=\exp(-c_0k+O(1))=\exp(-\Omega(V))$, where $c_0=\tfrac12\log(3\sqrt3/4)>0$. Since $V/H\to\infty$, this is below $\exp(-CH)$ for every fixed $C$ once the input is large enough. Thus conditioning on one parity bit suffices for the modular factors' requested exponential accuracy, while only saving one seed bit; the affine smoothness indicators above still distinguish points within a parity fiber, so this does not solve the smoothness part.

Run `python3 experiments/cogentic-parity-compression.py` to enumerate the four-word smoothness obstruction and verify the modular bias bound by exact integer counts for small $k,q,r$.
