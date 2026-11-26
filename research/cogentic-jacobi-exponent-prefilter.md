# A Jacobi prefilter for individual exponent searches

A deterministic search for verified individual order multiples can discard all targets with positive Jacobi symbol on every odd nonsquare input with at least two distinct prime divisors. The [dyadic prime supply estimate](cogentic-dense-exponents.md) shows that at least one quarter of all target primes still split the input once their own order multiple is supplied. For squarefree semiprimes the lower bound is three eighths. This saves about half of the candidate searches under the density hypotheses below and preserves the same asymptotic time bound.

Write $N=\prod_{i=1}^r p_i^{e_i}$, $u_i=v_2(p_i-1)$ and $s=\min_i u_i$. For a unit $a$, let $h_i$ be the 2-adic valuation of its order modulo $p_i$. The valuation is identical modulo $p_i^{e_i}$ since the reduction kernel has odd order. Given any verified $a^E=1\bmod N$, raise $a$ to the odd part of $E$ and scan the gcd of each successive square minus one with $N$. The scan splits $N$ exactly when the $h_i$ differ. If they differ, the first time a local component becomes one yields a proper gcd. If they agree, each power before all components become one has gcd one, and all components become one at the same step.

The local Legendre symbol of $a$ is $-1$ exactly when $h_i=u_i$. If the scan fails, the common height $h$ satisfies $h\le s$. Its Jacobi symbol is positive when $h<s$. When $h=s$, the Jacobi symbol is $(-1)^c$, where
\[
c=\sum_{i:u_i=s}e_i .
\]
Consequently every negative-Jacobi unit with a verified order multiple splits exactly when $c$ is even. When $c$ is odd, CRT gives failed negative-Jacobi units of common height $s$. The same criterion for a quadratic character $\prod_i(\cdot/p_i)^{c_i}$ replaces $e_i$ by $c_i$. Expanding $N=\prod_i p_i^{e_i}$ modulo $2^{s+1}$ also shows $v_2(N-1)\ge s$, with equality precisely when $c$ is odd. A failed scan on a negative-Jacobi target therefore determines $s=v_2(N-1)$ from public data.

## Density on the prime target interval

Suppose $c$ is odd. In each local cyclic unit group the elements of height exactly $s$ form one coset of the subgroup of elements of height at most $s-1$. Thus all failed negative-Jacobi units form one coset of a subgroup $H$ in $(\mathbb Z/N\mathbb Z)^\times$, with
\[
[G:H]=2^{r+\sum_i(u_i-s)} .
\]
The indicator of any coset of $H$ has a Dirichlet character expansion with coefficient absolute sum one, by orthogonality on $G/H$. Under the uniform Dirichlet RH estimate in the [dense exponent note](cogentic-dense-exponents.md), the dyadic average of this indicator over primes is $1/[G:H]+o(1)$, uniformly in $N$, whenever $B/\log^2 N\to\infty$. The primes dividing $N$ have negligible proportion. The Jacobi character is nonprincipal since $N$ is nonsquare, so its negative sign has average $1/2+o(1)$.

The proportion of targets guaranteed to split upon receiving their exponent is therefore
\[
\begin{cases}
1/2+o(1),&c\text{ even},\\
1/2-2^{-r-\sum_i(u_i-s)}+o(1),&c\text{ odd}.
\end{cases}
\]
The lower bound is $1/4-o(1)$ for $r\ge2$. For a squarefree semiprime with odd $c$ the valuations differ, so the lower bound becomes $3/8-o(1)$. This proof uses the hidden primes to count witnesses. The search checks only the publicly computable Jacobi symbol, runs the relation search on negative targets, verifies each supplied exponent, and tests the squaring chain. A zero Jacobi symbol can be handled by a gcd at the outset. With more than $3/4+\delta$ of all targets supplying verified exponents for fixed $\delta>0$, some negative target is productive for every sufficiently large surviving input. In particular the $1-o(1)$ supply of the existing deterministic schedule suffices. The condition would need to be re-established for any proposed one-third schedule.

## What the symbols distinguish

On arbitrary units, the full menu of individual Legendre symbols determines the local heights whenever every $u_i=1$. If some $u_i>1$, the involution with $-1$ only at that component is itself a square modulo $N$. Every quadratic character agrees on it and on the identity, while their gcd scans differ. Ordinary Jacobi on the involution sees only those negative branches with $p_i\equiv3\pmod4$ and odd $e_i$.

For an evaluable involution $z$, the affine challenge
\[
 J_z(t)=\left(\frac{((t+1)+(t-1)z)/2}{N}\right)
\]
with $t$ a unit and division in $\mathbb Z/N\mathbb Z$ equals the product of the Legendre symbols of $t$ at the positive branches with odd $e_i$. Two signatures differ exactly when their sign vectors differ at an odd-exponent branch. The ratio then defines a nonprincipal character modulo $N$, and under Dirichlet RH Bach's bound supplies a coprime prime $t\le 3\log^2 N$ distinguishing the signatures. All the challenges are public given $z$. Direct gcd is cheaper when $z$ is given, and obtaining the signature by this formula from square identities still requires the root ratio. [Bach's explicit bound](https://doi.org/10.1090/S0025-5718-1990-1023756-8)

Restricting the probes to $t$ with $\left(\frac{t}{N}\right)=1$ gives characters on $\mu_2(\mathbb Z/N\mathbb Z)/\{1,-1\}$. Changing all signs replaces the positive branch product by its complement with the same value. The combined signature distinguishes precisely the sign vectors whose difference, read on the odd-exponent branches, is neither empty nor the full odd-exponent set. Indeed the corresponding quadratic character of $t$ restricts trivially to the Jacobi kernel exactly when it is principal or equals the Jacobi character. On squarefree $N$ this separates every pair of distinct sign classes.

An explicit fixed menu suffices under Dirichlet RH. Collect the coprime integers up to $3\lceil\log_2 N\rceil^2$. They generate the unit group because Bach's bound gives a coprime witness outside any proper subgroup within this cutoff. Use the positive-Jacobi entries as probes and, if there is a negative entry $b$, use each negative entry multiplied by $b$, including $b^2$. The resulting probes generate the Jacobi kernel, since every negative generator can be written as a probe times $b^{-1}$ and a kernel word has even total exponent of $b$. There are $O(\log^2 N)$ probes of size $O(\log^4 N)$ before reduction. Thus the same menu works for all the root ratios from a supplied square-relation basis. This computes the detectable sign image from affine symbols of the reduced roots. It leaves open the supply of relations with a nontrivial image.

The [finite replay](../experiments/cogentic-jacobi-exponent-prefilter.py) checks the density formula among units, the common-height criterion, and the affine signatures on 29,160 units in 147 odd moduli up to 512 with at least two distinct prime divisors. It supplies true order multiples from known factors to exercise the modular postprocessing.
