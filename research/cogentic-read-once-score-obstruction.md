# An ordered read-once width obstruction for the arithmetic score

An actual two-field smooth-relation test in the fixed Cogentic schedule has deterministic ordered read-once branching-program width $\exp(\Omega(V))$ when the program first reads one intercept word in bit order. This holds for either most-significant-bit first or least-significant-bit first. It also holds for uniform average Boolean error below $\exp(-C H)$ for a sufficiently large fixed constant $C$. The proof concerns this representation and bit order. It leaves open other input orders, repeated access, and generators specialized to the arithmetic tests.

## Distinguishing the intercept prefixes

Use the [conservative fixed schedule](cogentic-deterministic-two-thirds.md#fixed-parameters), with $\log U=(100000+o(1))V$, $\log m=(1+o(1))V$, $\log B,\log A=\Theta(H)$ and marked heights $\exp((100001+o(1))V)$. Choose a retained integer mark $a$ at which neither field has a root modulo the generator prime $\ell$. Such marks exist in any grid interval for sufficiently large inputs. The first field forbids at most $d$ residue classes modulo $\ell$, costing a fraction $O(d/\ell+d/(Aw))=o(1)$ of that interval, and the second field is root-free modulo $\ell$. The cofactor and modulus sieves remove a fraction at most $\log 2+o(1)$ by the reciprocal bound for cofactor prime divisors and the absence of primes at most $B$ dividing the surviving modulus. At this mark the affine norm in field $i$ has the form
\[
                  C_i+D(u_{i0}+a u_{i1}),\qquad D=P_0\ell(a-m).
\]
Each $C_i$ is coprime to $D$. Modulo $m-a$ the value is the corresponding fixed cofactor times $N$, which is a unit by grid selection. The polynomial is the constant one modulo odd factors of $P_0$, its binary irreducibility excludes a root at two, and the mark avoids the target-prime roots. In particular every norm is odd. [Grid and real height bounds](cogentic-deterministic-two-thirds.md#the-grid-its-sieve-and-its-real-roots) · [Local field reductions](../formal/cogentic/Cogentic/ConstructionTarget.lean#L247)

The first field's intercept interval has length $M=4UA=2^h$. Split its word after $j=\lfloor h/5\rfloor$ bits, leaving a suffix of size $T=2^{h-j}$. In the most-significant-first order the decoded intercept is $b_0+Tx+y$, where $x$ is the prefix and $0\le y<T$. In the least-significant-first order it is $b_0+x+2^j y$. Thus at a fixed slope $u_{11}$ the first marked norm is an affine function of $y$ with step $D\kappa$, where $\kappa=1$ or $2^j$ respectively. Two distinct prefixes $x,x'$ give a nonzero constant difference $\Delta=D T(x'-x)$ or $D(x'-x)$ respectively. Both choices have $\log|\Delta|=O(V)$.

For any such pair choose a prime $p\in(V^2,2V^2]$ that does not divide $\Delta$ or $D$. There are $\gg V^2/\log V$ primes in this interval and only $O(V/\log V)$ possible exclusions. The prime is odd and below $\sqrt B$, so it is forbidden in the smooth norm. Impose the unique residue class of $y\bmod p$ on which the second prefix's norm is divisible by $p$. The first prefix's norm is nonzero modulo $p$. It is also a unit modulo $|D|\kappa$ because it is a unit modulo $|D|$ and is odd. The first norm consequently runs through a unit class modulo $q=|D|\kappa p$ on this suffix progression. The second prefix fails the smoothness test on every point of it.

The first norm has constant sign throughout the original perturbation box, and its absolute height there is $X_{\rm sc}\exp(O(H))$ with a lower factor at least $\exp(-4H)/2$ relative to $X_{\rm sc}$. Apply the [individual smooth-window estimate](cogentic-dirichlet-smooth-windows.md#a-gaussian-distribution-in-progressions) at a central member $Y$ of the first norm's positive progression, with absolute width $S=|D|\kappa T/(10L_0)$. Here $L_0=L+O(1)$, $L=\log N$. The center is within $O(q)$ of the point corresponding to the middle suffix index.

For the most-significant-first order this gives
\[
 \log q=(1+o(1))V,\qquad
 \log(Y/S)=(20000+o(1))V.
\]
For the least-significant-first order one has
\[
 \log q=(20001+o(1))V,\qquad
 \log(Y/S)=\Theta(H).
\]
In the latter case $\kappa T=M$, so the original leading-height rule and the lower grid factor give $\log(Y/S)=\Omega(H)$, while the same rule gives its upper bound. In both cases $\log Y=(100001+o(1))V$, and $q\le S$. The two contour errors in the window estimate are $\exp(-\Omega(V))$. In particular even the wider frequency range of the first order has $2\log(Y/S)-\frac12\log Y=(-10000.5+o(1))V$, and the nonprincipal error has $\log q+\log(Y/S)-\frac12\log Y=(-29999.5+o(1))V$. The saddle principal factor is $\exp(-O(H))$ or larger. Omitted primes from the cofactors or the progression modulus fit the allowed bit and deletion bounds.

The normalized Gaussian sum over the progression thus has mass at least $\exp(-O(H))$. Outside the suffix interval its total mass is $\exp(-\Omega(L_0^2))$ by the Gaussian tail. Each point in the progression counts with weight at most $q/S=10L_0p/T$. Therefore at least an $\exp(-O(H))$ fraction of all $T$ suffixes make the first norm smooth and the second nonsmooth, uniformly for every slope in its box. Multiplying by the probability that the independent second field is smooth leaves the same order of lower bound. That probability is also at least $\exp(-O(H))$ by applying the same window estimate on its full intercept interval conditional on its slope, with no extra forbidden-prime congruence. Hence for the genuine relation predicate $F=I_1(a)I_2(a)$ used in the score's mass term, every pair of distinct prefix values induces suffix functions differing on at least a $\delta=\exp(-cH)$ fraction of the uniform suffix space for one fixed constant $c>0$.

## Width and approximation

Consider an ordered read-once program that reads these $j$ intercept bits first and then the remainder of the four-word input in any fixed order. If two prefixes arrive at the same state, their residual program is identical on every suffix. An exact program must therefore have at least $2^j=\exp(\Omega(V))$ states at the cut.

For a program of uniform average Boolean error at most $\delta/8$, at least half the prefixes have conditional error at most $\delta/4$, by Markov's inequality. Two such prefixes reaching the same state would have true suffix functions within $\delta/2$ of each other by the union bound, contradicting separation. Thus the width is at least $2^{j-1}$ in the approximate case as well. The same bound applies to programs with randomized local transitions under the same average error requirement, by fixing all their transition choices to a deterministic realization with at most the average error.

This rules out obtaining small width by encoding these arithmetic predicates as ordinary monotone-bit-order read-once programs. It uses the actual fixed affine norm and relation predicate, rather than a test with synthetic coefficients or an arbitrary dense success set. It supplies no bound for samplers that approximate only signed score averages, programs reading the bits in a different order, or nonuniform master advice.

As a small integer check of prefix separation, take the scalar test $1+2u\mid\prod_{\sqrt{43}<p\le43}p$ on a ten-bit word. After the first three bits each order gives eight residual rows of length $128$. Exact enumeration gives minimum pairwise Hamming distances four in the most-significant-first order and eleven in the least-significant-first order. This fixture is illustrative. The growing-width bound uses the fixed-schedule smooth-window estimate.
