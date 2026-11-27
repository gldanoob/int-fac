# Sparse dependency extraction and a 2.155 schedule

For a single integer from scratch the joint private/public elliptic schedule admits a manuscript-level expected bit bound $L_N[1/3,2.155]$ under the same Dirichlet GRH and pinned KeyBreak inputs. The final matrix needs one verified nonzero binary dependency. Storing only its nonzero entries and using a sparse Krylov procedure reduces the linear-algebra coefficient from $2.4b$ to $2b$. The new limiting terms are the raw trials at the bottom of the descent and the private screening stages. [Public elliptic descent](keybreak-public-elliptic-recognition.md) · [Previous one-input schedule](keybreak-private-elliptic-schedule.md)

## The sparse matrix and its kernel

Write $C$ for the public bound on the number of parity and character columns, and collect $C+1$ rows without a rank test. Transpose these records, add zero padding for unused columns, then append one zero row to get a singular square binary matrix $M$ of size $s=C+1$. Repeated indices within a row are canceled by parity. The number of field elements and prime incidences in each completed tree is $\exp(o(H))$ where $H=(\log N)^{1/3}(\log\log N)^{2/3}$. In particular the depth is $O(\log\log N)$, each point has only polynomially many factors in the input bit length, and the **compressed** character output has polynomial length even for the cumulative sampler. Consequently $s=\exp((b+o(1))H)$ and the total stored support is at most $\exp((b+o(1))H)$. One need never store a dense square array. [KeyBreak (H.22) and (H.30)](https://crypto.sjtu.edu.cn/factoring.pdf#page=140) · [Compressed characters](keybreak-cumulative-character-probes.md)

Use $K=\mathbf F_{2^h}$ with $4s<2^h\le8s$. The bit length of each field element is $O(\log s)$. Enumerating at most $2^h$ candidate moduli and testing irreducibility by modular Frobenius and polynomial gcd costs $s\operatorname{poly}(\log s)$ bits up to constant factors. Draw uniform independent $u,v\in K^s$. Generate the first $2s$ values of $u^TM^iv$ and recover the scalar minimal recurrence using Berlekamp–Massey. If its polynomial $P$ is divisible by $t$, evaluate $z=(P/t)(M)v$ using Horner's rule. Verify $z\ne0$ and $Mz=0$, expand the coordinates in the binary basis and verify a nonzero binary component against the original rows. Repeat a fixed bounded number of times and fail the epoch on exhaustion. A sparse linear dependency procedure of this type is due to Wiedemann. [Wiedemann, *Solving sparse linear equations over finite fields*](https://www.enseignement.polytechnique.fr/informatique/profs/Francois.Morain/Master1/Crypto/projects/Wiedemann86.pdf)

For the success probability, $v$ misses the nilpotent summand in the Fitting decomposition with probability at most $1/|K|$, since $M$ is singular. Otherwise its vector minimal polynomial $m_v$ is divisible by $t$. For each distinct irreducible $f\mid m_v$ the vector $(m_v/f)(M)v$ is nonzero by minimality. If the scalar recurrence loses a copy of $f$, its polynomial divides $m_v/f$ and therefore $u$ annihilates that nonzero vector. The union bound over at most $s$ irreducibles loses at most $s/|K|$; the $2s$ terms suffice by the linear complexity bound. On the remaining event $P=m_v$, so $z$ is nonzero and lies in the kernel. At least one binary coordinate is nonzero and every binary component is killed by $M$, whose entries are binary. This works for arbitrary nullity and arbitrary Jordan blocks at zero. A fixed number of fresh attempts makes the total failure probability less than $1/128$. The random probes and verified dependency are public before the hidden roots are used.

For each matrix-vector multiply, sort/merge support records by column with the vector and accumulate the contributions by row, using sequential external merge sorts. A pass costs $\exp((b+o(1))H)$ bit operations even on multitape machines. At most $O(s)$ passes are needed. The recurrence discrepancies and coefficient updates in Berlekamp–Massey admit direct sequential scans of the saved prefix and polynomials (including a reverse-order sequence tape); $O(s^2)$ field operations and sequential index moves suffice. A final sparse pass verifies the dependency. Thus the full bound is $\exp((2b+o(1))H)$ including field construction, vector copies, randomness and failure checks. The [Python implementation](../experiments/keybreak-sparse-dependency.py) exercises these exact finite-field operations on small matrices. Its default PRNG is for reproducible experimentation when seeded; the proof uses independent uniform bits.

## Integer schedule and leading terms

Keep the finite rules of the [elliptic schedule](keybreak-private-elliptic-schedule.md). Set
$$
 \delta=1.36245,\quad\kappa=.79414,\quad\beta=.667731,\quad
 \alpha=.500005,\quad\gamma=.684287,\quad h_T=.644358.
$$
Use $\lambda_T(a)=1+.78a$, $\lambda_H=1.97$, $\lambda_L=2.149294$, and $1024$ private groups with $z_j=.026+.974j/1023$ and $a_j=z_j^2$. The first private floor is $.00067e_0$, rounded up as before. The curve coefficient allowance for both private and public tests is $.785005>1.4143/\sqrt{3\kappa\delta}$. Use cap slack $.000005$ and require a bottom absolute mean of $\exp(.00002\Lambda_d)$. All are fixed positive margins. In G.10 the previous diagonal estimate applies for every fixed positive mean exponent. The actual height coefficient is $.644353434\ldots$, the low fixed-point margin is $.000003750\ldots$, the bottom mean coefficient is $.000029020\ldots$, and the private factor-count ratio is below $1.698$ against the cap of two. The proof of the band estimates needs only finitely many fixed separated groups; increasing their count to 1024 changes no asymptotic union step.

| Work on this input | Coefficient, rounded up |
|---|---:|
| Private elliptic screening | 2.154788 |
| Low raw descent trials | 2.154790 |
| Top algebraic testing | 2.134201 |
| High raw descent trials | 2.097146 |
| Character setup and retained evaluations | 0.908300 and 1.818051 |
| Sparse dependency and exact extraction | 1.819501 each |

The [arithmetic replay](../experiments/keybreak-sparse-schedule.py) checks the upper bound and rounded guards at two symbolic input sizes, including every group and all high/low transitions. The square-congruence extraction and both elliptic recognition arguments retain the analytic assumptions stated in the previous schedule. The exact finite computations do not test asymptotic runtime.

## How close the schedule is to its cost floor

For one integer with all setup charged, a finer set of private cutoffs gives a conditional expected bit bound of $L_N[1/3,2.154631]$ in the same manuscript analysis. The private tests and terminal raw search contribute 2.154630710 and 2.154630718 respectively, rounded to nine decimals. A Lean theorem excludes a joint budget at or below 2.154630 under the current private and terminal cost constraints. Thus these two terms alone leave less than one millionth between the model floor and the exhibited budget. The theorem concerns this particular way of collecting relations. A different relation supply or field height can change the constraints. [Schedule and exact arithmetic](../experiments/keybreak-sparse-schedule.py) · [Lean upper certificate](../formal/cogentic/Cogentic/RandomizedSparseSchedule.lean) · [Lean lower certificate](../formal/cogentic/Cogentic/RandomizedEndpointFloor.lean)

Use 262144 fixed groups from $z=.002$ to $z=1$, with uniform spacing in $z$ and weight $h$ times the spacing on each interior group. The last group absorbs the remaining second moment. All per-curve and curve-count allowance coefficients can be made arbitrarily close to $1/\sqrt{2}$ from above under the previous elliptic argument. For this schedule take .707106783 and .707106784, whose sum is strictly below 1.41421357. The two-sided elliptic allowance in private cutoff units is .7848525113. The smallest mean and box margins remain strictly positive. The exact replay checks the leading guards across all 262144 groups. A separate integer certificate checks positive allocations, disjoint bands, local box guards and the factor-count ceiling on the fine grid whenever the binary length of the input bit length is at least 789082. It uses rational inequalities without materializing an integer of that size. [Fine-grid rounding certificate](../experiments/keybreak-private-grid-rounding.py)

The 3072-group version also checks the rounded integer schedule at two symbolic bit lengths and achieves 2.15468. For fixed group count, neighboring cutoff gaps have fixed positive relative size, while the relative width needed by the private allocation tends to zero. Constants in the finite union and confidence bounds can depend on that fixed count. [Elliptic recognition proof](keybreak-private-elliptic-recognition.md) · [Integer descent rules](../experiments/keybreak-tiered-descent.py)

For the lower certificate, put $x=\kappa\delta$, let $u=\sqrt{2/(3x)}$ be the ideal private curve coefficient, and write $C$ for the proposed budget. With endpoint one, the private moment is $2x/3=4/(9u^2)$. Summation by parts gives $b+4/(9u^2)+2u/3\le C$. Eliminating the last box dimension and ratio from the height, mean and raw-search constraints gives $3u^2/2+4/\delta+C\delta\le6b(C-b)$. At $C=2.154630$ exact rational supporting inequalities make the two conditions contradictory for every $b,\delta,u>0$. For a grid ending at $Z>0$, divide each cutoff coordinate by $Z$ and multiply its curve coefficient by $Z$. The gate costs stay equal and the physical height bound uses $x/Z^2$, so the same obstruction applies. [Finite summation proof](../formal/cogentic/Cogentic/RandomizedPrivateFloor.lean) · [Terminal elimination and rational certificate](../formal/cogentic/Cogentic/RandomizedScheduleFloor.lean)

Run `make check-randomized-lean` with the pinned Lean toolchain. The build checks the cost inequalities and finite algebra, including how a mixed CRT sign gives a proper gcd for an odd modulus with at least two distinct prime factors. The analytic prime supply, distribution of the sampled relations, and full expected bit-time theorem remain manuscript arguments. [Combined Lean target](../formal/cogentic/RandomizedFactoring.lean)

## Exact limiting coefficient

Let $u$ be the unique root in $(.78485210451994876996,.78485210451994876997)$ of
$$
455625u^{18}+1181952u^{12}-1092096u^9-663552u^6+294912u^3+65536=0.
$$
The limiting coefficient in this schedule model is
$$
C_* = \frac{225u^6-96u^3-128}{36u^2(3u^3-4)},\qquad
2.15463021529917670<C_*<2.15463021529917672.
$$
Lean proves existence and uniqueness on this interval, the enclosure of $C_*$, and the impossibility of a smaller budget for every finite private grid with its physical field height charged. [Root isolation](../formal/cogentic/Cogentic/RandomizedAlgebraicRoot.lean) · [Combined lower bound](../formal/cogentic/Cogentic/RandomizedOptimalCost.lean)

Here is how the root arises. Write $p(u)=4/(9u^2)+2u/3$. At the limiting optimum $b=C_*-p(u)$, $\delta=2/\sqrt{C_*}$ and the two active cost constraints give $6b(C_*-b)=3u^2/2+4\sqrt{C_*}$. Their tangent slopes satisfy $6(C_*-2b)p'(u)=-3u$. Eliminating $b$ and the square root yields the polynomial above. The root gives the desired sign before squaring. For any positive trial scale $v$, the tangent to $1/v^2$ at $u$ is a lower bound. The tangent to $6b(C_*-b)$ is an upper bound and $4/\delta+C_*\delta\ge4\sqrt{C_*}$. These three inequalities give the global supporting inequality. [Lean supporting inequality](../formal/cogentic/Cogentic/RandomizedStationaryFloor.lean) · [Exact Sage calculation](../experiments/keybreak-sparse-limit.py)

The limiting value can be approached by finite schedules. Set $\kappa=2/(3u^2\delta)$, $\beta=b/\delta$, and choose $\alpha=1/2+\eta$ for fixed $\eta>0$. Take $h_T=(1+\alpha/\kappa)/\delta^3+\eta$. Set
$$
\lambda_L=\frac{\beta+2h_T+1/(3\delta^3\beta)+4\eta}{2\beta-1/3},
\qquad
S=\lambda_L-(h_T+\eta)/\beta,\qquad \gamma=S-\alpha .
$$
The terminal box margin is then $\eta$ and its mean margin is $2\eta$. At $\eta=0$ both active costs equal $C_*$. Every other work coefficient is strictly below 2.14 at the limit and the other geometric constraints have strict room. At the top, the positive perturbation supplies $2\alpha>1$. For local top cutoffs, the G.17 error expression increases with the squared cutoff on $[0,1]$, so its value at one controls the whole grid. [Exact limit checks](../experiments/keybreak-sparse-limit.py)

Take a private first knot tending to zero, a mesh tending to zero, a positive curve-work allowance tending to $\sqrt 2$ from above, and cap slacks tending to zero. The interior weighted sum tends to $u\int_0^1z^2\,dz=u/3$, so the terminal weight tends to $4/(9u^2)-u/3>0$. The limiting factor count divided by its basic scale is $p(u)/(4/(9u^2))<2$. For any fixed positive tolerance, choose the parameters in this order and approximate them by rationals inside the strict inequalities. Each resulting schedule has finitely many fixed positive bands, with positive separation and positive allocated fractions before the input grows. The established rounding and analytic arguments therefore apply to each member separately. This gives, under the same manuscript hypotheses, a fixed schedule below $C_*+\varepsilon$ for every $\varepsilon>0$.

A single algorithm can realize this infimum in the leading exponent. Effectively enumerate the rational schedules, retaining integer verification of every returned proper divisor. In doubling phase $t$, run fresh copies from the start, allocating schedule $j\ge1$ at most $2^{t-j}$ simulated steps for $j\le t$. Parameter generation, setup and divisor checks count inside these budgets. Every accepted split is verified by division, and recursion with a primality test yields the complete factorization with polynomial overhead. Any fixed valid schedule of expected work $E$ receives at least $4E$ steps from phase $\lceil\log_2(4E)\rceil+j$ onward. Markov's inequality bounds its failure in each fresh phase by $1/4$. The remaining expected work is bounded by a convergent geometric sum. Standard multitape simulation and phase bookkeeping add at most polynomial factors in the input length and logarithm of the work. Thus each fixed valid schedule bounds the leading exponent of the same algorithm, giving a manuscript-level expected bound $L_N[1/3,C_*]$ for one input under the stated assumptions. The Lean target checks the restart arithmetic. The construction of the universal machine and the analytic factoring theorem remain outside it. [Restart bound](../formal/cogentic/Cogentic/RandomizedRestartBudget.lean)

## What an improvement below ordinary GNFS would have to change

The terminal box alone gives a useful comparison. Give private sampling zero cost and remove the Gaussian height overhead, leaving the radix contribution $h_T\ge1/\delta^3$. Under the original rational proposal cost and the terminal mean requirement, elimination of the box and slope gives
$$
4/\delta+C\delta\le6b(C-b)\le 3C^2/2.
$$
The left side is at least $4\sqrt C$, so $9C^3\ge64$. Equality in this relaxed inequality occurs at $b=C/2$ and $\delta=3C/4$. This recovers the ordinary GNFS heuristic coefficient $(64/9)^{1/3}=1.922999427\ldots$ as a lower bound for this particular proposal and mean calculation. The statement applies to one-input terminal searches satisfying these constraints. [Lean theorem and equality case](../formal/cogentic/Cogentic/RandomizedRelaxedCosts.lean) · [Buhler, Lenstra and Pomerance, *Factoring integers with the number field sieve*](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1993e/art.pdf)

Restoring the private gate cost strengthens the obstruction. Let $\theta$ be the fraction of the excess height retained and $\rho$ the fraction of rational trial work retained, both between zero and one. Keep the population constraint in the original box. The terminal necessary inequality becomes
$$
\frac32\theta u^2+\frac{2(1+\rho)}\delta+\frac{1-\rho}{3b}+C\delta\le6b(C-b).
$$
With $(\theta,\rho)=(0,1)$, the private and terminal rows exclude $C=1.94548659$. With $(1,0)$ they exclude $C=1.95$. Consequently speeding up either operation alone within this model cannot reach 1.923. The terminal mean and the number of expensive rows charged here are both assumptions that a new relation collector could change. [Radix-only certificate](../formal/cogentic/Cogentic/RandomizedRadixFloor.lean) · [Free rational proposal certificate](../formal/cogentic/Cogentic/RandomizedFreeRationalFloor.lean)

The [public-span calculation](keybreak-public-span-schedule.md) specifies the residual rank and preparation cost that would put a different one-input schedule below 1.923. Its public relation supply remains open.
