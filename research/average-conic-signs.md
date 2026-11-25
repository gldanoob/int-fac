# Quadratic signs for the elliptic search on average

The deterministic [mean-time factoring bound](mean-time-elliptic-factoring.md) follows from proved ordinary RH and the classical multiplicative large sieve. The proof replaces a least-prime-in-a-coset step with a larger, explicitly enumerable list of rational conics. All failures of the new list can be charged to the actual factorial-search cost. The original [pointwise theorem](pointwise-conic-marks.md) gives a polynomial-size list for every pair with Dirichlet GRH.

## A small exceptional list of characters

Fix a cofactor bit length and a common dyad parameter $X$, with every cofactor $d\le 2X$. Write $L=\log(2X)$, $B=\sqrt{L\log(2L)}$, take $R=\lceil e^B\rceil$ and $S=R^4$. For $U=R,S$ write $I_U=\{r\in(U,2U]:r\text{ prime},\ r\equiv1\pmod 8\}$, and $M_U=|I_U|\asymp U/\log U$ by the prime number theorem for the fixed modulus 8. Set $\eta=1/32$.

For any fixed coefficients $|w_r|\le1$ on $I_U$, the number of primitive characters of conductor at most $2X$ for which
$$
                    \left|\sum_{r\in I_U}w_r\chi(r)\right|>\eta M_U
$$
is at most $\exp(O(B))$. To see this take $k=\lceil2\log(2X)/\log(2U)\rceil$. On raising the sum to the $k$-th power its coefficients $a_n$ vanish beyond $(2U)^k$. Unique factorization implies $\sum|a_n|^2\le k! M_U^k$, since any ordered prime tuple has at most $k!$ others with the same product. The multiplicative large sieve bounds the number of exceptions by
$$
 \frac{((2X)^2+(2U)^k)\,k! M_U^k}{(\eta M_U)^{2k}}
 \ll \big(C\eta^{-2} k\log U\big)^k.
$$
With $k=O(L/B+1)$ its logarithm is $O(B)$. This argument even gives a direct first-moment exception estimate on the larger prime range for the much smaller conductor cutoff $2R$. With $k=1$ at $U=S$, at most $O(\log S)$ primitive characters of conductor $\le2R$ exceed the same threshold. [Montgomery and Vaughan, multiplicative large sieve](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf) · [Koukoulopoulos, Theorem 25.15](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf)

At conductor cutoff $2X$ take the union of exceptions for unit weights on each range and for $w_f=(f/e)$ on $I_S$ for every $e\in I_R$. These at most $2+M_R$ lists still give $\exp(O(B))$ characters. At the smaller cutoff call an auxiliary prime $e\in I_R$ unsuitable when $|\sum_{f\in I_S}(f/e)|>\eta M_S$. There are $O(\log S)$ unsuitable primes. All exception lists are used only in the proof.

## Obtaining the conics

Take distinct odd primes $p,q\mid d$ exceeding $2S$, and assume none of $\chi_p$, $\chi_q$ and $\chi_p\chi_q$ is in the large exception set. Their conductors are $p,q,pq\le2X$. Given $s=\pm1$, expand the two sign indicators over $I_R$. The conditions $(e/p)=s$ and $(e/q)=1$ hold for at least $(1-3\eta)M_R/4$ candidates. After discarding the unsuitable primes at least one $e$ remains. Over $I_S$ expand the three signs $(f/p)=s$, $(f/q)=-1$ and $(f/e)=1$. Their seven nonconstant character sums have absolute value at most $\eta M_S$ by construction. Consequently at least $(1-7\eta)M_S/8$ choices of $f$ qualify. In particular both signs supply distinct auxiliary primes with the same local specifications as the pointwise argument.

The public algorithm can enumerate all rationals up to height $R^{C_0}$ for a fixed absolute $C_0$. Indeed Holzer's bound on $w^2+fv^2=eu^2$ gives a primitive solution with $0<|u|\le\sqrt f$, $0<|v|\le\sqrt e$, $0<|w|\le\sqrt{ef}$. Thus $c=e(u/w)^2$ has height at most $ef\le4RS$ and $c-1=f(v/w)^2$. The preliminary small-factor cutoff can exceed $4RS$, so all these coordinates are units at the retained primes. Other prime factors dividing an auxiliary coefficient or a denominator can be detected by gcd as usual. Enlarging the cutoff to exceed all cross-differences between the first $H$ marks still costs $\exp(O(B))$. The conic parametrization has fixed degree and height polynomial in the input heights and $H$. Both the total public menu size and the number of pairs of conics used in the missed-start union are now $\exp(O(B))$. These factors fit the existing stage-cost estimate.

## Paying for every missing pair

For a cofactor $d$ reaching the curve stage take its least prime $p$ and any distinct prime $q\mid d$. Charge the factorial search, of cost $\sqrt p\,\mathrm{poly}(L)$, whenever the chosen pair fails the character conditions above. There are three possible charges, each summed over multiples in $X<d\le2X$. A prime $p$ whose primitive character is exceptional contributes normalized cost $O(1/\sqrt p)$, before the common polynomial factor. For an exceptional prime $q$, summing over $p\le q$ costs
$$
               O\!\left(\frac1q\sum_{p\le q}\frac1{\sqrt p}\right)
                 = O(1/\sqrt q).
$$
An exceptional product character determines its conductor $pq$ and hence a unique unordered prime pair. Its charge is $O(\sqrt p/(pq))$. Here $\#\{d\in(X,2X]:pq\mid d\}\le 2X/(pq)$ even near the end of the dyad. Thus the total charge is $\exp(O(B))$ in the mean. Primes and prime powers are recognized before this argument. The successful cases use the ordinary-RH exceptional Hasse count and binary sampling in the mean-time proof. The same charge applies unchanged to that proof's recursive divisor sum and after polynomial renormalization to balanced prime pairs.

The replay compared 758 two- and three-sign expansions with direct counts, checked 160 high-moment identities from ordered tuples and verified 378 rational witnesses from disjoint prime ranges of sizes 20 and 56. [Exact replay](../experiments/average-conic-signs.py)
