# An exact progression-index sieve for short scalar divisor counts

Let $J\subseteq(\sqrt B,B]$ be an explicit set of primes, and consider
\[
 C_J(c,d,T)=\#\{0\le j<T:c+dj\ne0,\ |c+dj|\text{ is a squarefree product of primes in }J\}.
\]
There is an exact algorithm taking
\[
 \operatorname{poly}(w)\left(\pi(B)+T\log\log(3B)+T\frac{w}{\log B}\right)
\]
bit operations, where $w$ bounds the bit lengths of $B,c,d,T$ and all progression values. In particular, it improves the naive per-value trial division cost $T\pi(B)\operatorname{poly}(w)$ by replacing the multiplicative $T\pi(B)$ scan with a progression sieve. If $T=\exp(O(H))$ and $B=\exp(O(H))$, this is still within $\exp(O(H))$; it handles the short-progression part of the scalar problem exactly and without dependence on a requested precision. It does not address the unresolved range $T=\exp(\omega(H))$.

If $c=d=0$, return zero immediately. Otherwise initialize residuals $r_j=|c+dj|$ and squarefree flags. For each $p\in J$, solve $c+dj\equiv0\pmod p$. If $p\nmid d$, this is one class $j\equiv j_p\pmod p$, so only indices in that class are inspected. If $p\mid d$, there are either no indices (when $p\nmid c$) or all indices (when $p\mid c$). At each inspected nonzero residual divisible by $p$, divide it once by $p$ and mark the flag false if it remains divisible by $p$. At the end accept exactly when the original value was nonzero, the residual is $1$, and the flag is true.

Every allowed prime factor is removed once, and a repeated allowed factor leaves a nonunit residual as well as setting the flag. A forbidden or omitted prime is never removed, so it also leaves residual greater than one. Hence acceptance is equivalent to the stated squarefree $J$-smoothness condition. Zero is explicitly excluded.

For $p\nmid d$, at most $T/p+1$ indices are inspected. Summing over $p\in J$ costs $O(T\sum_{p\le B}1/p+\pi(B))=O(T\log\log(3B)+\pi(B))$. Primes dividing both $c$ and $d$ inspect all $T$ entries, but there are at most $O(w/\log B)$ such primes because each exceeds $\sqrt B$; the exceptional pair $c=d=0$ was handled before this loop. Primes dividing $d$ but not $c$ inspect none. All residual arithmetic uses $O(w)$-bit integers, giving the displayed bit bound after polynomial overhead. The eligible list $J$ is input explicitly. If it must be generated as all band primes, Eratosthenes costs $O(B\log\log B)$, which is $O(\pi(B)\operatorname{poly}(w))$ by $\pi(B)\asymp B/\log B$ and $w\ge\log B$.

The replay compares this algorithm with independent trial factorization on 506 signed, zero, constant, nonunit-step and omitted-prime cases. A longer case records the number of progression-index visits against the naive value-by-prime loop. Run `python3 experiments/cogentic-scalar-progression-sieve.py`.
