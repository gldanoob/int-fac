# Which balanced-partner guarantees follow from a count of local parameters?

Fix $P$ and its dyad of primes $\mathcal P=\{P<p\le2P\}$ of size $n$. At each $p$ suppose an unspecified set of successful parameters $J_p\subseteq\mathbb F_p^d$ is guaranteed only to have at least $\lceil\gamma p^d\rceil$ elements, $0<\gamma<1$. A deterministic search on $p q$ may choose at most $T$ labels in the local space at each of its two factors, with its successive choices allowed to depend on every preceding success or failure. It suffices here to consider an abstract test for whether a parameter is in $J_p$ or $J_q$, permitting different labels at the two factors. A single integer label reduced at both primes is a special case. A local oracle success is the only recorded witness in this model.

Let $G$ be any simple graph on $\mathcal P$ with
$$
      \deg_G(p)\,T\ \le\ p^d-\lceil\gamma p^d\rceil
           \qquad(p\in\mathcal P).
$$
There exist sets $J_p$ of precisely the prescribed sizes such that **every** pair that is an edge of $G$ misses both successful sets throughout the first $T$ probes. To prove it, run the search on each indicated input along its all-failure transcript. At a vertex $p$ collect the labels used in all the transcripts of its incident edges. Their union has size at most $\deg_G(p)T$. Choose $J_p$ in the complement. Because the local choices are fixed simultaneously at every vertex, induction on the transcript shows that each prescribed failure actually occurs. There is no assumption of independence between the two orientations or across different inputs.

For each $0\le m<n$ a circulant graph on the $n$ vertices gives all degrees at least $m-1$ and at most $m$ by taking $\lfloor m/2\rfloor$ neighbors in either cyclic direction. For odd $m$ and even $n$ one may adjoin the antipodal matching as well. Thus when $\gamma\le1-c$ and $1\ll T\ll P^d$, one may force misses on a fraction
$$
          \gg_c \min\{1,P^{d-1}\log(P)/T\}
$$
of balanced pairs, by taking $m=\min(n-1,\lfloor cP^d/(2T)\rfloor)$ and using $n\asymp P/\log P$. In particular a one-coordinate bound based only on density cannot improve the $T^{-1}$ exponent of the missed-start fraction uniformly. For $d\ge2$ and $T=P^{o(1)}$ the complete graph meets the degree condition for large $P$. A decomposition over all local curves with three moduli coordinates cannot, through its parameter count alone, certify a hit on even one balanced pair for such a search. The longer-partner result supplies more input values at fixed $p$ and follows a different count. [Three-coordinate target and parameter bound](three-parameter-genus-two.md) · [Time moments over arbitrary partner intervals](common-divisor-partners.md)

These are set-theoretic limits on deductions from local abundance. The actual elliptic and genus-two targets are specified by arithmetic, and an algorithm can also split an input through separate gcds. The argument above includes neither an arithmetic construction of those targets nor a lower bound on unrestricted factoring. The [marked-order tail](smooth-marked-order-tail.md) gives a separate arithmetic obstruction for genuinely specified rational curves in a bounded total menu.

The finite replay uses the eleven primes in $(51,102]$ and exact local targets of density at least $1/4$. In one dimension an adaptive public search over seven probes had 31 actual missed pairs including all 22 prescribed edges. In two dimensions all 55 pairs missed on all 35 probes even though every prime retained the required local density, with 16,391 local target labels in total. A base-$p$ integer encodes each point of $\mathbb F_p^2$. [Exact simultaneous construction](../experiments/partner-target-barrier.py)
