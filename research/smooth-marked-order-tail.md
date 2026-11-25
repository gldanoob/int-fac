# How many rational elliptic curves can supply a smooth marked order?

Put $L=\log X$, $Y\ge2$, and $u=L/\log Y\to\infty$. Fix $A>0$. Let $E/\mathbb Q$ be an elliptic curve given by a rational Weierstrass equation, and $R\in E(\mathbb Q)$ an infinite-order point. Bound the logarithmic heights of its coefficients and affine coordinates by $L^A$. Both $E$ and $R$ can vary with $X$. At a uniformly chosen prime $X<p\le 2X$ the probability of bad reduction, or that the order of $R\bmod p$ divides a $Y$-smooth integer times **any integer at most $X^{1/8}$**, is
$$
\ll_A \exp[-c u\log(2u)]+X^{-c_A}
$$
for constants $c,c_A>0$. The proof uses the uniform Dedekind-zeta strip of Cureton and Thorner. For CM curves a classical Hecke Brun–Titchmarsh alternative is given below. The bound includes scalar tests with a single second-stage prime up to $X^{1/8}$, and arbitrary powers of small primes. [Cureton–Thorner, Theorem 1.1](https://hexagonmath.org/pdf/2610.00200v2#page=3)

Consequently, any menu of $K$ such rational marked curves has an annihilation at either factor on a fraction at most $O_A(K(e^{-cu\log(2u)}+X^{-c_A}))$ of the balanced products $pq$, $X<p<q\le2X$. The curves can depend on the dyadic range, and their selection from the menu can depend arbitrarily on the input. Torsion marks have the same order at every good prime $p>17$ by rational torsion and injectivity of good reduction on prime-to-$p$ torsion. The exceptional primes dividing a model discriminant or a coordinate denominator are already covered by the power saving. The result bounds factorizations witnessed by the stated local scalar annihilations. General intermediate group-law failures and arbitrary high-entropy, input-dependent curve generation have wider scope.

In particular a positive-density search at $Y=\exp(C\sqrt{L\log L})$ requires at least $\exp(\Omega_C(\sqrt{L\log L}))$ curves in its total menu. This holds even for nonuniform advice prepared with unlimited time. A search reading $d$ designated bits to choose a list of $Q$ curves has total menu size at most $2^dQ$. For general $Y$ a sufficient condition for density zero is $\log K=o(\min(u\log(2u),L))$.

## A uniform rational torsion sieve

Clearing denominators and passing to an integral short equation changes the heights by $O(1+L^A)$. There are $O_A(1+L^A)$ primes dividing its discriminant or the denominators used. The elementary comparison between canonical and naive height gives $h(x(kR))\ll_A k^2(1+L^A)$. At every remaining prime where $kR$ reduces to the identity, the denominator of $x(kR)$ is divisible by $p$. This coordinate is finite because $R$ has infinite order. The sum of the logarithms of those denominators over $1\le k\le X^{1/4}$ is $O_A(X^{3/4}(1+L^A))$. Dividing by $\log X$ and normalizing by the number of primes in the dyad shows that the order exceeds $X^{1/4}$ outside a proportion $O_A(X^{-1/4}(1+L^A))$. A successful annihilation there requires the $Y$-smooth part of that order to be at least $X^{1/8}$. [Silverman's uniform bounds for the canonical height](https://doi.org/10.1090/S0025-5718-1990-1035944-5)

Write $o_E(d)$ for the number of absolute Galois orbits on the torsion points of exact order $d$. Whenever $d$ divides the order of the marked point modulo $p$ there are at least $\varphi(d)$ rational points of exact order $d$. At $p\nmid d\Delta_E$ these are the fixed points of Frobenius on the corresponding Galois set. For each orbit, with field of definition $F$ of degree $n_F$, the count is the number of degree-one primes of $F$ over $p$. Summing these counts against a fixed positive smooth majorant for the prime dyad gives, for $d<X$,
$$
\Pr[p\nmid d\Delta_E,\ d\mid{\rm ord}(R\bmod p)]
\ll \frac{o_E(d)}{\varphi(d)}+O_A(X^{-\delta}d^6 L^{O_A(1)})
$$
with any fixed $0<\delta<1/32$. Indeed $\sum_F n_F\le d^2$. Ramification is confined to the primes of $d\Delta_E$ by good reduction and étaleness of multiplication by $d$. The local different bound $e-1+e\,v_t(e)$ in residue characteristic $t$ gives $\log|D_F|\ll n_F(\log|d\Delta_E|+\omega(d\Delta_E)\log(2n_F))\ll_A n_F L^{O_A(1)}$. The fixed-strip prime-ideal explicit formula has error $O_w(X^{1-\delta}(\log(2|D_F|)+n_F L)^2)$ for the weighted logarithmic count. A majorant retains the upper bound at ramified primes because all counts are nonnegative. The constant on the orbit main term is absolute. [Explicit-formula details](fixed-marked-orders.md)

For a non-CM curve its adelic image $H$ has index $I\le L^D$ in $\mathrm{GL}_2(\widehat{\mathbb Z})$ uniformly for $X$ large, with $D=D(A)$. This follows from Zywina's polynomial bound in the logarithmic height of $j$. The full group acts transitively on exact $d$-torsion, giving $o_E(d)\le I$. If every prime divisor of $d$ exceeds $I$, then $o_E(d)=1$. To see this let the full group act on its $I$ cosets of $H$. Each elementary unipotent subgroup supported at $\ell>I$ is pro-$\ell$, so its image in $S_I$ is trivial. The two elementary unipotent subgroups generate $\mathrm{SL}_2(\mathbb Z_\ell)$, which therefore lies in the core of $H$ at each such prime. Their product acts transitively on the primitive vectors for $d$ by the Chinese remainder theorem. [Zywina, Theorem 1.1(i)](https://arxiv.org/pdf/1102.4656#page=1)

For a CM curve there is an absolute constant such that
$$
 o_E(d)\ll w(d),\qquad w(d)=\prod_{\ell^a\parallel d}(2a+1).
$$
There are thirteen rational CM $j$-invariants. For each choose a reference curve and a fixed isogeny to a curve with maximal CM order over a fixed number field containing its CM field. Each rational twist becomes isomorphic to its reference over an extension of degree at most six, by the size of the geometric automorphism group. Over this composite field the index of the maximal-order torsion image in $(\mathcal O_K\otimes\widehat{\mathbb Z})^\times$ is bounded by a uniform constant, by the CM open-image theorem and the bounded extension degree. The maximal-order Tate module is locally free of rank one. At a split prime the two valuations of a primitive vector modulo $\ell^a$ have minimum zero, giving $2a+1$ unit orbits, with zero assigned valuation $a$. At an inert prime there is one orbit. At a ramified prime the uniformizer valuation is zero or one, giving at most two. CRT multiplies the orbit bounds. Under the fixed isogeny of degree $c_0$, an exact $d$-torsion point maps to a point of order $d'$ with $d/d'\mid c_0$ and every image fiber has at most $c_0$ elements. Thus lifting the orbits costs another uniform constant. Restricting the Galois group during this argument gives an upper bound for the original orbit count. [CM image description](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/opposing-average-congruence-class-biases-in-the-cyclicity-and-koblitz-conjectures-for-elliptic-curves/43DEB36546504B3F9D79902F7226D679)

## Truncated smooth divisors with positive weights

Fix $\eta=\delta/32$. Take a set of primes $\mathcal P$ all at most $Z\le X^{\eta/2}$. If the $\mathcal P$-part of $n$ is at least $X^{\eta/2}$, multiply prime factors of this part with multiplicity until first reaching $X^{\eta/2}$. The resulting divisor $d_0$ belongs to $[X^{\eta/2},X^\eta]$. For $0<t\le1/2$ define
$$
J_t(d)=d^t\prod_{\ell\mid d}(1-\ell^{-t}),\qquad \sum_{d\mid d_0}J_t(d)=d_0^t .
$$
Hence the sum of these positive weights over $\mathcal P$-supported $d\mid n$ with $d\le X^\eta$ is at least $X^{\eta t/2}$. Summing the torsion-sieve errors against $J_t(d)\le d^{1/2}$ to $X^\eta$ costs $O_A(X^{-\delta/2})$ for large $X$. For the main terms use
$$
\log\!\sum_{{\rm supp}(d)\subseteq\mathcal P}
       \frac{J_t(d)w(d)}{\varphi(d)}
\ll \sum_{\ell\le Z}\frac{\ell^t-1}{\ell}
\ll t(\log Z) Z^t .
$$
Indeed $J_t(\ell^a)=(\ell^t-1)\ell^{(a-1)t}$ and the weighted geometric series in $\ell^{t-1}\le2^{-1/2}$ is bounded uniformly. The last inequality uses $\ell^t-1\le t(\log\ell) Z^t$ and $\sum_{\ell\le Z}\log\ell/\ell\ll\log Z$.

Choose $B=L^{D+2}$, increasing $D$ to at least one. For $\ell\le B$ use the global orbit bounds and $t_0=\min(1/4,1/(4(D+2)))$. Then $B^{t_0}\le L^{1/4}$, so after allowing the non-CM prefactor $I\le L^D$ the moment main term is $\exp(o(L))$. Dividing by $X^{\eta t_0/2}$ makes this exceptional probability $O_A(X^{-c_A})$. If $Y>B$, use the primes $B<\ell\le Y$ and $t=\log u/(2\log Y)$. Here $t\le1/2$ eventually, and both $Y$ and $B$ are at most $X^{\eta/2}$. The non-CM orbit count is one throughout this sum. The CM bound uses $w(d)$ directly. The logarithm of the moment is $O(\sqrt{u}\log u)$ while the logarithm of its required divisor weight is $(\eta/4)u\log u$. If the full smooth part is at least $X^{1/8}$ then the small or large range alone contributes at least $X^{1/16}>X^{\eta/2}$. This proves the assertion, including the case $Y\le B$ by the small range alone.

## Classical proof of the CM upper bound

Use a fixed reference $E_0$ for each rational CM $j$ and its quadratic CM field $K$. At inert good primes $p>3$, $E$ is supersingular with trace zero, so $d\mid{\rm ord}(R\bmod p)$ implies $p\equiv-1\bmod d$. The ordinary Brun–Titchmarsh bound gives a proportion $O(1/\varphi(d))$ for $d\le X^\eta$.

At split primes write $\mathfrak p$ for a degree-one prime of $K$ over $p$. All endomorphisms of $E_0$ are defined over $K$. Frobenius on a twist, transported to $E_0[d]$ using a geometric isomorphism, differs from reference Frobenius by one of the at most six geometric automorphisms $\nu$. The abelian torsion field $K(E_0[d])/K$ has conductor of norm $O(d^{O(1)})$. Indeed the fixed CM Grössencharacter giving Frobenius on the Tate module is the identity on principal generators congruent to one modulo its fixed conductor, up to choosing the conjugate embedding. On generators congruent to one modulo the conductor times $d$, its Frobenius action on $d$-torsion is trivial. This description also holds for a nonmaximal order on increasing the fixed modulus by its order conductor. [CM Grössencharacter and torsion reciprocity, Milne, *Complex Multiplication*](https://www.jmilne.org/math/CourseNotes/CM.pdf)

For a fixed primitive $v\in E_0[d]$ and automorphism $\nu$, the condition $\mathrm{Frob}_{\mathfrak p}v=\nu v$ is empty or is one coset of the stabilizer. In the resulting abelian orbit field it specifies one Galois element, and its relative density is $1/\#\operatorname{Orb}(v)$. Thorner–Zaman's Hecke Brun–Titchmarsh theorem gives the upper bound $O(X/(\#\operatorname{Orb}(v)\log X))$ whenever $X\gg d^{C}$, uniformly in $v,d$ because the base field is one of finitely many fixed quadratic fields. Reduce the absolute value of $\eta$ if necessary. Sum over vectors and automorphisms and divide by $\varphi(d)$. The resulting upper bound is $O(w(d)/\varphi(d))$ using the same finite-index orbit argument over $K$. The positive divisor proof now applies without any uniform zero-free strip in varying-degree fields. [Thorner–Zaman, Theorem 1.1](https://arxiv.org/pdf/1606.09238#page=3)

The finite replay enumerated 18 split, inert and ramified Cartan actions on 9,312 primitive torsion vectors with exact prime-power order. It also verified 5,997 divisor identities at positive integral values of the parameter and 162,990 truncated divisor certificates. The identities hold algebraically for every positive real parameter. [Exact GP replay](../experiments/smooth-marked-order-tail.gp)
