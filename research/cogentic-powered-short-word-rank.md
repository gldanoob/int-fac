# Full rank from signed short words in a powered local quotient

Under Dirichlet RH, a deterministically enumerable catalogue of words with at most three signed prime letters has full rational rank of productive words under a quantitative condition on a powered local quotient. The condition bounds an index at one prime and asks for a nontrivial powered image at another. It allows the local residual order and the opposite image to be much larger than the catalogue cutoff. This replaces a giant product fiber by a short prime catalogue on the stated promise. [Sparse product fibers](cogentic-short-order-lattice-determinants.md)

## Two prime projections

Let \(p\ne q\) be two prime divisors of \(N\), and let \(E\ge1\) be public. For \(r\in\{p,q\}\), let \(h_r=(r-1)/\gcd(r-1,E)\) be the order of the image of the \(E\)-th power map on \(\mathbb F_r^\times\). Suppose that some \(1\le d\le R\) satisfies
\[
     a:=h_p/\gcd(h_p,d)\le A_0,\qquad
     b:=h_q/\gcd(h_q,d)\ge 2.
\]
Neither the primes nor \(d\) need be given. Denote the images of the \(Ed\)-th power map at \(p,q\) by \(A,B\), of sizes \(a,b\) respectively. The map
\[
  \psi:(\mathbb Z/N\mathbb Z)^\times\to A\times B,\qquad
  s\mapsto (s^{Ed}\bmod p,\ s^{Ed}\bmod q)
\]
is onto by CRT and the definitions of the images. A word \(w\) with \(\psi(w)\in\{1\}\times(B\setminus\{1\})\) has residual order dividing \(d\) at \(p\) and residual order not dividing \(d\) at \(q\), for the powered base \(w^E\). Call these the productive words.

Choose a public cutoff \(X\) and split \((X/2,X]\) into three fixed positive-length proportions. Let \(\mathcal S\) be the set of its unit primes, with \(m_0=|\mathcal S|\). Under Dirichlet RH, for uniform primes in each one of these intervals, every nonprincipal character modulo \(N\) has mean of magnitude at most
\[
      \epsilon \ll X^{-1/2}\log(NX)\log X .
\]
Indeed the prime-sum explicit formula gives \(O(X^{1/2}\log(NX))\) before normalization, and the interval has \(\gg X/\log X\) primes. Primes dividing \(N\) can be detected and removed by gcd, giving a factor when encountered. Any nonprincipal character on a quotient of the unit group pulls back to a nonprincipal Dirichlet character modulo \(N\). This is the ordinary rational-prime character bound. [Jao, Miller and Venkatesan, equation (2.4)](https://arxiv.org/abs/0811.0647)

Take \(X\) large enough that \(\epsilon\le1/(8A_0)\). An effective choice is \(X\) of order \(A_0^2\log^C(2NA_0)\) for a sufficiently large fixed \(C\). Character orthogonality on each quotient shows that, in each of the three intervals, the mass of every \(A\)-label is at least \(1/a-\epsilon\), while the mass of a single joint label in \(A\times B\) is at most \(1/(ab)+\epsilon\). The former is strictly larger than the latter because \(b\ge2\). Thus each \(A\)-label in each of the three intervals contains primes with at least two distinct \(B\)-labels. No upper bound on \(b\) is needed.

## A catalogue and its full rank

Take any menu \(\mathcal P\) of \(m\) distinct rational unit primes containing \(\mathcal S\), for example every prime through an independent public cutoff greater than \(X\). Include the following signed words.

- Include \(s/t\) for \(s\in\mathcal P\), \(t\in\mathcal S\) and \(s\ne t\).
- Include \(s_1s_2/s_3\) with \(s_i\) in the \(i\)-th interval of \(\mathcal S\).

The catalogue has size \(O(mm_0+m_0^3)\) and uses neither of the hidden labels or \(d\). Its exponents belong to \(\{-1,0,1\}^m\) since the three intervals are disjoint.

Project the rational exponent space to \(\mathbb Q^A\) by taking the coordinate at a prime \(s\) to the basis vector \(f_u\) for its \(A\)-label \(u\). Within each \(u\), choose two primes in \(\mathcal S\) with distinct \(B\)-labels. They are joined by a productive ratio. Every menu prime with label \(u\) has a \(B\)-label different from that of at least one of the two chosen primes, and its ratio with that prime is in the catalogue. This gives a connected graph within each \(A\)-class. Its edge differences span all within-class differences, yielding the kernel of the projection, of dimension \(m-a\).

For any \(u,v\in A\), take \(s_1,s_2\) in the first two intervals with labels \(u,v\). The third interval supplies \(s_3\) of label \(uv\) whose \(B\)-label differs from the product of the first two \(B\)-labels. The resulting productive word projects to \(f_u+f_v-f_{uv}\). These vectors span \(\mathbb Q^A\). In the quotient by their span, the map \(u\mapsto f_u\) is a homomorphism from the finite group \(A\) to an additive rational vector space, so all its values vanish. The productive catalogue vectors therefore span the entire \(\mathbb Q^m\).

For cyclic \(A\) of order greater than two, support at most two with coefficients in \(\{-1,0,1\}\) cannot span the full rational exponent space even if the test at \(q\) is dropped. A word trivial in \(A\) then projects either to zero, a multiple of \(f_1\), or a signed sum \(f_u+f_{u^{-1}}\). All such projections are invariant under inversion on \(\mathbb Q^A\), which has a nonzero anti-invariant subspace.

The middle letter may instead come from a separate menu of \(m_1=\operatorname{poly}(\log N)\) primes below \(X/2\), saving a factor \(m_0/m_1\) in the triple list when this is large. Indeed, take all unit primes in \((Y/2,Y]\) for \(Y=\log^{C'}(2N)\) with \(C'>4\) fixed, and increase \(X\) if needed so that \(Y<X/2\). Include these primes in \(\mathcal P\) if it does not already contain them. Their \(A\)-labels generate \(A\), since a proper subgroup would make some nonprincipal character of \(A\) identically one on this interval, contradicting its prime bound. Use the first and third original intervals for the other two letters. Now the projected vectors \(f_u+f_v-f_{uv}\) are guaranteed for every \(u\) and for \(v\) in a generating set. In the rational quotient by these vectors, taking \(u=1\) gives \(f_1=0\) and iterating any such \(v\) through its finite order gives \(f_v=0\). Invariance under the generators then forces every \(f_u=0\), as required. The reduced catalogue size is \(O(mm_0+m_0^2m_1)\), at most \(mm_0\operatorname{poly}(\log N)\). For \(A_0=\exp(o(H))\) and \(m=\exp(\Theta(H))\), this is \(m\exp(o(H))\), where \(H=(\log N)^{1/3}(\log\log N)^{2/3}\).

## Testing and limits of the promise

If \(d\) is known, testing \(\gcd(w^{Ed}-1,N)\) recognizes a proper factor from each productive word. If only \(R\) is known, cap it at \(N\) and use the deterministic prefix test for the first positive \(j\le R\) with \(\gcd((w^E)^j-1,N)>1\). A productive word has a hit by \(d\). At the first hit the gcd cannot be all of \(N\), since the local orders at \(p,q\) are different and a first hit is the minimum local order over the prime divisors of \(N\). No powering by \(N-1\) is needed for this implication, and it also works when \(N\) contains prime powers. The list and the tests therefore give a deterministic split under the promise in \(\widetilde O((mm_0+m_0^3)(\sqrt R+\log(2E))\operatorname{poly}(\log N))\) bit operations, with the same improvement if using the reduced catalogue and with the construction and size of the prime menu charged separately. [Local first-hit prefix test](cogentic-partial-odd-orders.md#search-from-an-odd-partial-scalar)

For \(A_0,R,\log(2E)\le\exp(O(H))\) and a menu of \(\exp(O(H))\) primes, both catalogue construction and verification fit the one-third budget. This is a short signed rank guarantee, distinct from a speedup for the first factor on the same small-order promise. In fact \(h_p\le A_0R\), so single-base local-order searches can also have one-third cost in that regime. If \(R\) is much larger, the catalogue can still have one-third size, with the first-hit verification cost depending on \(R\).

Without a local index bound of this form, the argument gives no short catalogue at the target scale. For instance if \(Ed\) is too small to remove the large local order at either prime, each useful fiber can have mass far below the prime character error. This is consistent with the support lower bound for unpowered short words on balanced inputs. [Support and index bounds](cogentic-short-order-lattice-determinants.md)

## Finite check

For \(N=211\cdot227=47897\), \(E=N-1\) and \(d=35\), the two \(E\)-powered image orders are 105 and 113, giving \(a=3,b=113\). The three intervals forming \((210,420]\) each contain 11 unit primes. In each interval every one of the three \(A\)-labels has at least two \(B\)-labels. With the prime menu through 600, excluding the two divisors of \(N\) for this check, the above graph and triple construction has full rational rank \(107\) using \(113\) productive words. Every chosen word gives a proper gcd at or before exponent 35 of its \(E\)-th power. The checks also give rank \(107\) with \(E=2\) for both \(211\cdot227\) and \(211^2\cdot227\).
