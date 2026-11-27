# Product merges for the terminal rational numerator

For one input \(N\), let \(D=(\log N/\log\log N)^{1/3}\) and \(H=D\log\log N\). Fix the public prime \(Q\) with \(\log Q=(\sigma+o(1))DH\), where \(\sigma>0\), and condition on \(Q\) when drawing the public residue parameter \(r\). Its source interval \(I_Q\) has \(\lvert I_Q\rvert\asymp Q\) and consists of distinct units modulo \(Q\). In the terminal box, \(0<b'\le U=\exp((v+o(1))H)<Q\), and the positive rational numerator \(w=rb'-Qa\) has a uniform upper bound \(X\asymp QU\). The rational cutoff is \(B=\exp(O(H))\). The statements below allow every denominator in the interval and ignore the algebraic norm and parent-label conditions. They constrain two specified forms of rational candidate generation. [Terminal environment](keybreak-late-rational-eligibility.md)

## One denominator leaf in a product tree

Take an explicit binary merge tree. Its distinguished leaf supplies \((rb')^{-1}\) for the allowed denominators. The other leaves supply known smooth factors, each stored with its actual integer value or equivalent prime-power representation. A merge can preserve any selected products of one row from each child. Fix \(Q\) and the random coins independent of \(r\). Suppose each sibling subtree off the denominator-to-root path produces a menu \(S_j\) independent of \(r\), with at most \(W_j\) entries. Computation on the path itself may use all of \(r\), including in its pruning rules.

If an output succeeds, its numerator belongs to \(\{\prod_j s_j:s_j\in S_j\}\). For a fixed \(w\) and \(0<b'<Q\), the congruence \(w\equiv rb'\pmod Q\) determines at most one \(r\in I_Q\). Thus, even if the menus are correlated and all matching is free,
\[
 \Pr_r(\text{success}\mid Q,\text{coins})
 \le \min\left(1,\frac{U}{|I_Q|}\prod_{j=1}^{h} W_j\right),
\]
where \(h\) is the length of the distinguished path. The proof counts whole integer products, so repeated factors and multiple representations cannot increase the bound.

For a perfect tree of height \(h\) with every numerator leaf contributing an integer at least \(2\), any product below \(X\) needs \(2^h-1\le\log_2 X\). Therefore \(h=O(\log\log N)\). Under an explicit list budget \(T=\exp(O(H))\), each \(W_j\le T\) and \(h\log T=o(DH)\). The probability of alignment is \(\exp(-\Omega(DH))\), even giving the tree exact group coordinates. A constant success probability in this model requires a maximum width of at least \(\exp(\Omega(DH/\log\log N))\). The same estimate still gives negligible success after \(\exp(O(H))\) such trees. The unrestricted generalized birthday tree can use many more leaves because its outputs need no positive integer product bound. [Wagner's generalized birthday tree](https://people.eecs.berkeley.edu/~daw/papers/genbday.html)

The menu bound requires a path of length \(\Omega(D)\) at width \(\exp(O(H))\) for constant success. Allowing identity leaves or using an unbalanced tree can provide that depth. In those variants the menu formula still bounds the probability using the actual distinguished path length. Allowing signed exponents has a related limitation when the expanded negative factors are capped. If all \(2^h-1\) numerator leaves contribute nonidentity positive rational numbers \(u_i/v_i\) and the final product is the positive integer \(w\le X\), then
\[
 (2^h-1)\log 2
 \le \sum_i(\log u_i+\log v_i)
 =\log w+2\sum_i\log v_i.
\]
Thus a perfect tree at that necessary depth needs \(\sum_i\log v_i=\exp(\Omega(D))\). This is a requirement on the uncancelled denominator weight, which may fit the budget in a compressed representation. Using the budget with compressed supports would require a separate bound on their effective menu widths. The menu probability assumes that the sibling lists are independent of \(r\).

## What additive coordinates provide

The exact congruence is in the cyclic multiplicative group \(\mathbb F_Q^\times\) of order \(Q-1\). A homomorphism from it to the additive group \(\mathbb F_Q\) is trivial, since the orders are coprime. Taking low bits of ordinary residue representatives does not give an additive filter for multiplication. Discrete logs in a specified generator give addition modulo \(Q-1\), where one can express the exact bounded search as
\[
 \sum_{p\le B} e_p\log_g p\equiv \log_g r+\log_g b' \pmod{Q-1},
 \qquad e_p\in\mathbb Z_{\ge0},\quad
 \log w=\sum_{p\le B}e_p\log p.
\]
The integer product must still pass the exact interval and box checks. Logarithm coordinates alone supply neither a solution with nonnegative bounded weight nor uniform short lists of admissible factors.

For exact subgroup merging, discrete logs are unnecessary if a divisor chain of \(Q-1\) is provided. For \(t\mid Q-1\), the homomorphism \(g\mapsto g^{(Q-1)/t}\) has image order \(t\). Sorting one child by this image and the other by its inverse enforces membership in its kernel. If \(t\mid t'\), the quotient between the two nested kernels has order \(t'/t\). In particular, a prime factor of \(Q-1\) has to enter in one step of any exact chain reaching the identity. A large such factor prevents slicing that step into many small exact quotient constraints. The cost of matching that quotient still depends on the distribution of the lists.

Factoring \(Q-1\) by the Lenstra–Pomerance bound would charge at most \(\exp((\sqrt{2\sigma/3}+o(1))H)\) in expectation, since \(\log\log Q=(2/3+o(1))\log\log N\). This is a first-scale upper bound. A partial factorization may already supply usable projections. An \(L_Q[1/3,O(1)]\) routine, whenever justified, would have \(\exp(o(H))\) cost on this smaller modulus. Even providing the full chain and all logarithms for free leaves the product-menu and height bounds above. [Lenstra and Pomerance, Theorem 10.5](https://math.dartmouth.edu/~carlp/PDF/paper85.pdf)

## A small set of prime coordinates

Suppose an algorithm uses at most \(J=\exp((c+o(1))H)\) catalogues of primes fixed independently of \(r\) after conditioning on \(Q\) and its coins. It may select among them using the full \(r\) and solve each catalogue's bounded exponent problem for free. For a catalogue of \(s\) primes, replacing the ordered primes with the first \(s\) primes gives an injection from its natural numbers up to \(X\) into numbers at most \(X\) supported on the first \(s\) primes. This bounds the whole support with arbitrary nonnegative multiplicities.

If \(s\le\exp((\beta+o(1))H)\) for \(\beta>0\), the first \(s\) primes are at most \(Y=\exp((\beta+\epsilon)H)\) for every fixed \(\epsilon>0\) and all large \(N\). For \(X\asymp QU\), Rankin's count at \(\alpha=1-(\log D-2\log\log D)/\log Y\) gives
\[
 \Psi(X,Y)\le X^\alpha\prod_{p\le Y}(1-p^{-\alpha})^{-1}
          \le X\exp\left(\left(-\frac{\sigma}{3(\beta+\epsilon)}+o(1)\right)H\right).
\]
Indeed, \(p^{1-\alpha}\le D/(\log D)^2\) and \(\sum_{p\le Y}1/p=O(\log\log Y)\), so the logarithm of the product is \(o(H)\). The term from \(X^\alpha\) uses \(\log D=(1/3+o(1))\log\log N\). It follows from the union bound on \(w,b'\) that
\[
 \Pr_r(\text{alignment})\le
 \min\left(1,\exp\left(\left(c+2v-\frac{\sigma}{3\beta}+o(1)\right)H\right)\right),
\]
taking \(\epsilon\) to zero after the input limit. When \(s=\exp(o(H))\), one can use every fixed \(\beta>0\). The probability is then at most \(\exp(-\omega(H))\) for any fixed \(c,v\). This applies to an exact solver on a small, previously chosen subset of prime coordinates, including one that never enumerates its admissible products. A catalogue built directly as a function of the full \(r\) falls outside the independence hypothesis. [Related Rankin count](keybreak-asymmetric-terminal-budget.md#full-prebuilds-and-selective-reconciliation)

## An exact reconstruction from a known large divisor

A divisor of the sought numerator can provide an alternative to building the whole \(w\). Fix a positive \(d\) coprime to \(Q\), and set \(k=rQ^{-1}\bmod d\) in \([0,d)\). A primitive mark with \(|a|\le U\), \(0<b'\le U\), and \(d\mid rb'-Qa\) satisfies \(kb'-a=t d\). If \(d>2U^2\), then
\[
 \left|\frac{k}{d}-\frac{t}{b'}\right|=\frac{|a|}{db'}<\frac1{2b'^2}.
\]
Here \(\gcd(t,b')=1\), since a common divisor divides \(a\). By the continued-fraction convergent criterion, one can recover the mark, if it exists, by testing the convergents of either finite continued fraction for \(k/d\), including the exact value. Two distinct primitive marks cannot both qualify, since their nonzero determinant would be divisible by \(d\) and have magnitude at most \(2U^2\). For example \(Q=211,r=127,U=10,d=256\) gives \(k=37\). The convergent \(1/7\) of \(37/256\) gives \(a=37\cdot7-256=3\) and \(127\cdot7-211\cdot3=256\).

If a proposed \(d\) is independent of \(r\) conditional on \(Q\), its success probability is \(O(U^2/d+U^2/Q)\). For each candidate primitive pair, \(\gcd(b',d)>1\) makes the divisibility impossible, since a common prime would also divide \(a\). Otherwise \(r\) is in one residue class modulo \(d\), which hits at most \(|I_Q|/d+1\) values. Summing over the box proves the estimate. Thus even free reconstruction leaves an \(\exp(-\Omega(DH))\) alignment probability for each independently proposed \(d\) of logarithmic height \(\Theta(DH)\). At the other scale, a known smooth divisor with \(\log d=O(H)\) only subtracts \(O(H)\) from the logarithmic cofactor height \((\sigma+o(1))DH\). Its contribution to the leading coefficient of the marginal smoothness loss is \(o(1)\). A sampler adapting the divisor to \(r\) would need a separate supply and cost argument.
