# Primitive completions from a majority of quadratic classes

Let \(K\) be an imaginary quadratic field with maximal order \(\mathcal O_K\), discriminant of absolute size \(\asymp V^2\), and class number \(h\gg V/(\log V)^D\) for a fixed \(D\). Set \(X=V^{1+\varepsilon}\) for fixed \(\varepsilon>0\), \(N=X/V\), and \(z\ge(\log V)^4\). Fix a set of forbidden rational primes. Suppose more than \(0.60h\) classes each contain \(\gg N\delta\) primitive integral ideals of norm at most \(X\), with every prime factor of the norm at most \(y\) and greater than \(z\), and with norm coprime to the forbidden primes. Assume \(\delta\gg(\log\log V)^{-D_1}\) for fixed \(D_1\), with uniform constants across the good classes.

Then every target class contains \(\gg X^2/[V(\log V)^{O(1)}]\) distinct primitive integral ideals of norm at most \(X^2\) obeying the same prime restrictions. Each is a product of two of the specified ideals with relatively prime rational norms, and the counted products have at most \((\log V)^{O(1)}\) ordered factorizations into integral ideals.

## Uniform counting at smaller cutoffs

In any fixed class the number of primitive integral ideals of norm at most \(U\) is \(O(1+U/V)\), uniformly in \(U\) and in the class. Take an integral ideal \(\mathfrak b\) in the inverse class. An integral ideal \(\mathfrak a\) in the given class has \(\mathfrak a\mathfrak b=(\gamma)\) for \(\gamma\in\mathfrak b\), and \(\mathrm N\mathfrak a=|\gamma|^2/\mathrm N\mathfrak b\). For any integer \(m\ge2\), one has \(\gamma\in m\mathfrak b\) exactly when \(\mathfrak a\subseteq m\mathcal O_K\), by invertibility of \(\mathfrak b\). Thus primitive ideals correspond, up to units, to primitive vectors in the lattice \(\mathfrak b/\sqrt{\mathrm N\mathfrak b}\), where the quotient denotes geometric scaling. This lattice has covolume \(\sqrt{|\operatorname{disc}K|}/2\asymp V\), and the norm bound gives a disk of radius \(\sqrt U\).

If the lattice vectors in the disk span at most a line, at most two of them are primitive. Otherwise a shortest lattice vector of length \(\lambda\le\sqrt U\) defines parallel lattice rows spaced by the covolume divided by \(\lambda\). This spacing is at most \(\sqrt U\) since there is a vector off the central row in the disk. Counting those rows and the points along each gives \(O(U/V)\). This proves the stated bound including small cutoffs.

## Pairs in a prescribed class

Write \(G\) for the class group and \(S\subset G\) for the good classes. For a target \(C\), the map \(c\mapsto Cc^{-1}\) is a bijection. More than \(0.20h\) classes belong both to \(S\) and to its inverse image under this map. For each such class, fix a first ideal \(\mathfrak a\) in its specified family. Its partner lies in the single good class \(C[\mathfrak a]^{-1}\).

Remove partners whose norm is divisible by any rational prime \(q\mid\mathrm N\mathfrak a\). For a primitive partner, such divisibility requires a prime ideal over \(q\) of norm \(q\). An inert prime cannot occur, as its sole prime ideal is \((q)\). At a split or ramified prime there are at most two candidate prime ideals. On dividing by one of them, the class is fixed, the ideal remains integral and primitive, and its norm is at most \(X/q\). The uniform cutoff count bounds the number of excluded partners for this \(q\) by \(O(1+N/q)\). All the primes of \(\mathrm N\mathfrak a\) exceed \(z\) and their number is at most \(\log X/\log 2\), so the number removed per first ideal is at most
\[
 O\bigl(\log X(1+N/z)\bigr)=o(N\delta).
\]
The first term is negligible because \(N=V^\varepsilon\), and the second because \(z\ge(\log V)^4\). Consequently there are \(\gg hN^2\delta^2\) ordered pairs in the target class with coprime rational norms. Each product is primitive. Indeed, a rational principal ideal \((q)\) for prime \(q\) dividing the product would have to divide one factor whenever \(q\) divides just one of the two norms, contradicting primitivity of that factor.

## Distinct products

For an integral ideal \(\mathfrak a\), let \(\tau_K(\mathfrak a)\) count its integral ideal divisors. Uniformly in the discriminant,
\[
 \sum_{\mathrm N\mathfrak a\le X}\tau_K(\mathfrak a)
 \ll X(1+\log X)^3.
\]
The norm coefficients of \(\zeta_K\) are bounded coefficientwise by those of \(\zeta^2\), as follows directly from the split, ramified and inert Euler factors. The displayed sum has Dirichlet series \(\zeta_K^2\) and is bounded by the summatory coefficients of \(\zeta^4\). The elementary bound for that sum follows by summing three of the factors with harmonic weights and counting the fourth by \(X\) divided by their product.

Set \(T=(\log V)^L\) and discard pairs with \(\tau_K>T\) on either side. There are \(O(X(1+\log X)^3/T)\) ideals of norm at most \(X\) above this divisor threshold, and each has \(O(N)\) possible primitive partners in its complementary class. For fixed \(L>D+5\) the number of discarded pairs is \(o(hN^2\delta^2)\). Each remaining product has divisor count at most \(T^2\), by unique ideal factorization and \(e+f+1\le(e+1)(f+1)\) at each prime ideal. Its divisor count bounds the number of ordered representations of the product. Dividing the surviving pair count by \(T^2\) proves the claimed lower bound.

The forbidden set can include the primes dividing \(2Z\) and the \(O(d)\) individual primes already selected from bins. The conclusion is uniform in these exclusions whenever the majority hypothesis is uniform. With \(y\le V^{0.9}\), all prime factors of the completion norm satisfy that same bound, including the factors introduced by class correction.
