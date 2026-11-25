# Deterministic average splitting from one cyclotomic multiple

Fix an integer $k\ge2$. Given a composite $N$ and a positive multiple $M$ of $\Phi_k(p)$ for one unknown prime divisor $p$ of $N$, a deterministic algorithm returns a proper factor with polynomial average bit cost on uniform integers of each bit length. The exceptional sets are independent of $M$. If $M$ covers all but at most one distinct prime in the residual, the same sweeps give complete factorization, allowing repeated prime powers. More precisely, on $Z/2<N\le Z$ any family of supplied multiples of bit length at most $H(Z)$ has mean cost polynomial in $\log Z+H(Z)$, and for every fixed $A>0$ a polynomial cutoff misses at most $O_{k,A}(Z/(\log Z)^A)$ integers. For a proper split, finding a small prime divisor already succeeds, including when that prime was the only one covered. For complete factoring, remove each small prime to full multiplicity. A branch supported at a single prime is handled by integer roots and primality testing.

As a corollary, for every fixed positive integer $j$ there is deterministic polynomial average-time complete factoring from one value $\sigma(N^j)$. Use $k=2$ if $j$ is odd and the least prime divisor $k$ of $j+1$ otherwise. A prime of original multiplicity one has
$$
 \Phi_k(p)\mid \frac{p^{j+1}-1}{p-1}\mid\sigma(N^j).
$$
Large repeated prime divisors are charged to the runtime tail below. The algorithm always finishes, including those exceptional inputs. Obtaining the supplied divisor sum is outside the bit bound.

## Conductors separating an ordered prime pair

Put $b_k=2\omega(k)$. For each prime $\ell\equiv1\pmod{4k}$ choose a Dirichlet character $\chi_\ell$ of order $k$. Write its value at $t$ as $\zeta_k^{x_\ell(t)}$. For each prime $s\mid k$, consider the coordinate vectors of a pair $p,q$ reduced modulo $s$. Suppose these are independent for every such $s$ on some list of small conductors. At each $s^e\parallel k$, invert a nonsingular two-coordinate minor modulo $s^e$ to construct a row taking values $1,0$ on the vectors of $p,q$. Combine the rows by CRT on their union of supports. The resulting row modulo $k$ has at most $b_k$ nonzero coordinates and defines a character of order $k$ with values $\zeta_k,1$ at $p,q$. Its conductor $f$ is the product of its nonzero coordinates' prime conductors. The corresponding cyclic degree-$k$ field in $\mathbb Q(\zeta_f)$ has $p$ inert and $q$ completely split. The construction works in either orientation.

Use a single global conductor list through $Y=(\log Z)^B$, with $B$ fixed sufficiently large. Its support bound gives $f\le(\log Z)^F$, where $F=b_kB$. Failure of independence modulo some $s\mid k$ implies either that one profile is zero, or that both profiles are nonzero and some $p^a q^c$, $1\le a,c<s$, is an $s$th power at every conductor. The projection of $\chi_\ell$ to order $s$ detects these powers. We count the associated prime or mixed radical exceptions on dyadic intervals, without a restriction on the relative sizes of the two prime factors.

## A global marker bound

Write $b=\log\log Z$. In a fixed-dimensional coefficient lattice, suppose a marker collection has $P$ elements whose norms distinguish all subsets. Suppose the logarithm of each marker's archimedean sup norm is at most $Ab$, and conversion from archimedean to coefficient norm costs at most $e^{Ib}$. On a dyadic modulus interval $[T,2T]$, with $(\log Z)^C\le T\le Z$, take products of
$$
 r=\left\lfloor\frac{2\log T-Ib}{Ab}\right\rfloor
$$
distinct markers. They fit in the coefficient cube of radius $T^2$. In the applications $r=O(\log Z/b)$, and $C$ will ensure $r\ge1$. If $\log(P/r)\ge Jb$, the product set $S$ satisfies
$$
 \frac{\log |S|}{\log T}
 \ge \frac{2J}{A}-\frac{J(1+I/A)}{C}.
 \tag{1}
$$
Indeed, $\binom Pr\ge(P/r)^r$ and the floor loses at most one factor. The second term also accounts for the conversion back to coefficients.

A killing character extended by zero to the nonunits is one on $S$ if all its markers are units. Its normalized additive Fourier coefficients have squared sum at most one. In each application its supported vectors have exact denominator equal to the bad modulus $d$, which will be a prime or a product of two distinct primes. This follows because a local frequency vector that is zero modulo a prime factor gives the zero local multiplicative mean. Select one killing character per failed modulus. The supported vectors of distinct moduli in $[T,2T]$ are disjoint and $1/(4T^2)$-separated on the coordinate torus. If $F_S(x)=\sum_{n\in S}e^{2\pi i n\cdot x}$, Fourier inversion gives $|S|=\sum_v\widehat\chi(v)F_S(v/d)$. By Cauchy–Schwarz each bad modulus contributes at least $|S|^2$ to the sum of $|F_S|^2$ over its supported vectors. The $h$-dimensional additive large sieve gives a total of $O_h(T^{2h})|S|$, so the count is $O_h(T^{2h}/|S|)$. [Huxley, multidimensional additive large sieve](https://doi.org/10.1112/S0025579300002540)

For the reciprocal characters at an odd prime $s\mid k$, use $F_s=\mathbb Q(\zeta_s)$ of degree $h=s-1$. Fix a ray modulus $\lambda^u$ at its prime over $s$, with $u>2v_\lambda(s)$. Among the rational primes $\ell\le Y$ that split completely in a fixed normal extension containing both the ray class field and $\mathbb Q(\zeta_{4k})$, choose one marker generator $\pi_\ell$ of norm $\ell$ with $\pi_\ell\equiv1\pmod{\lambda^u}$. There are $\gg_k Y/\log Y$ such markers by Chebotarev. The logarithmic lattice of ray units makes all conjugates $O_k(\ell^{1/h})$, and Hensel's lemma makes $\pi_\ell$ a local $s$th power at $\lambda$. For $w=p^a q^c$, tame power reciprocity then gives
$$
 \left(\frac{w}{(\pi_\ell)}\right)_s
 =
 \prod_{\mathfrak p\mid p}\left(\frac{\pi_\ell}{\mathfrak p}\right)_s^a
 \prod_{\mathfrak q\mid q}\left(\frac{\pi_\ell}{\mathfrak q}\right)_s^c.
$$
The complex places contribute one. A single factor gives the same identity for an individual prime. The right side is a character of $(\mathcal O_{F_s}/d\mathcal O_{F_s})^\times$ with a nonprincipal factor at each prime of the radical $d=pq$ or $t$. This follows because the residue fields contain $\mu_s$ and the exponents are nonzero modulo $s$. For $s=2$ use rational Legendre characters and rational markers $\ell\equiv1\pmod{4k}$, so $h=1$. In either case the norms distinguish subsets and choosing $C>B$ makes every marker a unit at each tested prime. [Neukirch, Chapter VI §8, Theorems 8.1 and 8.3](https://web.math.ucsb.edu/~agboola/teaching/2021/fall/225A/neukirch.pdf) · [Milne, ray class fields](https://www.jmilne.org/math/CourseNotes/CFT.pdf#page=167)

These reciprocal markers give $A=B/h+1$, $I=1$, and $J=B-2$ for sufficiently large $Z$, using $P\gg_k e^{Bb}/b$ and $r=O_k(\log Z/b)$. In (1) the gap $2h-2J/A=2h(h+2)/(B+h)$ can be made smaller than $\epsilon/4$ simultaneously for all $s\mid k$. After increasing $C$ the floor and conversion loss also stay below $\epsilon/4$. The sieve thus gives $O_k(T^\epsilon)$ bad prime or pair radicals per dyadic interval, after absorbing constants and the finitely many $s$. This ensures independent profiles for all uncharged pairs over the same global list.

## Uniform local generation

An order-$k$ character primitive at conductor $f$ has a period $\theta$ with $k$ distinct conjugates of modulus at most $f$. The first Fourier coefficient of the cyclic sequence of coset periods is the nonzero primitive Gauss sum, so a stabilizing cyclic shift must be the identity. Its power-basis discriminant and index are polynomially bounded in $f$ for fixed $k$. [Primitive Gauss sums](https://dlmf.nist.gov/27.10)

Fix a larger global marker scale $Y'=(\log Z)^{B'}$. For $v\equiv1\pmod f$ prime, evaluation at a residue root gives a coordinate lattice of determinant $v$. Minkowski gives a nonzero marker of coefficient size at most $2v^{1/k}$, with conjugates $O_k(f^{k-1}v^{1/k})$ and absolute norm $v$ times an integer $O_k(f^{k(k-1)})$. Discard primes through the latter multiplier bound. The remaining norms distinguish subsets. Maynard supplies $P\gg_k Y'/((\log Z)^{3F/2}\log Y')$ such markers for $B'$ sufficiently large. Choose $B'>\max\{8F,3F/2+Fk(k-1)+1\}$ to meet the theorem's range and retain the marker lower bound after the deletion. The bounded conductors follow by the fixed-progression prime number theorem. In (1) take
$$
 A=B'/k+F(k-1)+1,\qquad I=F(k-1)^2+1,\qquad
 J=B'-3F/2-2.
$$
The inverse embedding matrix bound uses the cofactor formula and a nonzero integral basis discriminant. A sufficiently large $C$ makes every marker a unit at $t\ge(\log Z)^C$. If the small box of radius $2(Y')^{1/k}$ fails to generate at prime $t$, a nonprincipal unit character kills it and the same additive sieve applies, now in dimension $k$. Take $B'$ large enough that $2k-2J/A=2(kA-J)/A<\epsilon/4$. Next take $C$ so the second term of (1) is below $\epsilon/4$. There are $O_k((\log Z)^F)$ possible fields from the bounded-support rows. Their union costs at most $T^{F/C}$, which is at most $T^{\epsilon/4}$ by increasing $C$ once more. Thus simultaneous local generation fails at $O_k(T^\epsilon)$ primes per dyadic interval. For the rational reference when $k=2$, the degree-one rational-marker argument above gives the same conclusion for the full unit group using any nonprincipal killing character. [Maynard, Theorem 2](https://arxiv.org/pdf/1201.1777#page=3)

## Literal gcd tests

For $k\ge3$, put $D=M/2^{v_2(M)}$ and $U(X)=(X^k-1)/\Phi_k(X)$. At a pair with the covered $p$ inert and the other prime $q$ split, let $\sigma$ be Frobenius at $p$ in the cyclic degree-$k$ field $K$. For a small unit candidate $\alpha$ of the local generating box set
$$
 \beta=\prod_i\sigma^i(\alpha)^{u_i},\qquad U(X)=\sum_i u_iX^i.
$$
At $p$ its order divides $\Phi_k(p)$ because the projection reduces to $\alpha^{U(p)}$. For odd $p$, the parity of $\Phi_k(p)$ equals that of $\Phi_k(1)$. When $k$ has an odd divisor greater than one, $\Phi_k(1)$ is odd, so $\beta^D=1$ at $p$. If $k=2^a$ with $a\ge2$, then $\Phi_k(p)=p^{2^{a-1}}+1\equiv2\pmod8$. The reduction of $\beta^D$ then has order at most two and is still scalar.

At $q$, the product of the quadratic signs in two adjacent components of $\beta$ is a character of $\alpha$ given, up to cyclic labeling, by the vector of coefficients of $(1+X)U(X)$ in $\mathbb F_2[X]/(X^k-1)$. It is nonzero since its degree is $k-\varphi(k)+1<k$. Local generation at $q$ therefore supplies $\alpha$ with opposite signs in those two components of $\beta$. The odd exponent $D$ preserves those signs, so $\beta^D$ is nonscalar at $q$. This uses generation at the split prime alone.

Multiply $\beta$ by the rational integer $|\mathrm{Nm}(\alpha)|^{\sum_{u_i<0}|u_i|}$ to obtain an integral $\gamma$. All its conjugates have polylogarithmic size in $Z$, since $k$ is fixed, the conjugates of $\alpha$ have that size, and their product is a nonzero integer. Its minimal polynomial $P$ has degree between two and $k$, polynomially bounded coefficient height in $\log Z$, and discriminant of the same type. The initial trial cutoff exceeds every nonzero norm and discriminant bound used here. Thus denominator clearing is by units at the residual primes. Reduction of $\mathbb Z[\gamma]$ embeds into $\mathcal O_K/t\mathcal O_K$ at $t=p,q$: the order index in its own field is prime to $t$, and $t\mathcal O_K\cap\mathcal O_{\mathbb Q(\gamma)}=t\mathcal O_{\mathbb Q(\gamma)}$. Accordingly $X^D\bmod(P,t)$ is scalar at $p$ and nonscalar at $q$. The algorithm scans every monic polynomial in the stated coefficient box and takes the gcd of $N$ with all nonconstant coefficients. Thus it never needs to compute the conductor fields, the projection, or an automorphism.

For $k=2$ use the quadratic power chain $2^iD$, $0\le i\le v_2(M)$, and the rational split reference. The projective unit groups in the inert and split cases have cyclic orders $t+1$ and $t-1$, respectively. Define the threshold of a group to be the first chain exponent divisible by its order, or infinity. If the split reference thresholds differ, its generators supply a split by gcd tests with $a^{2^iD}-1$. If they coincide, a field inert at the covered $p$ and split at $q$ keeps the reference threshold at $q$ and changes it at $p$ to $v_2(p+1)$. This is distinct from either $v_2(p-1)$ or infinity. The resulting test separates using a generator at the side whose full group is not yet killed. Test all small squarefree quadratic radicands, including the two-conductor products. A local witness expressed in the period basis has polylogarithmic coefficients in the basis $1,\sqrt f$ after clearing a factor of two. Choose the test box to include these coefficients and use norm gcds for any candidate that is not a unit at a residual prime.

When a proposed gcd $g$ is found, saturate it to $\gcd(n,g^{\lceil\log_2 n\rceil})$ on the current cofactor $n$, computing the power modulo $n$. Saturation retains the prime support of $g$ and includes its full powers in $n$. A divisor separating two prime supports stays proper. With all but one covered, a branch with at least two distinct primes has at least one covered prime, so the same supplied $M$ suffices through the recursion. A fixed finite set of allowed indices can also be used if the index varies by covered prime. Run the corresponding searches and take the finite union of their exceptional sets.

## Uniform stage choices and dyadic tails

First fix $B$ for all reciprocal sieves and $F=b_k B$ for conductors. Next choose $B'$ for local generation. The coefficient-radius and conductor bounds determine global polylogarithmic height, norm and discriminant bounds for projected witnesses. Finally choose $C>\max\{B,B',4F/\epsilon\}$ and above all height, norm and discriminant exponents. In every application of (1), also require $C>4J(1+I/A)/\epsilon$ and $2C>I+A$. Thus no earlier exponent depends on the trial cutoff $L_0=(\log Z)^C$. The algorithm's sweep is polynomial in $\log Z+\log M$ for fixed $k$.

After extraction through $L\ge L_0$, the fraction of inputs charged to a prime $t$ is $O(1/t)$, and to a radical $pq$ is $O(1/(pq))$. Dyadic summation yields separate bounds.

- Individual reciprocal-sieve exceptions contribute $O(L^{-1+\epsilon})$.
- Mixed radical exceptions contribute $O(L^{-2+2\epsilon})$, since $pq>L^2$.
- Local generation exceptions contribute $O(L^{-1+\epsilon})$.
- The $\sigma(N^j)$ corollary needs one additional $O(1/L)$ term for $t^2\mid N$ with $t>L$.

Take $\epsilon<1/2$. Small-factor extraction costs $\sqrt L$ times a polynomial in $\log Z$, and the static sweeps add polynomial bit cost. Double $L$ whenever needed and stop at $L\ge\sqrt Z$ at the latest. The mean costs beyond the initial stage are bounded by a dyadic series with terms $L^{-1/2+\epsilon}$ times the polynomial bit bound. This gives the claimed mean cost and always yields exact verified factors. Stopping after any sufficiently large fixed power of $\log Z$ gives the stated inverse-logarithmic exception bound. [Bostan–Gaudry–Schost, Lemma 13](https://mathexp.eu/bostan/publications/BoGaSc07.pdf#page=15)

Bach and Shallit's Theorems 3–4 choose an inert/split conductor under ERH and use a randomized polynomial-time algorithm with one cyclotomic multiple. Źrałek's deterministic Theorem 5.5 uses a fixed cyclic field, irreducibility at the covered prime, and a smooth cyclotomic value. The average bound here uses a conductor library and does not impose smoothness. The focused search did not establish priority for the unconditional average-input result. [Bach–Shallit, Theorems 3–4](https://doi.org/10.1090/S0025-5718-1989-0947467-1) · [Źrałek, Theorem 5.5](https://arxiv.org/pdf/0707.4102#page=11)

## Arithmetic checks

- For fixed powers 8 and 24 the replay completely factors inputs with six residual primes, all inert in every singleton field in the finite library. Every successful refinement uses a field with two conductor primes. Multiplying each supplied divisor sum by a 1,344-bit integer preserves the refinements. Separate fixtures cover exactly one prime at indices 2, 3 and 5, in each orientation and with repeated factors. [Exact divisor-sum and one-prime gcds](../experiments/average-cyclotomic-refinement.gp)
- The composite-index replay checks indices 4, 6 and 8, including powers of two where the projected value raised to the odd exponent equals $-1$ at the covered prime. The gcd still splits both squarefree and repeated-factor inputs. A separate CRT replay checks 3,053 prime-pair row lifts. Its index-six example has no minor invertible modulo six and uses different minors modulo two and three. [Projection and literal polynomial powers](../experiments/composite-order-projection.gp) · [CRT rows](../experiments/composite-conductor-rows.py)
- Four explicit quintic ray generators verify 208 prime and 5,632 composite residue-symbol comparisons, covering all four nonzero rational-prime classes modulo five. On 135 test primes the first eight quintic conductors leave no exceptional ordered pair. A literal degree-five field of conductor 341 separates a pair that both singleton fields miss under dual coverage. [Quintic reciprocity and cutoff](../experiments/quintic-reciprocity.gp) · [Cubic reciprocity and balanced-pair bounds](public-cubic-characters.md)
