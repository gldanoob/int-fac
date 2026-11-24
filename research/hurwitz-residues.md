# Factoring from low bits of Hurwitz class numbers

Let $H(m)$ be the Hurwitz class number, counting all classes of positive binary quadratic forms of discriminant $-m$ with the usual automorphism weights. Write $h(D)$ for the primitive order class number. The reduction below uses $H$ at nonfundamental discriminants and allows repeated prime factors of the factoring input.

The [single-index reduction](#one-large-index-and-quarter-bit-precision-suffice) factors using just the lowest $\lceil b_n/4\rceil+1$ bits of the positive three-square count at each twist $\ell n^2$. The two-index argument first explains how to isolate any prime power.

## Two-index oracle and bit bound

Fix rational $0<\epsilon<1/4$. On input $N\ge2$ of bit length $b$, the algorithm returns the complete prime factorization. For a cofactor $n$ of bit length $b_n$, set $k=\lceil(1/4+\epsilon)b_n\rceil$. The oracle receives an **unfactored positive integer** $m\equiv3\bmod8$ and returns the integer $3H(m)\bmod 2^{k+1}$. An equivalent oracle returns the ordered, signed three-square count $r_3(m)\bmod 2^{k+4}$, since $r_3(m)=24H(m)$ on this progression. Dividing its least nonnegative residue by eight gives the required $k+1$ bits exactly. [Chen–Garvan, §2, Eq. (2.1) and Gauss's identity](https://doi.org/10.1016/j.aim.2022.108235)

Assuming Dirichlet GRH for the least-prime estimate, the reduction costs $2^{O_\epsilon(\sqrt b)}(1+Q)$ deterministic bit operations, where $Q$ bounds one such evaluation at the requested precision on indices of at most $4b+O(\sqrt b)$ bits. In particular, an evaluator of cost $2^{o(b/\sqrt{\log b})}$ there would beat the repository benchmark. Evaluation at this precision remains open here. [Least-prime theorem, §1.2](https://arxiv.org/pdf/1309.3595#page=3) · [Scope of the Dirichlet GRH verification used in the repository](https://math.mit.edu/~drew/grh/)

## Isolating one prime power

Trial-divide once through $2^{\lceil\sqrt b\rceil}$, recording multiplicities. For each residual cofactor, finish primes and replace a perfect power by its base, carrying the exponent. A remaining $n$ is odd, has at least two distinct prime factors and is nonsquare. Choose for the proof a prime power $p^e\parallel n$ with $e$ odd and set $C=n/p^e$. Then $1<C<n$. Each remaining prime exceeds the trial bound, so $t=\omega(n)\le\sqrt b$.

There is a prime $\ell\equiv3\bmod8$, coprime to $n$, with $(-\ell/p)=-1$ and $(-\ell/q)=+1$ for every other prime $q\mid n$. Indeed, on units modulo $8n$ the residue modulo 8 and the $t$ Legendre symbols $(\ell/q)$ are independently prescribable by CRT. Multiplying the signs by $(-1/q)$ specifies one coset of index $J=4\cdot2^t$. Lamzouri–Li–Soundararajan's Theorem 1.4 gives a least prime $O(J^2\log^2(8n))=2^{O(\sqrt b)}$, absorbing the finitely many small moduli. The algorithm tries eligible primes in increasing order until it verifies a split. Only the existence proof uses the factors of $n$. [Lamzouri–Li–Soundararajan, Theorem 1.4](https://doi.org/10.1090/S0025-5718-2015-02925-1)

For each such trial prime define $R(f)=3H(\ell f^2)/(3H(\ell))$ for $f$ coprime to $2\ell$. The base $3H(\ell)$ is odd, including $3H(3)=1$. In the Hurwitz product formula the factor at $q^a\parallel f$ is
$$
q^a+\bigl(1-(-\ell/q)\bigr)(1+q+\cdots+q^{a-1}).
$$
In particular $R(f)$ is an odd integer. At the isolating prime all local factors except the one at $p$ equal their respective prime powers. With $S=1+p+\cdots+p^{e-1}$, this gives
$$
A=\frac{R(n)-n}{2}=CS,\qquad
B=\frac{R(n^2)-n^2}{2}=C^2 S(1+p^e)=A(n+C).
$$
Both $C$ and $S$ are odd. Hence $C\equiv B A^{-1}-n\bmod 2^k$. For a squarefree cofactor, $e=1$ and **$A=C$ already**. In fact this shortcut works whenever the isolated prime has exponent one. [Chen–Garvan, Eq. (2.1) and Theorem 2.3](https://arxiv.org/pdf/2010.14315#page=6)

## Precision, reconstruction and recursion

Query at $\ell,\ell n^2,\ell n^4$. Invert the odd base residue modulo $2^{k+1}$ to get both ratios at that precision. Subtract $n$ or $n^2$ in the same modulus, lift each even difference to $[0,2^{k+1})$, and halve **as an integer**. This leaves $A,B\bmod 2^k$. Starting with only $k$ input bits would leave just $k-1$ bits after halving. Skip even $A$. For odd $A$ try the residue $B A^{-1}-n\bmod 2^k$. On the squarefree promise, use $A\bmod 2^k$ alone and omit the $\ell n^4$ query, reducing the largest index to $2b+O(\sqrt b)$ bits. An unrestricted run may also try $A$ first and request the last value only if needed.

For each candidate residue list the divisors of $n$ in that class modulo $2^k$, retaining only verified proper divisors. An even residue class contains no divisor of the odd integer $n$. For odd residues the coprimality conditions hold and $2^k>n^{1/4+\epsilon}$, so Coppersmith–Howgrave-Graham–Nagaraj give deterministic polynomial bit cost for fixed $\epsilon$. If $2^k\ge n$, just test the residue directly. Handle the finitely many small inputs by trial division. Any verified split is valid, and the isolating twist guarantees one. [Coppersmith–Howgrave-Graham–Nagaraj, Corollary 3.1](https://doi.org/10.1090/S0025-5718-07-02007-8)

Recurse on both sides of a proper split. Expanding multiplicities gives at most $b$ prime leaves. Perfect-power replacement only reduces the work compared with expanding the equal factors. Trial division and twist enumeration cost $2^{O(\sqrt b)}\operatorname{poly}(b)$ bit operations. Each twist uses at most three queries and polynomial work for deterministic primality tests, integer roots, modular arithmetic and divisor reconstruction. The largest query is $\ell n^4$ and recursion never increases $b_n$. These bounds give the stated total and also recover the smallest prime factor.

## One large index and quarter-bit precision suffice

For a cofactor $n$ of bit length $b_n$, take $k=\lceil b_n/4\rceil$. For each trial twist $\ell$ in the isolation argument, the only large query needed is
$$
3H(\ell n^2)\pmod{2^{k+1}} .
$$
Compute $3H(\ell)$ exactly by enumerating reduced forms at the small prime discriminant (including the exceptional weight at 3). Even a polynomial-in-$\ell$ enumeration fits the $2^{O(\sqrt b)}$ budget. For $m\equiv3\bmod8$ the oracle value counts ordered triples of **positive** integers with $x^2+y^2+z^2=m$: all coordinates are odd and each positive triple has eight sign choices. The largest index is now at most $2b+O(\sqrt b)$ bits. This strengthens the two-index reduction above, including on cofactors with repeated prime factors.

The ordinary **unweighted count of all reduced forms** also suffices on these chosen indices. Let $C(m)$ count all reduced positive forms of discriminant $-m$ with the standard tie rule. When $\ell>3$, every primitive part has discriminant $-\ell f^2$ and has only the generic automorphisms, so $3H(\ell n^2)=3C(\ell n^2)$. When $\ell=3$ one form, obtained by scaling the primitive class at $-3$ by $n$, has weight $1/3$. All other classes have weight one. Hence $3H(3n^2)=3C(3n^2)-2$. This gives an alternative transfer from the published raw form-counting interface, applicable to arbitrary factoring inputs without imposing a primitivity filter on the counting machine. [Tulsyan, §6](https://hexagonmath.org/pdf/2611.00115v2#page=7) · [Hurwitz weights and formula](https://qseries.org/fgarvan/papers/mockmod4.pdf)

For the isolating twist use $R=3H(\ell n^2)/(3H(\ell))$ and $A=(R-n)/2$. The preceding local formula gives, with $p^e\parallel n$ isolated,
$$
A/n\equiv F_e(p^{-1})\pmod{2^k},\qquad F_e(x)=x+x^2+\cdots+x^e .
$$
Here division by $n$ uses its odd inverse. One extra input bit suffices for halving $R-n$. With the exact integer $A$, the identity $\gcd(A,n)=n/p^e$ would give the split directly. For truncated $A$ we try all odd $e\le b_n$, since a nonsquare cofactor has at least one prime of odd multiplicity.

**Recovering an odd residue.** Write $h=v_2(e+1)$ and $x=1+2y$. Then
$$
G(y)=\frac{F_e(1+2y)-e}{2^h}
=\sum_{j=1}^e \frac{2^j}{2^h}\binom{e+1}{j+1}y^j.
$$
The linear coefficient $e(e+1)/2^h$ is odd. For $j\ge2$ the identity $\binom{e+1}{j+1}=(e+1)\binom ej/(j+1)$ and $j-v_2(j+1)\ge1$ make every other coefficient even. Thus $G(y)\equiv y\bmod2$ and $G'(y)$ is always odd. If $k>h$, a compatible target determines one $y\bmod2^{k-h}$ by simple binary lifting, and at most $2^{h-1}$ odd values of $x\bmod2^k$. If $k\le h$, test compatibility with $e\bmod2^k$ and enumerate the at most $2^{k-1}$ odd residues. In either case the list size is at most $(e+1)/2$. Invert the listed residues modulo $2^k$ to obtain candidates for $p$.

**Listing divisors without any fixed exponent slack.** More generally suppose $p^E\mid n$ and a candidate residue for $p\bmod M$ is known, with $M$ a power of two and $M\ge n^{1/(4E)}$. Write $\alpha=\log_n(p^E)$, try $\beta=i/b_n$ for $1\le i\le b_n$, and try the four lifts $r$ of the candidate to modulus $4M$ in $[0,4M)$. For the correct lift and the lower grid point $\beta\le\alpha<\beta+1/b_n$, the integer $w=(p-r)/(4M)$ satisfies
$$
0\le w\le n^{(\alpha-1/4)/E}/4
\le n^{\alpha^2/E}/4\le n^{\beta^2/E}.
$$
The middle bound uses $\alpha-\alpha^2\le1/4$, and $n^{(\alpha^2-\beta^2)/E}\le4$. For $f(Y)=(Y+r(4M)^{-1})^E\bmod n$, $p^E\mid f(w)$ in the modular sense. The unknown-divisor version of Coppersmith’s theorem lists all $w$ in this range with $\gcd(f(w),n)\ge n^\beta$ in time polynomial in $b_n,E$. Verify each proposed divisor by exact division. Taking $E=1$ and $M=2^k$ proves the all-input reduction. If an odd multiplicity $e$ is to be targeted, the same proof with $E=e$ needs only $k=\lceil b_n/(4e)\rceil$ usable bits for that target. [Cohn–Heninger, Theorem 1.1](https://arxiv.org/pdf/1008.1284#page=2)

A more general decoder also works. For any monic degree-$e$ polynomial $P$ modulo $2^k$, the possible roots are covered by at most $e$ prefixes modulo $2^{\lceil k/e\rceil}$. At depth $j<\lceil k/e\rceil$, substitute $r+2^jY$ and remove the common power of two from the coefficients. Its valuation is $<k$ because the leading coefficient is $2^{je}$. Try the two root digits of the normalized polynomial modulo 2. For a root digit of multiplicity $m$, the coefficient of $Y^m$ after translation and doubling has valuation exactly $m$. The next content has valuation at most $m$, and after removal the degree modulo 2 is at most that valuation. Charging child nodes to the digit multiplicities bounds the width by $e$. Stopping at the stated depth gives a cover in polynomial bit time. Inverting odd prefixes and using $E=e$ above gives an independent quarter-bit decoder that does not rely on simple lifting for the special $F_e$. [Wright, Proposition 2.1](https://www.maths.ed.ac.uk/~wright/papers/LS.pdf#page=3) · [Kopp–Randall–Rojas–Zhu, §§2–3](https://arxiv.org/pdf/1808.10531#page=7)

The [GP regression](../experiments/hurwitz-prefixes.gp) compares the specialized lift with exhaustive odd roots for odd exponents through 31 and precisions through eight bits. It also checks the generic prefix cover and uses PARI’s small-root routine to recover 29 on $n=902393=29^3\cdot37$ from the twist $\ell=3$. The specialized decoder recovers 29 on the same input from six low input bits, one of which is consumed by halving. A separate end-to-end check scans twists, exponents and dyadic divisor sizes on five composite inputs, including repeated primes. It gives the splitter only the two truncated counts and the cofactor.

**Cost and remaining question.** Across the full recursion the bit cost is $2^{O(\sqrt b)}(1+Q)$, with $Q$ the worst deterministic cost of that single large query at the requested indices and precisions. With a promise of at most a fixed number of distinct factors, the twist scan itself has polynomial cost using the same coset theorem, and the initial exponential-in-$\sqrt b$ trial division may be omitted. For leaderboard improvement it suffices to evaluate the low bits of this three-square count in $2^{O(b/(\log b)^{1/2+\delta})}$ for some fixed $\delta>0$. A full count can already be described by three square products and a sum in the current generic counting framework. Its rate matches the benchmark. Upstream’s theta-section programs evaluate characteristic-two signed divisor coefficients. Their charged evaluator remains exponential in input bit length, and the output algebra carries different information from the integer low bits used here. [Pinned upstream theta sections](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/lambert-theta-sections.md) [Tulsyan, generic counting theorems in §§3–4](https://hexagonmath.org/pdf/2611.00115v2#page=4)

## Two unconditional fixed-modulus computations

* **Primitive parity.** For any negative order discriminant $D$, $h(D)$ is odd exactly when $|D|$ is $4,8,16,p^{2j+1}$ or $4p^{2j+1}$, where $p\equiv3\bmod4$ is prime and $j\ge0$. The genus quotient $G/G^2$ is trivial exactly when $|G|$ is odd. In Ibukiyama's Proposition 3.4 its size is $2^{t-1}$ for $D\equiv1\bmod4$ or $D\equiv4\bmod16$, where $t$ counts the distinct odd primes dividing $D$. These two cases give the two prime-power families. The other residue classes give genus number one only at $D=-4,-8,-16$. Integer roots and deterministic primality tests decide the list in polynomial bit time. In particular $h(-3)=h(-4)=h(-12)=h(-28)=1$, whereas $H(3),H(4),H(12),H(28)$ are respectively $1/3,1/2,4/3,2$. [Ibukiyama, Proposition 3.4](https://arxiv.org/pdf/2303.14983#page=12)
* **Hurwitz residues on square multiples.** Given $a>0$ with $a\equiv3\bmod4$, its base residue $3H(a)\bmod4$, and $f>0$ with $\gcd(f,2a)=1$, one Jacobi symbol gives $3H(af^2)\equiv3H(a)\,f(-a/f)\bmod4$. At $q^j\parallel f$ the local factor above, with character $\chi=(-a/q)$, is $q^j$ if $\chi=1$ and $q^j+2j\bmod4$ if $\chi=-1$. In both cases it is $q^j\chi^j\bmod4$. Coprimality ensures these local factors multiply the existing base value even when $-a$ is nonfundamental. Taking $a=3$ fixes the base residue at one and leaves $f$ entirely unfactored. [Chen–Garvan, Eq. (2.1)](https://doi.org/10.1016/j.aim.2022.108235)

## What three bits reveal on semiprimes

Suppose $n=pq$ with distinct odd primes labeled by $p\equiv1\bmod4$, $q\equiv3\bmod4$. For each eligible $\ell\equiv3\bmod8$, the **three** low bits of $3H(\ell n^2)$ and the known odd base give $R(n)\bmod8$. The following lookup uses only $n$ and that residue.

| $(R(n)-n)\bmod8$ | $((p/\ell),(q/\ell))$ |
| --- | --- |
| 0 | $(+1,+1)$ |
| 2 | $(+1,-1)$ |
| 4 | $(-1,-1)$ |
| 6 | $(-1,+1)$ |

Quadratic reciprocity gives $(-\ell/p)=(p/\ell)$ and likewise at $q$. For exactly one negative sign the difference is $2p$ or $2q$. For two negative signs it is $2(p+q)+4\equiv4\bmod8$. This explains why reducing the normalized value modulo four loses the labels and taking one more bit recovers them.

In fact, polynomially many such queries **uniquely identify** each prime among all odd primes up to $n$. To separate any distinct candidates $r,s$, require $\ell\equiv3\bmod8$, $\ell\nmid nrs$ and $(rs/\ell)=-1$. On the units modulo $8nrs$, CRT permits that sign within the specified residue class modulo 8, since $r,s$ are distinct odd primes. The combined map to the four classes modulo 8 and the sign of the quadratic character has index eight for its kernel. The least-prime-in-a-coset theorem supplies $\ell=O(\log^2 n)$ uniformly, since the modulus is at most $8n^3$. Enumerating that list and checking gcds with $n$ uses polynomial overhead. This is an information bound. A deterministic algorithm recovering the unknown prime quickly from the list of its Legendre symbols is a separate decoding problem. The GP check compared the four cases against direct Legendre symbols on 364 eligible triples of primes. [Lamzouri–Li–Soundararajan, Theorem 1.4](https://arxiv.org/pdf/1309.3595#page=3) · [Chen–Garvan, Eq. 2.1](https://qseries.org/fgarvan/papers/mockmod4.pdf)

## Numerical check

From the repository root run

~~~sh
gp -fq experiments/hurwitz-residues.gp <<<'checkHurwitzResidues()'
~~~

GP's documented `qfbhclassno(m)` returns $H(m)$, including $1/3$ at 3 and $1/2$ at 4. The check forms the integral $12H(m)$ and compares it with an independent sum of primitive `qfbclassno` values over square contents, with weights 4 at $-3$, 6 at $-4$ and 12 otherwise. At odd admissible indices it divides $12H$ by four exactly before modular arithmetic. It also counts positive ordered three-square triples directly at $m\equiv3\bmod8$ through 500. [PARI/GP reference, qfbhclassno](https://pari.math.u-bordeaux.fr/dochtml/html/Quadratic_number_fields_and_binary_quadratic_forms.html#qfbhclassno)

The check compares 250 discriminants through $|D|=500$, 724 coprime mod-four lifts, and 61 isolating twists on odd cofactors through 151 at eight precisions each. Of the 61 twists, 53 exercise squarefree cofactors. The finite check uses known factors to label the expected $C$ and PARI to supply oracle values. The asymptotic search and lattice reconstruction are paper arguments. [GP check](../experiments/hurwitz-residues.gp)
