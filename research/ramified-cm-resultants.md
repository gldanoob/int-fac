# A ramified CM polynomial shared by all separating fields

For every odd $N$ define the integer polynomial

$$
 A_N(X)=\prod_{f^2\mid N} H_{-8N/f^2}(X),
 \qquad V_r(N)=\operatorname{Res}(A_N,H_{-r}),
$$

where $H_D$ is the monic ring class polynomial and $r$ ranges over primes $7\bmod 8$ coprime to $N$. Each scalar is nonzero. The quadratic fields of the factors on the left have even fundamental discriminant and the target field on the right has odd fundamental discriminant. For every odd nonsquare $N$ with at least two distinct prime factors, a prime $r=O(\log^2(2N))$ gives $1<\gcd(V_r(N),N)<N$, apart from a finite range of least odd-valuation primes which trial division handles. The bit cost outside scalar evaluations is polynomial in $b=\mathrm{bits}(N)$. Its degree is the three-square representation count $r_3(2N)/12$ and lies between constant multiples of $\sqrt N/(1+\log\log(3N))$ and $\sqrt N(1+\log\log(3N))$. This reduces the degree from the public levels in the [fixed pair of CM fields](cm-isogeny-prime-filters.md). Computing the polynomial implicitly at the small fields remains the expensive step.

Write $N=s^2n$ with $n$ squarefree and $\chi=(-8n/\cdot)$. A fundamental discriminant $-8n$ has two units, so the degree sum is the Hurwitz class number $H(8N)=r_3(2N)/12$. Here $r_3$ counts signed, ordered triples, including zero coordinates. For the quantitative bound, sum the order class number formula over conductors $u\mid s$. This gives

$$
 \deg A_N=h(-8n)s\prod_{p^e\parallel s}\left(1+(1-\chi(p))\frac{1-p^{-e}}{p-1}\right).
$$

Each local multiplier is at least one. The proved Dirichlet GRH gives $L(1,\chi)\gg1/(1+\log b)$ and a relative $O(1)$ upper factor compared to the Euler product through $b^4$. Combining any conductor factor with its Euler factor at the same prime gives at most $(1-1/p)^{-1}$, including the ramified case. The product of the remaining conductor factors at $p>b^4$ is at most $\exp(O(b/b^4))$. Mertens and the fundamental class number formula now give both bounds. Explicitly writing $A_N$ requires at least as many coefficient positions as this degree. The squarefree part enters the proof, while a scalar evaluator receives $N,r$. [Gauss’s three-square formula, Theorem 1.3](https://pure.mpg.de/pubman/item/item_3118169_2/component/file_3118171/Mortenson_A%2BKronecker-type%2Bidentity_oa_2017.pdf) · [Short Euler product and local bounds](middle-three-square-bit.md#raising-the-normalized-count-on-demand) · [Lamzouri–Li–Soundararajan, Theorem 1.5](https://arxiv.org/abs/1309.3595) · [Alpöge](https://alpo.ge/remark.pdf) · [Sutherland](https://math.mit.edu/~drew/grh/)

## A zero-trace term for a prescribed odd-valuation prime

Suppose that $p\mid n$ is inert in $K=\mathbb Q(\sqrt{-r})$ and every other prime of $n$ splits in $K$. The polynomial $H_{-8n}$ is one factor of $A_N$. Its discriminant $d_2=-8n$ and $d_1=-r$ are coprime and fundamental. The Gross–Zagier product for $J=\operatorname{Res}(H_{-8n},H_{-r})$ expresses $|J|^2$ as a product of positive integers $F(2rn-t^2)$ over $t\in\mathbb Z$ with $t^2<2rn$. For such $m$ write

$$
 F(m)=\prod_{a\mid m}a^{\epsilon(m/a)},\qquad
 \epsilon(\ell)=(d_i/\ell)\quad\text{for }\ell\nmid d_i,
$$

with multiplicative extension. A trace term is a positive power of $\ell$ if $\ell$ is the unique prime of odd valuation in $m$ having $\epsilon(\ell)=-1$. All other trace terms equal one. The unit groups of both quadratic orders have order two. [Gross–Zagier, Theorem 1.3, as stated by Lauter–Viray](https://arxiv.org/pdf/1206.6942#page=1)

At $t=0$, $m=2rn$ is squarefree. Here $\epsilon(2)=1$ since $r\equiv7\bmod8$, and $\epsilon(r)=(-8n/r)=-(n/r)=1$ by reciprocity and the prescribed signs. For every $\ell\mid n$, $\epsilon(\ell)=(-r/\ell)$. Thus $F(2rn)=p^{\tau(2rn/p)}$. In particular $p\mid V_r(N)$. Conversely take any $q\mid N$ that splits in $K$. A root of $H_{-r}$ has ordinary reduction at $q$ with endomorphism algebra $K$. Each root of $A_N$ either reduces to a supersingular curve or has ordinary endomorphism algebra $\mathbb Q(\sqrt{-2n})$, a different field. Consequently $q\nmid V_r(N)$ even when $q\mid s$ or $q\mid n$. [CM reduction theorem](https://ocw.mit.edu/courses/18-783-elliptic-curves-fall-2025/mit18_783_f25_lec_s_21.pdf)

For a semiprime $N=pq$ with opposite signs the gcd therefore returns the inert prime. The same proof applies to a unique inert prime of odd valuation together with arbitrary even-valuation companions. In the Gross–Zagier product a nonzero $t$ with $(t,n)=1$ has $(2rn-t^2,n)=1$, so every prime divisor of its contribution is coprime to $n$. A nonzero $t$ sharing some but not all prime divisors of $n$ already gives a partial factorization by its gcd. The zero-trace formula itself involves divisors of $n$.

## Uniform coverage at a small ramified prime

Let $p\mid n$ be odd. Every supersingular elliptic curve $E/\overline{\mathbb F}_p$ has a CM lift of discriminant $-8n$ whenever

$$
                         2n>c(2p^2)^{337}
$$

for an absolute $c$. To see this put $R=\mathrm{End}(E)$, a maximal order of the definite quaternion algebra ramified at $p$ and infinity, and let $L=\{x\in R:\operatorname{Tr}(x)=0\}$. The Hessian of its positive integral ternary norm form $Q(x)=\operatorname{Nrd}(x)$ has determinant $2p^2$. Indeed the full norm pairing on $R$ has determinant $p^2$. The trace has image $\mathbb Z$, since the trace of 1 is 2 and its image modulo 2 is surjective in the split maximal order at 2. Therefore $\mathbb Z\cdot1\oplus L$ has index two in $R$. Its norm pairing decomposes orthogonally, with norm pairing 2 on the first basis element. This gives $2\det(\mathrm{Hess}(Q))=4p^2$. [Supersingular endomorphism orders and CM lifts](https://people.math.wisc.edu/~tonghaiyang/deuring.pdf#page=7) · [Quaternion order discriminants and local maximal orders](https://math.dartmouth.edu/~jvoight/quat-book.pdf)

The squarefree integer $2n$ is represented by this ternary form at every finite place. At $p$ the ramified quadratic extension $\mathbb Q_p(\sqrt{-2n})$ embeds in the local division algebra, whose unique maximal order contains the integral generator. At every other finite prime the maximal order is a matrix order, and the integral companion matrix of $T^2+2n$ has trace zero and determinant $2n$. Local conjugacy of maximal orders transfers it to $R$. The local trace kernel agrees with $L\otimes\mathbb Z_\ell$ by the integral trace surjectivity. Duke’s Theorem 1 now represents $2n$ integrally under the displayed bound. The corresponding endomorphism $u$ satisfies $u^2=-2n$. Deuring lifts $(E,u)$ to characteristic zero, and $\mathbb Z[u]$ is already maximal since $-2n\equiv2\bmod4$ is squarefree. Thus $H_{-8n}(j(E))=0$ in characteristic $p$. The classical fixed-$p$ theorem of Elkies, Ono and Yang also gives surjectivity for every sufficiently large fundamental discriminant with $p$ nonsplit. [Duke, *On ternary quadratic forms*, Theorem 1](https://www.math.ucla.edu/~wdduke/preprints/ternary.pdf) · [Deuring’s lifting theorem](https://webspace.science.uu.nl/~oort0109/Aug2015CMlift.pdf) · [Elkies–Ono–Yang, Theorem 1.2](https://arxiv.org/pdf/math/0512350#page=3)

## Choosing the small target without knowing the factors

Take $p$ to be the least prime divisor of $n>1$, and take any different $q\mid N$. If $n$ has at most 675 prime divisors, prescribe $(-r/p)=-1$, $(-r/q)=1$ and splitting at every other prime of $n$. If $n$ has at least 676 prime divisors, $n\ge p^{676}$. The preceding bound then holds for sufficiently large $p$. Prescribing $(-r/p)=-1$ alone makes every root of $H_{-r}$ a supersingular root of $A_N$ modulo $p$. Prescribe $(-r/q)=1$ to exclude $q$ in this case as well. The remaining bounded $p$ in this second branch can be trial factors for all sufficiently large $N$, for example by trial division through $b$.

In either branch the sign prescriptions and $r\equiv7\bmod8$ define a nonempty coset of bounded absolute index in the units modulo $8N$ by CRT. By the least-prime-in-a-coset theorem using the proved Dirichlet GRH over $\mathbb Q$, some $r=O(b^2)$ lies in this coset. Enumerate the primes in the specified progression in increasing order, test $\gcd(r,N)$ and compute scalar gcds until a proper split occurs. The algorithm needs no value for Duke's ineffective constant. Prime and perfect-power tests handle the single-prime inputs. A square input gives its integer square root. The number of recursive splitting steps is $O(b)$. [Lamzouri–Li–Soundararajan, Theorem 1.4](https://arxiv.org/abs/1309.3595) · [Alpöge’s Dirichlet GRH theorem](https://alpo.ge/remark.pdf) · [Sutherland’s independent verification of the precise statements](https://math.mit.edu/~drew/grh/)

## Finite checks

The replay constructs the integer polynomials and checks their degrees by direct enumeration of signed three-square representations. Every one of the 178 odd inputs through 599 with two or more distinct prime factors split using primes $r\equiv7\bmod8$ through 151. It checked 3,247 local signs, 750 forced inert divisibilities and 204 forced divisibilities on inputs with repeated factors. For $N=65$ and $r=23$, the resultant gcd returns 5 although the split prime 13 is nonprincipal in the field of discriminant $-23$. An independent product over the Gross–Zagier factors verified all 28 integer resultant squares, including 1,412 positive traces. For 130 pairs $p,q$ the test independently computed the supersingular polynomial via the Legendre Hasse invariant, then checked whether it divides $H_{-8pq}$ modulo $p$. All supersingular vertices were covered in 118 of those small examples. The asymptotic inequality has an ineffective absolute constant. [Executable replay](../experiments/ramified-cm-resultants.gp)
