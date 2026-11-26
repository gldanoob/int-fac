# Exact local divisibility for the monic pair

For the [monic pair](cogentic-monic-pair.md), write $F(m)=G(m)=N$, $d=\deg F\ge2$, and $G(X)=F(X)+(X-m)X^d$. Use $U=F_{\rm hom}(a,b)$, $V=G_{\rm hom}(a,b)$ and $C=F(0)$ on a primitive integer mark $(a,b)$. The identities give exact joint prime-power tests even at singular roots. On marks with $\gcd(a-mb,N)=1$, the rational primes shared by the two norms are exactly the prime divisors of $\gcd(a,C)$.

## The common divisor

The homogeneous identity is $V=bU+(a-mb)a^d$. Also $U\equiv Nb^d\pmod{a-mb}$ and $\gcd(b,a-mb)=1$, so
\[
 \gcd(U,V)=\gcd(U,(a-mb)a^d),\qquad
 \gcd(U,a-mb)=\gcd(N,a-mb).
\]
Use nonnegative gcds and $v_p(0)=+\infty$. The congruence for modulus zero means the equality at $a=mb$. At a prime $p\mid a$ one has $p\nmid b$ and $p\mid U$ exactly when $p\mid C$. If $v_p(a)>v_p(C)$, then the constant term $Cb^d$ has strictly lower valuation than the other terms, so $v_p(U)=v_p(C)$. Otherwise $v_p(a^d)\le d\,v_p(C)$. This proves
\[
 \gcd(U,a^d)\mid |C|^d,\qquad
 \gcd(U,V)\mid N|C|^d=|\operatorname{Res}(F,G)|.
\]
On marks with $\gcd(a-mb,N)=1$ the common divisor is exactly $\gcd(U,a^d)$. Adding the single test $\gcd(a,C)=1$ therefore enforces coprime norms. At a prime dividing $N$, eligibility removes the common slope $m$. The slope $0$ remains a common root precisely when $p\mid C$ and $p\nmid m$. For instance, $N=129$, $m=5$ and $F(X)=X^3+2X-6$ have this surviving common slope at $p=3$.

## Mixed prime-power thresholds

For $p\mid b$, primitivity and monicity make both valuations zero. For $p\nmid b$ the two valuations equal those of $F(x)$ and $G(x)$ at the affine slope $x=a/b$ in $\mathbb Z_p$. Set $D(x)=(x-m)x^d$. For thresholds $u,v\ge0$ with $k=\max(u,v)>0$, choose $P=F$ when $u\ge v$ and $P=G$ otherwise. Then
\[
 v_p(U)\ge u,\quad v_p(V)\ge v
 \quad\Longleftrightarrow\quad
 P(x)\equiv0\pmod {p^k},\qquad D(x)\equiv0\pmod {p^{\min(u,v)}}.
\]
Indeed the larger threshold implies the smaller threshold for the anchor polynomial, and subtracting the values imposes exactly the remaining condition. A zero threshold on $D$ accepts every slope.

For $t>0$ put $s=v_p(m)$. The solutions of $D(x)\equiv0\pmod{p^t}$ are the following disjoint residue classes, with the latter row containing two classes.
\[
\begin{array}{ll}
t\le(d+1)s&
 x\equiv0\pmod {p^{\lceil t/(d+1)\rceil}},\\[2mm]
t>(d+1)s&
 x\equiv0\pmod {p^{\lceil(t-s)/d\rceil}}
 \quad\text{or}\quad
 x\equiv m\pmod {p^{t-ds}} .
\end{array}
\]
When $v_p(x)<s$, the valuation of $D$ is $(d+1)v_p(x)$. When $v_p(x)>s$ it is $d\,v_p(x)+s$. At equality it is $ds+v_p(x-m)$. These three cases also give the formula when $p\nmid m$.

In the uniform primitive residue classes modulo $p^k$, there are $p^k+p^{k-1}$ projective classes, each of size $\varphi(p^k)$. The affine classes arise by scaling $(x,1)$ by a unit. The classes with $p\mid b$ arise by scaling $(1,y)$ with $p\mid y$. For a nontrivial joint threshold, divide the number of surviving affine roots modulo $p^k$ by $p^k+p^{k-1}$ to get its exact probability. If the local unit condition $a-mb\not\equiv0\pmod p$ is imposed, discard $x\equiv m\pmod p$ and use denominator $p^k$. Exact valuation masses follow by differences of the four neighboring threshold probabilities. CRT multiplies the probabilities of any finite collection of such local tests, conditional on primitivity and any imposed unit conditions at the included primes.

The resultant controls which common branches are available. If $p\nmid NC$, both positive thresholds are impossible. If $p\mid N$ and $p\nmid C$, then $p\nmid m$ and the common affine roots modulo $p^k$ for $u=v=k$ consist of $x=m\bmod p^k$ exactly when $k\le v_p(N)$. The local unit condition discards this class. If $p\mid C$ and $p\nmid N$, then $p\nmid m$ and the common roots are on the zero branch alone. When $F'(0)$ is a unit, this branch is a simple root of both polynomials, since $d\ge2$. The root $\alpha$ of $F$ in $p\mathbb Z_p$ has $v_p(\alpha)=v_p(C)$ by $F(\alpha)=0$ and the unit linear term. The diagonal joint threshold therefore has one root class modulo $p^k$ for $k\le d\,v_p(C)$ and none after that. At $p=2$ Eisenstein gives a different exact law. Both valuations are one for even $a$ and zero for odd $a$, with probabilities $1/3$ and $2/3$ on primitive classes. The even-numerator case has odd $b$ and every term above the constant is divisible by four.

### Counting singular roots without expanding $p^k$ residues

Work in a cylinder $x=r+p^j y$ and substitute into $P$. If all coefficients have valuation at least the current threshold, keep the entire cylinder. Otherwise strip their common $p$-power from both the coefficients and the threshold and let the resulting polynomial be $Q$. Its reduction modulo $p$ is nonzero. Only the root residues $s_0$ of that reduction can lead to children, given by $y=s_0+pz$.

For a reduced root of multiplicity $\mu$, the coefficient of $z^\mu$ in $Q(s_0+pz)$ has valuation exactly $\mu$. Every coefficient above it has valuation greater than $\mu$. After stripping the new common power of $p$, the reduced degree at a continuing child is at most $\mu$. A terminal child has no descendants. Since the multiplicities of the roots sum to at most the reduced degree, the sum of continuing degrees at a depth is at most $\deg P$, and at most $\deg P$ nodes are created at each next depth. Each step also strips at least one more $p$ from the threshold. The full root set modulo $p^k$ is therefore a disjoint union of at most $1+k\deg P$ cylinders with this same bound on the total number of visited nodes. Scanning $p$ residues at each node and shifting coefficient lists costs $p\,\operatorname{poly}(d,k,\log p,\log(2+\|P\|_\infty))$ bit operations. Coefficient growth is bounded by the original coefficient lengths plus $O(dk\log p+d\log(d+1))$ under the substitutions and divisions.

Intersection with the at most two difference cylinders and removal of an optional $m$-class now use just residue compatibility and cylinder sizes. Compatible classes with moduli $p^i,p^j$ intersect in the class with the higher modulus and contribute $p^{k-\max(i,j)}$ affine roots modulo $p^k$.

## Avoidance on finite sets of primes

For a prime $p$ let $M_p=p+1$ be the number of primitive projective classes modulo $p$. If imposing the unit condition at this prime, remove $m$ and take $M_p=p$. Let $f_p,g_p,c_p$ count the eligible roots of $F$, the eligible roots of $G$ and their intersection. The probability of avoiding both divisibilities is $(M_p-f_p-g_p+c_p)/M_p$. The difference from the product of the two marginal avoidance probabilities is $c_p/M_p-f_pg_p/M_p^2$. In particular outside the resultant support the correlation is nonpositive, and is negative when both root sets are nonempty.

With the local unit restriction imposed at primes dividing $N$, every shared slope that survives is zero, so $c_p\le {\boldsymbol 1}_{p\mid C}$. For any finite prime set above $Y\ge4(d+1)$, the ratio of the product of joint avoidance probabilities to the product of the marginal avoidance probabilities is
\[
 \prod_{p>Y}\left(1+\frac{M_pc_p-f_pg_p}{(M_p-f_p)(M_p-g_p)}\right)
 =\exp\!\left(O\!\left(\frac{d(d+1)}Y+
                  \frac{\log |C|}{Y\log Y}\right)\right),
\]
where the product runs over the chosen set. Indeed $f_p\le d$, $g_p\le d+1$, and the logarithm at each prime is $O(d(d+1)/p^2+{\boldsymbol 1}_{p\mid C}/p)$. Sum $p^{-2}$ using the integer tail and bound the number of prime divisors of $C$ above $Y$ by $\log |C|/\log Y$. For the scheduled pair $\log |C|\le \log(2m)$, so a sufficiently large fixed power of $\log N$ provides a cutoff with vanishing error. The estimate measures the joint local avoidance correction within the CRT model.

There is also a direct finite-box comparison. Take $Q=\prod p^{k_p}\le A$ and let $\delta_p$ be the fraction of primitive classes modulo $p^{k_p}$ satisfying the chosen local test, counting any unit condition as part of the test. Assume invariance under multiplication by a unit, as holds for the valuation and unit tests here. In the box $|a|\le A$, $1\le b\le A$, the fraction of primitive integer marks satisfying all the tests is
\[
             \prod_{p\mid Q}\delta_p
                      +O\!\left(\frac{Q\log(2A)}A\right).
\]
To prove this, let $\Omega$ be the CRT set of admissible residue pairs modulo $Q$, and use Möbius inversion for the remaining common divisors $h$ of $a,b$. The tests force $(h,Q)=1$, and dividing by such $h$ leaves the allowed residue set unchanged. For each $h\le A/Q$, the count is $2A^2|\Omega|/(hQ)^2+O(AQ/h+Q^2)$ by the interval count in each residue pair. For $h>A/Q$, the total count is $O(AQ+A\log(2A))$ by bounding each contribution by $(2A/h+1)A/h$ without any local restrictions. Extending the main-term sum over $h$ to infinity costs $O(AQ)$. The resulting main count is $2A^2|\Omega|Q^{-2}\prod_{p\nmid Q}(1-p^{-2})$. Dividing by the primitive box count, obtained by the same argument with $Q=1$, yields the formula. Conditions at primes outside $Q$ are outside this comparison.

## An exact deterministic sieve

Enumerate primitive marks in the box and test $\gcd(a-mb,N)$. Any proper gcd is a factor of $N$. For the remaining unit marks store both absolute norms. For every prime $p\le B$, scan the affine residues for roots of the two polynomials. For each root $r$, loop over denominators $b$ with $p\nmid b$ and visit only the progression $a\equiv rb\pmod p$. Each visit to a stored norm removes every copy of $p$. The final residual is one exactly when the norm is $B$-smooth. The progression criterion follows from primitivity and monicity, and norms are nonzero since the polynomials are irreducible of degree at least two. This works at repeated roots and at every prime dividing the resultant. If coprime norms are desired, the test $\gcd(a,C)=1$ can be applied when initializing the marks.

An elementary prime enumeration and residue scan cost $B^2\operatorname{poly}(w)$, where $w$ bounds the relevant input and norm bit lengths and the degree. Each root produces $O(A^2/p+A)$ progression visits. There are at most $2d+1$ roots across the two polynomials at any prime, and the total number of successful divisions is $O(A^2w)$ because each division reduces a stored norm by at least a factor two. The full bound is
\[
   \bigl(B^2+A^2+dA^2\log(2B)+dA\pi(B)\bigr)\operatorname{poly}(w)
\]
using the harmonic sum over integers as an upper bound for $\sum_{p\le B}1/p$. This gives deterministic exact filtering at the one-third parameter scale when $\log A,\log B=O((\log N)^{1/3}(\log\log N)^{2/3})$. A lower bound for the number of residual pairs becoming $(1,1)$ and a rank bound for those relations remain open. The finite-box estimate only transfers tests whose combined modulus is small compared with the box.

Run `python3 -B experiments/cogentic-monic-local-laws.py` to check the formulas against direct integer valuations and mark counts on nine fixtures with degrees through 13. The replay checks 1,989 joint threshold counts, 25,641 primitive marks, nine complete CRT boxes, and exact sieve acceptance against direct factor removal. A degree-13 singular root modulo $3^{120}$ checks the compressed representation without expanding its residues. [Replay](../experiments/cogentic-monic-local-laws.py)
