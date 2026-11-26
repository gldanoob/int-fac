# A scalar counting problem sufficient for deterministic one-third factoring

Every conditional expectation in the fixed integer-mark field selection reduces to unweighted counts of **divisors of a single primorial quotient on one arithmetic progression at a time**. Let $P_B=\prod_{\sqrt B<p\le B}p$ for $B\ge2$, and define
\[
 D_B(c,d,T)=\frac{1}{T}\#\{0\le j<T:\ c+dj\ne0,\quad |c+dj|\mid P_B\}.
\]
The parameters are in binary, with $T\ge1$. Suppose a uniform deterministic algorithm approximates this fraction to additive error $2^{-s}$ in
\[
              \operatorname{poly}(B,2^s,w)\,
                     \exp(O(\sqrt{w\log(2w)}))
                    \tag{1}
\]
bit operations, where $w$ bounds the total bit length of $B,c,d,T$. **Then the two-field construction gives a uniform deterministic $L_N[1/3,O(1)]$ complete factoring algorithm**, under the scalar-moment and extractor results used by the fixed-schedule manuscript. The proof only needs (1) on its generated progressions. The uniform large-modulus case of (1) remains open. [Fixed-schedule moment argument](cogentic-deterministic-two-thirds.md) · [Sufficient score](cogentic-conditional-score.md) · [Sum of absolute score coefficients](cogentic-universal-score-sampler.md)

## Rectangles for a pair of marked values

The geometric reduction is independent of the factoring estimates. Let $X,Y$ be independent and uniform on the integer intervals $[x,x+p-1]$ and $[y,y+q-1]$. Fix distinct integer marks $0\le a<b\le A$. Each test is the product of two unary indicators, one at $u=X+aY$ and one at $v=X+bY$, and an arbitrary acceptance predicate on $(X,Y)\bmod M$. In the factorization application $M=B^{O(1)}$. The translations and the constants of the unary tests may have either sign.

Put $\Delta=b-a$. The possible $u$'s lie in an interval of length $m=p+a(q-1)$. The allowed $v$'s at a fixed $u$ satisfy $v\equiv u\bmod\Delta$ and $l(u)\le v\le h(u)$. For $a>0$ the endpoints are
\[
\begin{split}
 l(u)&=u+\max\{\Delta y,\ \lceil\Delta(u-x-p+1)/a\rceil\},\\
 h(u)&=u+\min\{\Delta(y+q-1),\ \lfloor\Delta(u-x)/a\rfloor\}.
\end{split}
\]
For $a=0$ use $l(u)=u+\Delta y,\ h(u)=u+\Delta(y+q-1)$. The inverse map is $Y=(v-u)/\Delta,\ X=u-aY$. The two residues $u,v\bmod\Delta M$ determine integrality and both inverse residues modulo $M$. This also covers $\gcd(M,\Delta)>1$.

The endpoints are nondecreasing. Each increases by at most $A$ in one integer step, since $1+\lceil\Delta/a\rceil=\lceil b/a\rceil\le A$ for $a>0$. Across an integer panel $L\le u\le R$, the inner rectangle uses $l(R)\le v\le h(L)$ and the outer one uses $l(L)\le v\le h(R)$. Reversed endpoints give an empty interval. In each vertical slice the outer interval contains at most $2A(R-L)$ more integers than the inner one, including when the latter is empty. The same bound applies after imposing the lattice and the modular predicate.

Given a tolerated additive error $0<\eta\le1$, use panels of length at most
\[
                      t=1+\left\lfloor\frac{\eta pq}{4A m}\right\rfloor .
\]
The total loss from retaining the inner rectangles is at most $2A(t-1)m\le\eta pq/2$. At most $1+4Am^2/(\eta pq)$ panels suffice when consecutive panels have length $t$ except at the end. Within one rectangle and one admitted residue pair modulo $\Delta M$, the two smoothness tests separate exactly. Obtain their accepted fractions on the two scalar progressions, clamp to $[0,1]$, and multiply by the two exact progression lengths. Empty progressions contribute zero. If each fraction has error at most $\eta/4$, their product has error at most $\eta/2$. All admitted rectangles and residue pairs represent disjoint subsets of the $pq$ original points. Summing errors and dividing by $pq$ gives total error at most $\eta$. The number of scalar pairs is bounded by
\[
              (\Delta M)^2\left(1+\frac{4A m^2}{\eta pq}\right).
                    \tag{2}
\]
This includes nearly parallel slopes and singleton panels. A one-mark term can use an unused mark with constant indicator one. A term without smoothness tests can use two constant indicators. Two occurrences of the same smooth mark give a single Boolean indicator.

At a mark the unary test accepts the squarefree band-smooth values of $|C+D u|$ with primes dividing a known $K=k_0k'_0$ omitted. Substituting the panel's residue class for $u$ preserves this form. Test the band primes against $K$ to obtain the omissions. There are at most $2\log |K|/\log B$ for $|K|\ge1$. For each subset of them with product $e$, solve $C+D u\equiv0\bmod e$ on the scalar index progression. Division by the coefficient gcd gives one residue class or the empty set. Inclusion–exclusion now uses only $D_B$. The error in the original fraction increases by at most $2^{\#\mathrm{omissions}}$, since each restricted progression has length at most its original length. A positive divisibility requirement can be imposed in the same linear-congruence step. This includes nonunit steps and sign changes. The divisor test already enforces squarefreeness.

## Fixing the four coefficient words

Write $L=\log N,\ H=L^{1/3}(\log L)^{2/3},\ V=L^{2/3}(\log L)^{1/3}$. The fixed schedule has $\log A,\log B=O(H)$, $\log B\asymp H$ and $\log U,\log |K|=O(V)$. In each field take the two admissible uniform intervals of lengths $4UA,4U$, both powers of two. The sufficient nonnegative score has uniform mean $o(1)$. It is a signed sum of $\exp(O(H))$ separated terms with sum of absolute coefficients $\exp(O(H))$. In each field each term has at most two smooth marks and finitely many affine modular predicates at primes up to $B$. The translated affine smooth tests throughout the search have $O(V)$-bit descriptions. These are the inputs from the existing manuscript. [Rectangle and description bounds](cogentic-universal-score-sampler.md) · [Score expansion](cogentic-conditional-score.md)

Bisect the longer coefficient interval within a field at each step. Break ties deterministically. The ratio of the longer side to the shorter side stays at most $\max(2,A)$ in both children and down to singleton leaves. Thus $m^2/(pq)=O((A+1)^3)$ in (2). Finish one field and then the other. Independence separates the two field factors in every prefix box. This takes $D=O(V)$ binary decisions.

Take $\eta=\exp(-C H)$ for a sufficiently large fixed effective $C$. Formula (2) costs $\exp(O(H))$ scalar calls per factor. The omissions cost $2^{O(V/H)}=\exp(o(H))$ more calls and $O(V/H)$ extra precision bits. Each call has $w=O(V)$ and $s=O(H)$. Since $\sqrt{V\log(2V)}=O(H)$, (1) costs $\exp(O(H))$ per call. The bounded factor estimates and the coefficient sum give each child's score mean within $1/(32(1+D))$ after increasing $C$. Compute the score coefficients themselves to the precision in the original conditional-score calculation. Each parent mean is the average of its two child means. Selecting the smaller computed mean increases the true mean by at most $1/(16(1+D))$. An initial mean below $1/4$ therefore leads to a leaf with true score below one. The verified extractor accepts that leaf.

The original coefficient evaluator also factors $|a-m_0|$ for $m_0=\lceil N^{1/d_{\rm field}}\rceil$ to compute $q_0/\varphi(q_0)$. These are $O(V)$-bit integers and there are $\exp(O(H))$ of them. Use the same construction recursively on these smaller inputs. To bound all the auxiliary work, first group one parent factorization by its ordinary splitting tree with $O(L)$ nodes. All auxiliary coefficient-preparation calls arising from this tree have input logarithm at most $C_0V(L)$. Their number and the other work in this tree are at most $\exp(C_1H(L))$. A monotone worst-case envelope thus satisfies
\[
 T(L)\le \exp(C_1H(L))(1+T(C_0 V(L))).
\]
As $H(C_0V(L))/H(L)\to0$, induction gives $T(L)\le\exp(C_2 H(L))$ for a sufficiently large constant, with direct trial division at bounded sizes. A verified trial-division fallback handles failed finite searches. Under the stated hypotheses every sufficiently large surviving composite has a successful search. The prime-base gcd splitting and prime-power handling preserve multiplicities. [Coefficient evaluator](cogentic-conditional-score.md#computing-the-real-coefficients-without-a-smoothness-oracle) · [Prime-base splitting](cogentic-dense-exponents.md)

## A deterministic scalar counter for small moduli and wide windows

There is an unconditional algorithm in the following range. Split a signed progression at zero and reverse a negative progression. It suffices to count $d\mid P_B$ in a positive interval $[\ell,h]$ in one residue class modulo $q>0$. Let $T$ be the number of progression members and $\delta\in(0,1]$ the allowed additive error in their fraction. Empty and constant progressions can be handled directly. Put $W=\lfloor\log_2 h\rfloor+1$. If $T<4/\delta$, test every term directly.

Otherwise choose the least integer $K\ge16(W+1)(1+h/(qT))/\delta$. For each eligible prime compute $j_p=\lfloor K\log_2 p\rfloor$ exactly from the binary length of $p^K$. Starting with the empty product, update the counts indexed by
\[
                   \left(\sum_{p\mid d}j_p,\quad d\bmod q\right)
\]
by adding the cases including and excluding each prime once. Keep bins at most $\lfloor K\log_2 h\rfloor$. Sum the required residue at bins from $\lfloor K\log_2\ell\rfloor-W$ through that upper cutoff.

Every desired divisor is included. Any counted product has at most $W$ factors since $j_p\ge K$. Its actual value lies in $[\ell 2^{-(W+1)/K},h2^{W/K}]$. Since $(W+1)/K\le1$, the total extra real length at the two endpoints is at most $4h(W+1)/K$. Distinct prime subsets give distinct products, so in the prescribed residue there are at most $4h(W+1)/(qK)+2\le\delta T$ extra integers. The same size bound applies to all retained partial products, hence each stored count has $O(W)$ bits. This computes an upper count with the prescribed tolerance.

The sieve, integer logarithmic bins and dynamic program take $\operatorname{poly}(B,W,q,\delta^{-1},1+h/(qT))$ bit operations. Thus when both $q$ and $1+h/(qT)$ fit $\exp(O(H))$ the scalar counter has the required one-third cost, even for arrays of length $\exp(\Theta(V))$. One may replace the table's $q$ factor by the size of the multiplicative semigroup generated by the eligible residues modulo $q$, using a sorted list of occupied bins and residues. Arithmetic per entry then costs $\operatorname{poly}(\log q,W)$ bits. The general prefix construction allows larger moduli and narrower relative windows. Equidistribution on average over moduli has different quantifiers from this per-query bound. [*Smooth numbers in arithmetic progressions to large moduli*](https://doi.org/10.1112/S0010437X2500747X)

The exact replay checks 144 projected two-mark counts against coefficient enumeration, including signed values, omitted primes and noncoprime row moduli and determinants. All 288 inner/outer brackets contain the direct answers, with 123 strict brackets. Of 144 logarithmic-bin upper bounds, 22 are strict overcounts, and all 24 fine-bin checks meet their prescribed tolerance. [Finite replay](../experiments/cogentic-scalar-divisor-count.py)

## A sharp count for long progressions at arbitrary moduli

On the factoring schedule, a second algorithm handles large $q$ and sharp interval endpoints. It uses the Dirichlet-RH character estimate (1) in the [squarefree smooth windows argument](cogentic-dirichlet-smooth-windows.md#an-individual-character-estimate). Write $w$ for an upper bound on the input bit length including the endpoints, let $h$ bound the positive values being counted, and suppose $w^c\le\log B\le w$ for a fixed $c>0$. For an effective constant $D$ in that character estimate, put $\sigma_0=1/2+D\log(2w)/\log B$. For all sufficiently large $w$ we have $\sigma_0<1$. There is a deterministic counter of bit cost $\operatorname{poly}(B,w,2^s)$ and absolute error $2^{-s}$ in the fraction whenever
\[
                         T\ \ge\ C\,2^s w h^{\sigma_0}.                 \tag{3}
\]
Here $C$ is an absolute constant after fixing the character-estimate parameters. It is the **number of progression members** $T$ that must clear this threshold. There is no table indexed by $q$. On the one-third schedule the threshold is $\sqrt h\,\exp(O(H))$. Small moduli and wide windows can still use the unconditional bins above. For related square-root thresholds on ordinary smooth numbers see [Younis, Theorem 1.1 under RH](https://arxiv.org/abs/2409.05761).

**Reduction to unit classes.** Split off zero and handle the two signs by reversing the negative values. For a positive piece $[l,h]$, with nonzero step of magnitude $q$, put $g=\gcd(c,q)$ where $c$ is any progression member. If $g\nmid P_B$, the count vanishes. Otherwise divide the endpoints and the step by $g$ using inward rounding of the endpoints, and omit the prime factors of $g$ from the band. The reduced residue is a unit modulo $Q=q/g$. A remaining divisor must also be coprime to $Q$, so delete all band primes dividing $Q$. All deletions use trial division through $B$. Constant progressions take a single divisor test. This also treats the omissions from a known $K$ directly by deleting its band primes at the outset and using the modified primorial throughout. The character estimate permits the resulting $O(w)$ deletions when $K$ has $O(w)$ bits.

**Sharp endpoints.** For the resulting band $J$, put $F_\chi(z)=\prod_{p\in J}(1+\chi(p)p^{-z})$. Its Dirichlet coefficients have absolute value at most one. Take a half-integer endpoint $x$ (upper endpoint plus $1/2$, lower endpoint minus $1/2$), $\kappa=1+1/\log(2h+2)$ and height $Y=(2B+2h+4)^3$. Endpoints below one have cumulative count zero. Truncated Perron on $\Re z=\kappa$ gives the sharp cumulative character sum with error $O((h+1)\log(2h+2)/Y)$. Indeed the terms with $x/2<n<2x$ cost $O((x/Y)\sum_{n}|n-x|^{-1})$ on that range, and the rest cost $O(x^\kappa\zeta(\kappa)/Y)$.

Shift the integral to $\Re z=\sigma_0$. The finite Euler product is entire and the pole of $1/z$ is to the left. For $|t|\le Y$ the cited character estimate gives $|F_\chi(\sigma+it)|=O(1)$ on $[\sigma_0,1]$ for every nonprincipal character. For the principal character it gives the same bound when $B\le |t|\le Y$. Indeed one integration by parts bounds its prime integral by $O(B^{1-\sigma}/(|t|\log B))$. The estimate applies with $L=w$, since $\log Q,\log(2+Y)=O(w)$. For $1\le\sigma\le\kappa$, the crude product bound $|F_\chi|\le\prod_{j=1}^B(1+1/j)=B+1$ suffices on the two horizontals. Their integrals cost $O((h+1)(B+1)/Y)$.

On the new line each nonprincipal integral is $O(h^{\sigma_0}\log(2Y))$, by integrating $1/|\sigma_0+it|$. The part of the principal integral with $B\le |t|\le Y$ has the same bound. Thus write
\[
 I(x)=\frac{1}{2\pi}\int_{-B}^B
       \frac{x^{\sigma_0+it} F_{\chi_0}(\sigma_0+it)}
            {\sigma_0+it}\,dt ,
\]
using $I(x)=0$ for $x<1$. Character orthogonality, including $Q=1$, gives the sharp count in the prescribed unit class as
\[
            \frac{I(x_{\rm hi})-I(x_{\rm lo})}{\varphi(Q)}
                          + O(w h^{\sigma_0}).
\]
Averaging over the characters absorbs their number in this *absolute count* error. Each signed piece costs this error even when short. Summing both before dividing by the original $T$ gives (3).

**Computing the principal integral.** The band sieve and one finite product suffice to evaluate the integrand. On complex disks in the $t$-plane of radius $1/4$ around real panel centers, the denominator has modulus at least $1/4$, and the numerator has modulus at most $\exp(O(w+B))$ by the elementary bound of two on each Euler factor. Use real panels of half-width at most $1/8$. Cauchy's estimate gives absolute error below $2^{-s-4}$ in the whole integral by integrating Taylor polynomials of degree $C'(B+w+s)$ for a sufficiently large absolute $C'$. These coefficients are obtained by multiplying truncated exponential series and the reciprocal linear denominator. Using the disk radius as the series scale bounds the growth of coefficient absolute sums by $\exp(O(B+w))$: each prime exponential has absolute sum at most $p^{-\sigma_0+1/4}$ before the constant one is added. For $x^{\sigma_0+it}$ and the reciprocal denominator the corresponding bounds are $x^{\sigma_0+1/4}$ and $4$. All evaluations of elementary constants have polynomial bit length and cost, including reduction of real phases of size $O(Bw)$. Polynomially many guard bits therefore suffice for certified interval arithmetic. This computation can suffer cancellation of $O(B+w)$ bits, within the claimed cost.

To divide by $\varphi(Q)$ without factoring $Q$, use $Q^{-1}\prod_{p\mid Q,\ p\le 100(w+1)2^s}(1-1/p)^{-1}$. The sum of the logarithms of the omitted factors is at most $2w/(100(w+1)2^s)$, since $Q$ has at most $w$ distinct prime factors. Under (3) the normalized principal interval estimate has absolute value at most $1+O(wh^{\sigma_0}/T)$ for each sign by the count formula, so this replacement costs less than $2^{-s}/8$ in total for large enough $C$. The same choice absorbs the contour errors and quadrature. Clamping to $[0,1]$ preserves the accuracy.

The [finite replay](../experiments/cogentic-scalar-divisor-count.py) also checks the gcd reduction and its omitted-prime case by exact enumeration. A contour check computes the short principal integral, both high-frequency tails up to a finite height and the two horizontal segments. Their sum reproduces the original finite-height Perron integral. This checks the cutoff and contour orientation independently of the asymptotic character bound.

The scalar counter is still missing for intermediate lengths above direct enumeration and below (3) when the bin table is too large. The asymptotic reduction and counters have no independent Lean verification.
