# Weighted residue counts below the square-root threshold

Under the individual Dirichlet-RH estimate used for the scalar counter, averaging over a multiplicative coset of size $S$ reduces the absolute count error bound by a factor $S$. On the fixed Cogentic schedule this gives certified accuracy at progression lengths below the individual square-root threshold. The fixed coefficient score keeps the residue at each mark constant. [Individual scalar counter](cogentic-scalar-divisor-count.md#a-sharp-count-for-long-progressions-at-arbitrary-moduli) · [Fixed intermediate score](cogentic-intermediate-score-budget.md)

## Weighted scalar estimate

Let $J\subseteq(\sqrt B,B]$ be the eligible band after deleting primes dividing $q$. Use the band-omission and bit-length conditions of the character estimate. For each unit $r$ modulo $q$, let $C(r)$ count the squarefree products of primes in $J$ in the integer interval $[l,h]$ congruent to $r$. Let $G=(\mathbb Z/q\mathbb Z)^\times$ and $g=|G|$. For a real weight $\nu$ on $G$, set $\widehat\nu(\chi)=\sum_{r\in G}\nu(r)\overline{\chi(r)}$. Then
\[
 \left|\sum_r \nu(r)C(r)-\frac{\widehat\nu(1)}{g}\sum_r C(r)\right|
 \le E\Lambda(\nu),\qquad
 \Lambda(\nu)=\frac1g\sum_{\chi\ne1}|\widehat\nu(\chi)|,\qquad
 E=O(w h^{\sigma_0}).
\]
Here $w$ is a binary length envelope and $\sigma_0=1/2+O(\log(2w)/\log B)$ is the line in the sharp scalar counter. Indeed $\sum_r C(r)\chi(r)$ is the interval sum of coefficients of the twisted Euler product. The nonprincipal Perron shift in that counter bounds each such sum by $E$ before orthogonality. Inserting the inverse transform of $\nu$ proves the inequality. Parseval gives $\Lambda(\nu)\le\|\nu\|_2$, with the counting norm on $G$. It also gives a root mean square bound across unit residues at the same modulus and interval.
\[
 \left(\frac1g\sum_r\left|C(r)-g^{-1}\sum_s C(s)\right|^2\right)^{1/2}
 \le \frac{E}{\sqrt g}.
\]

If $\nu$ is uniform on a coset of a subgroup $K\subseteq G$ of size $S$, its transform has modulus one on the $g/S$ characters trivial on $K$ and zero otherwise. Thus $\Lambda(\nu)=1/S-1/g$. In this case the algorithm needs only the mass $\widehat\nu(1)=1$ and a lower bound for $S$. For other probability weights or signed weights of total variation at most one, supply the total mass and a certified upper bound for $\Lambda(\nu)$, for example from a bound on $\|\nu\|_2$. Evaluation requires no enumeration of the weight support or of the characters.

Take an interval $[bq,(b+T)q-1]$ for positive integers $b,T$, so each residue occurs exactly $T$ times. Write $M=\sum_r C(r)$. For a probability weight approximate the weighted fraction by $M/(gT)$. Compute $M/(qT)$ by the existing sharp scalar count with modulus one and the same band $J$, using accuracy a sufficiently small constant times $\delta/(w+1)$. The bound $q/\varphi(q)\le1+\omega(q)=O(w)$ follows from $p_j\ge j+1$ for the ordered prime factors. Compute an approximation to $q/\varphi(q)$ by testing primes through $O(w/\delta)$. The omitted logarithmic factors sum to at most $O(w)$ divided by that cutoff. This gives $O(\delta)$ error in the weighted fraction since $M/(gT)\le1$. For signed weights multiply the principal approximation by $\widehat\nu(1)$. After fixing sufficiently large effective constants, the conditions for accuracy $\delta$ are
\[
       qT\ge C_0\delta^{-1}w^2 h^{\sigma_0},
 \qquad T\ge C_0\delta^{-1}w h^{\sigma_0}\Lambda(\nu).
\]
The bit cost is $\operatorname{poly}(B,w,\delta^{-1})$ with the supplied weight data. The $qT$ condition comes from counting the untwisted total. For comparison, Younis obtains asymptotics under RH for ordinary smooth integers in intervals longer than $h^{1/2+\epsilon}$. For weights of total mass zero, returning zero uses only the second condition. [Sharp count and totient truncation](cogentic-scalar-divisor-count.md#a-sharp-count-for-long-progressions-at-arbitrary-moduli) · [Younis, Theorem 1.1](https://arxiv.org/abs/2409.05761)

## Fixed constants and a nonzero weighted fraction

On the fixed schedule put $\lambda=100001$ and $\rho=\lambda/3000$. Take $\log h=(\lambda+o(1))V$, $\log q=(1+o(1))V$, $\log T=(\tau+o(1))V$ and $\delta=e^{-CH}$ for fixed $C>0$. Then $h^{\sigma_0}=\sqrt h\,e^{O(H)}$. If $\Lambda(\nu)\le e^{(-\kappa+o(1))V}$, the two sufficient conditions hold throughout
\[
                  \tau>\max(49999.5,50000.5-\kappa).
\]
A distribution with maximum atom at most $e^{(-1+o(1))V}$ permits $50000<\tau<50000.5$ by the counting norm. A coset with $\log S=(1+o(1))V$ permits $49999.5<\tau<50000.5$. The same $\tau>50000$ gives a root mean square error $e^{-\Omega(V)}$ for the normalized individual counts under uniform unit residues. [Fixed parameters](cogentic-deterministic-two-thirds.md#fixed-parameters)

For an explicit coset, multiply successive odd primes until $q$ first crosses $2^{\lfloor V/\log 2\rfloor}$. The primes used are $O(V)$ by the prime number theorem, so this costs $\operatorname{poly}(L)$ and $\log q=V+O(\log V)$. Take the units with Jacobi symbol $+1$ modulo $q$. The Jacobi character is the product of the nontrivial Legendre characters at every prime dividing $q$. By the Chinese remainder theorem changing a single prime coordinate can change membership, so the mask on the units requires the full modulus. The support has size $g/2$, and $g$ and $\Lambda(\nu)=1/g$ are available from the construction. The modulus removes no band primes, since $O(V)<\sqrt B$.

For any fixed rational $49999.5<\tau<50000.5$ one can deterministically find an aligned interval at this length with weighted fraction at least $e^{(-\rho+o(1))H}$. Start with an aligned interval of height and width comparable to $e^{\lambda V}$ and with a power of two for the initial number of blocks. The untwisted density in that interval is at least $e^{(-\rho+o(1))H}$. For this lower bound take the existing Gaussian progression estimate at modulus one and relative width $e^{-H}$, centering the Gaussian at each integer of the middle half of the interval. Uniformly over those centers the saddle has $(1-\alpha)\log B=(1/3+o(1))\log L$, so the estimated density is $e^{(-\rho+o(1))H}$ with absolute error $e^{-\Omega(V)}$. Averaging over the centers gives a point weight $O(1/(qT))$ at each integer because the widths are comparable and a Gaussian of width $W$ has lattice sum $O(W)$ here. The mass outside the original interval is negligible. The average Gaussian density therefore lower bounds the untwisted interval density up to a constant factor. The weighted estimate with $C>\rho+1$ transfers this lower bound to the coset.

Bisect by whole blocks. The parent fraction is exactly the mean of its two child fractions. Estimate both to accuracy $e^{-CH}$ and retain the larger estimate until $T=2^{\lfloor\tau V/\log 2\rfloor}$. Each step loses at most $2e^{-CH}$ from the true fraction and there are $O(V)$ steps. The final fraction still has the stated lower bound, with bit cost $e^{O(H)}$. In this example returning zero would exceed the prescribed error, even though every progression being averaged has length below $\sqrt h$ by an exponential factor in $V$. [Gaussian progression estimate](cogentic-dirichlet-smooth-windows.md) · [Fixed saddle scale](cogentic-intermediate-score-budget.md#dyadic-subboxes-and-the-linear-mass-term)

## Sparse weights and the point-class limitation

In the fixed first-field box, the coefficient contribution at a mark $a$ is always a multiple of $q_a=P_0\ell|a-m|$. Averaging over the slope preserves the single residue at that mark. Combining marks typically changes the modulus, interval and omitted primes. Even if these data were shared and a weighted sum used only $S_0=e^{O(H)}$ residues, Fourier inversion would give
\[
 \Lambda(\nu)\ge\max_r|\nu(r)|-\frac{|\widehat\nu(1)|}{g}
 \ge\frac{\|\nu\|_1}{S_0}-\frac{|\widehat\nu(1)|}{g}.
\]
This applies to signed weights, including exact cancellation of the principal term. After normalizing $\|\nu\|_1=1$, this certificate provides no gain on the $V$ scale for such sparse weights. [Actual projected progressions](cogentic-intermediate-score-budget.md#dyadic-subboxes-and-the-linear-mass-term)

Two integer profiles exhibit the limitation of the character inequalities with the principal total supplied exactly. Fix a residue $r_0$ and let the first profile have $u$ in every class. Change it to $u+(g-1)d_0$ at $r_0$ and $u-d_0$ in every other class, with integers $0<d_0\le u$ and $u+(g-1)d_0\le T$. The change in each nonprincipal character sum is $gd_0\chi(r_0)$. Both profiles meet the same bound if $E\ge gd_0$, while the point-class fraction changes by $(g-1)d_0/T$. For $1<\tau<50000.5$, take $u=\lfloor T e^{-\rho H}\rfloor$ and $d_0=\lfloor u/g\rfloor$. These choices are eventually positive and feasible, with $gd_0\le u\ll w h^{\sigma_0}$. The normalized change has size $e^{(-\rho+o(1))H}$, the size of the reference probability. Thus the individual character inequalities and principal total alone cannot certify the needed point-class error. These profiles concern the information in those inequalities. Actual smooth counts may have additional constraints.

The [finite replay](../experiments/cogentic-weighted-smooth-count.py) directly counts 267 band products in eight unit classes modulo 15. It checks both Jacobi coset averages, the Parseval identity and the integer-profile construction.

## Translation averages at a fixed residue

There is a different averaging gain that keeps the residue fixed. Fix any unit $r$ modulo $q$, a reference height $X\ge2$, and a log-width $0<d\le1/4$. For $x\in[X,2X]$ let $C_r(x,d)$ count the same band products in $(x,e^d x]$ and class $r$. Write $s=\sigma_0+it$ and define
\[
 P(x,d)=\frac{1}{2\pi\varphi(q)}
    \int_{-B}^{B} x^s \frac{e^{ds}-1}{s} F_{\chi_0}(s)\,dt.
\]
The sharp scalar counter gives
\[
  \frac1X\int_X^{2X}|C_r(x,d)-P(x,d)|^2\,dx
                 \ll X^{2\sigma_0}d+1.                         \tag{1}
\]
In its Perron proof, use the difference of the two endpoints and take $Y=(2B+8X+4)^3$. Real endpoints are allowed at cost $O(1)$ in the truncated sum. The integer nearest either endpoint contributes at most a constant to the truncation error, including an integer endpoint itself, and all other nearby integers satisfy the same harmonic bound as at half-integers. The horizontal integrals cost $O(X(B+1)/Y)$. On the shifted line subtract the principal integral on $[-B,B]$. The remaining multiplier, apart from $x^s(e^{ds}-1)/s$, is
\[
 {\bf1}_{|t|\le Y}\,\frac1{\varphi(q)}
 \left(\sum_{\chi\ne\chi_0}\overline{\chi(r)}F_\chi(s)
         +{\bf1}_{|t|>B}F_{\chi_0}(s)\right).
\]
Its absolute value is uniformly bounded by the existing character estimate, including the principal high-frequency bound. The window multiplier satisfies
\[
 \int_{\mathbb R}\left|\frac{e^{d(\sigma_0+it)}-1}{\sigma_0+it}\right|^2dt
       =2\pi\int_0^d e^{2\sigma_0 y}\,dy=O(d).
\]
This is Plancherel applied to the exponential on $[0,d]$. Apply it again to the entire shifted integral in the variable $\log x$ after dividing by $x^{\sigma_0}$. On $[X,2X]$, the measures $dx/X$ and $d\log x$ differ by a factor between one and two. This proves (1). Its constants are uniform in the specified residue. [Sharp Perron shift](cogentic-scalar-divisor-count.md#a-sharp-count-for-long-progressions-at-arbitrary-moduli)

Here is a consequence for a family of discrete scalar calls. Fix $T\ge1$ and $\Delta=qT$, and suppose the starting points $x_j$ are consecutive multiples of $\Delta$, up to translation, filling an interval of length $W\le X/2$ in $[X,2X-\Delta]$. Write $K$ for the number of starts and assume $W\asymp K\Delta$. Take $0<\epsilon<1/16$ with $\Delta\le \epsilon X/8$. Partition the region of starts into intervals of length at most $\epsilon X/8$. For each nonempty interval choose a reference $x_*$ inside it and set $d=\log(1+\Delta/x_*)$. To estimate the count for $(x_j,x_j+\Delta]$, average $P(x,d)$ over $[x_j,x_j+\epsilon\Delta/8]$. For these $x$, the two intervals have corresponding endpoints within $O(\epsilon\Delta)$ of each other. They therefore differ by at most $O(\epsilon T+1)$ progression members. The jitter intervals are disjoint, and Jensen's inequality and (1) give a mean squared error for the normalized estimates of at most
\[
 O\left(\frac{X^{2\sigma_0}(\Delta/X)+1}
                {\epsilon^2 W T^2/X}
          +\epsilon^2+T^{-2}\right).                         \tag{2}
\]
Indeed the bound for each subregion of starts uses the integral over $[X,2X]$, scaled by $X/(\epsilon\Delta)$, and there are $O(\epsilon^{-1})$ subregions. Dividing by $KT^2$ gives (2). The approximation allows additional numerical error at most $\epsilon$ per normalized estimate. Averaging $x^s$ on a jitter interval replaces it by
\[
 \frac{(x_j+\epsilon\Delta/8)^{s+1}-x_j^{s+1}}
      {(\epsilon\Delta/8)(s+1)} .
\]
The resulting integral on $[-B,B]$ has the same fixed-radius complex disks and exponential bounds as the scalar principal integral. Rounding $d$ to sufficiently many guard bits, computing the scalar elementary functions, using the totient truncation and integrating Taylor polynomials as there costs $\operatorname{poly}(B,w,\epsilon^{-1})$ per estimate. For the unknown totient, compute the integral divided by the truncated totient and use the multiplicative enclosure, then clamp to $[0,T]$. This keeps the same error bound up to constants even in a call where the prediction was outside the count range.

If $\log X=(100001+o(1))V$, $\log q=(1+o(1))V$, $\log T=(\tau+o(1))V$ with $1<\tau<50000.5$, and $W\ge Xe^{-O(H)}$, take $\epsilon=e^{-(C+1)H}$ for any fixed $C$. The first term of (2) is $e^{-(\tau-1+o(1))V}$. More precisely the discrepancy caused by translating the true intervals and numerical evaluation is bounded by a constant times $\epsilon+T^{-1}$ on *every* start, while the first term bounds the mean square of the remaining error. Hence only an $e^{-(\tau-1+o(1))V}$ fraction of starts can exceed error $e^{-CH}$. This applies to fixed-class horizontal scalar slices whose allowed origins range over an original full-width coefficient interval and whose mark keeps its sign. The proof allows losing a factor $X/W$ for shorter ranges of starts. It establishes small exceptional sets over translations and leaves open how to certify a particular child after earlier coefficient decisions.

A bounded multiplier can concentrate error at a prescribed start. In the shifted integral replace the multiplier after the subtraction of the principal term by
\[
  A(t)=e^{-it(\log x_0+d/2)}{\bf1}_{|t|\le1/d}.
\]
Its modulus is bounded by one, as required by the Plancherel argument. At $x=x_0$, write $(e^{ds}-1)/s=\int_0^d e^{sy}\,dy$. For every pair $(t,y)$ in the resulting integral the phase is $t(y-d/2)$, of absolute value at most $1/2$. Thus its real part has size $\gg x_0^{\sigma_0}$, although its mean square still obeys (1). This example concerns the bounded-multiplier argument and places no lower bound on the error for true Euler products.

## Lookahead within a certified parent

Let a parent have $R$ progression members in a fixed residue and be tiled by $K=R/T$ aligned children of length $T$. Write $p_j$ for the child fractions and $\widehat p_j$ for their estimates in (2). Fix a tolerance $0<\eta<1/16$, take $\epsilon$ a sufficiently small fixed multiple of $\eta$, and assume $T\gg\eta^{-1}$ and $qT\le\epsilon X/8$. The absolute bound on the number of inaccurate children is
\[
  \#\{j:|\widehat p_j-p_j|>\eta\}
  \le B_T,\qquad
  B_T=C_1\frac{X^{2\sigma_0}}{\eta^4T^2}                       \tag{3}
\]
for a sufficiently large effective $C_1$. To see this, keep the uniform jitter and numerical errors separate as in (2), so their combined size is at most $\eta/2$. Multiply the remaining mean square bound by $K\asymp W/(qT)$ and apply Chebyshev. The other term from (2), $X/(\eta^4 qT^3)$, is bounded by the term in (3). The same bound holds for any distinct subset of children. It can be applied to a collection of aligned intervals that covers them, or to their disjoint jitter intervals directly.

Suppose $\log R=(\pi+o(1))V$, $\log T=(\tau+o(1))V$, $\log X=(\lambda+o(1))V$ and $\eta=e^{-CH}$. The bound (3) has leading exponent $\lambda-2\tau$ in $V$. It ensures that at least one child is accurate when $K>B_T$, which holds for $\pi+\tau>\lambda$. This distinguishes two uses of a lookahead.

- An enumerable list of $M=e^{O(H)}$ children can defeat (3) by cardinality only when $T\gg \eta^{-2}X^{\sigma_0}/\sqrt M$. A jump of $O(H)$ binary decisions can affect the secondary exponent, while any fixed $\tau<\lambda/2$ leaves (3) larger than the whole list.
- A wider jump may give $K>B_T$ and still leave too many exceptional children to store or test individually. Even granting a list of $\lfloor B_T\rfloor+1$ promising alternatives, a scheme that verifies each by scanning its $T$ members uses $\exp((\lambda-\tau+o(1))V)$ operations in that budget. This exceeds the square-root exponent for every fixed $\tau<\lambda/2$.

For example, suppose a parent has known average at most $u$ for a nonnegative quantity, and the child predictors for this quantity have error at most $\eta$ outside at most $B_T$ children. Given all predictions, it suffices to keep the $\lfloor B_T\rfloor+1$ smallest when $K(1-u/v)>2B_T+1$ for a chosen $v>u$. By Markov, at least $K(1-u/v)$ children have true mean at most $v$. After removing inaccurate predictions there are enough predictions below $v+\eta$. At least one of the kept predictions is accurate, and its true mean is at most $v+2\eta$. This certifies that a list contains a suitable child. It gives no test for which child to descend into. The same reasoning can absorb $e^{O(H)}$ scalar tests by summing their exceptional budgets, provided they have the same family of child origins and the scalar accuracies absorb the score weights. That changes secondary factors and keeps the leading threshold above.

The analytic assumptions used to obtain (3) allow all members of a short list to be inaccurate, even given the exact parent count at the chosen residue and the exact untwisted total on every aligned subinterval. To show this, choose two distinct unit residues $r,r'$ in a modulus $q>2$ with at least two units. View the parent as $R$ whole $q$-blocks inside $[X,3X]$. Fix any inspected list of at most $M$ aligned subintervals of at most $T$ blocks each. Let $S$ be the union of the inspected blocks and choose a disjoint reserve $S'$ of equal size inside the parent, possible if $2MT\le R$. Define two binary coefficient sequences. In both there is one occupied integer per block in $S\cup S'$ and none elsewhere. In the first sequence place the occupied integers in residue $r$ on $S$ and $r'$ on $S'$. In the second exchange the residues. The untwisted totals agree on every aligned interval. Both parent counts at $r$ equal $|S|$, but each inspected child has fraction one at $r$ in the first sequence and zero in the second.

For every character, the twisted finite Dirichlet sum of either sequence has absolute value at most $2MT X^{-\sigma_0}$ on $\Re s\ge\sigma_0$. This follows termwise, including for the principal character, and is $e^{-\Omega(V)}$ for $M=e^{O(H)}$ and fixed $\tau<\lambda/2$. Thus the bounds on the shifted line and on the original Dirichlet coefficients used in the translation proof hold for both sequences. Each short principal predictor, divided by the queried length, has size
\[
 O\left(MT\, \frac{Bq}{X\varphi(q)}\right)=e^{-\Omega(V)}.
\]
Indeed the interval kernel on $[-B,B]$ has size $O(d)$ with $d=O(qT_j/X)$ for a queried length $T_j$, and the same estimate holds under endpoint jitter. The sequences therefore agree at any $e^{-CH}$ precision in these predictions despite opposite exact answers on the list. The construction also preserves every exact ancestor count when the reserve is chosen inside the current parent. It applies to a list determined by such a common rounded transcript. The sequences are examples under the analytic inequalities, without the additional algebraic structure of smooth-product Euler coefficients. A search that uses that structure to choose or validate its short list remains open.

For search for a child of higher scalar density, the obstruction also permits adaptive access to exact untwisted counts. Fix in advance $R_0=\min(R,\lfloor X^{\sigma_0}e^{-H}\rfloor)$ occupied blocks and supply their entire occupancy pattern, along with the exact parent count $\lfloor R_0/2\rfloor$ at $r$. Leave the occupied residue in each block unspecified. Every assignment between $r$ and $r'$ meets the same shifted-line bounds. All its short principal predictions are $O(R_0 Bq/(X\varphi(q)))$ after normalization, so the common transcript can use zero at accuracy $e^{-CH}$. If $MT<R_0/2$, answer every exact inspected child count at $r$ by zero. After the queries, the required $\lfloor R_0/2\rfloor$ hits can all be assigned outside their union. The parent has positive density, and no inspected child reaches it. Including a final untested output in the inspected list proves the same failure for any particular output of such a short-list rule. For a parent of size at least $e^{(\lambda/2+o(1))V}$, the inequality $MT<R_0/2$ holds for $M=e^{O(H)}$ and every fixed $\tau<\lambda/2$. This is an information obstruction for the bound-based scalar rule, independent of how neighboring prefixes are prioritized.
