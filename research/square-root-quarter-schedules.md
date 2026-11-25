# What a short continued-fraction search decides about quarter-bit prediction

Let $n=pq$ with distinct odd primes $p,q\in[X,2X]$. Write $r$ for a mixed square root of one modulo $n$, and $H(z)=\operatorname{sgn}\cos(2\pi z)$. The informative part of the centered parity at a unit $t$ is $H(rt/n)$. A public family of candidate predictors examines which intervals contain $t/n$ and $a_i t/n\bmod1$, where $a_i=\lfloor\sqrt{j_i n}\rfloor$ for integers $1\le j_i\le J$. The same result holds for rounding to the nearest integer. Endpoints and the Boolean function of the interval answers may depend on $n$. Let $h$ be the number of interval tests, with repetitions at the same slope allowed. [Centered parity identity](floor-sum-and-log-parity.md#nonadaptive-queries-for-two-distinct-prime-divisors)

From $n$ and the multiplier list alone, a deterministic algorithm either factors $n$ or certifies the following simultaneous bound on **all** these predictors over uniform unit centers. For a nonempty list let $d=[\mathbb Q(\sqrt{j_1j_2},\ldots,\sqrt{j_1j_s}):\mathbb Q]\le2^{s-1}$, and set
$$
 K=\left\lfloor\frac{n^{1/(4d)}}{16(h+1)\sqrt{J+1}}\right\rfloor.
$$
For $K\ge2$ their prediction advantage above $1/2$ is at most $O((h+1)\log(2K)/K+1/\sqrt n)$ with an absolute constant. For fixed multipliers this is $n^{-1/(4d)+o(1)}$ with polynomially many tests in the input bit length $b$. The certificate also gives negligible advantage when $J,h$ are polynomial in $b$ and $s\le(1-\epsilon)\log_2 b$ for fixed $\epsilon>0$. Here negligible means smaller than every inverse power of $b$ for sufficiently large $b$. There is no assumption on how often the factor-returning branch occurs.

The algorithm takes gcds of the public slopes with $n$, ignoring multiples of $n$ which supply constant tests. For each squarefree part $v$ of a multiplier, try $\gcd(v,n)$, then enumerate the ordinary convergents $x/y$ of $\sqrt{vn}$ through $y\le\lfloor n^{1/4}\rfloor$. At a positive square norm $x^2-vny^2=z^2$, try $\gcd(x-z,n)$ and $\gcd(x+z,n)$. A square radicand with $n$ squarefree implies $v=n$ and can be handled by trial division through $\sqrt J$. Factoring the small $j_i$ by trial division and the Fibonacci lower bound on convergent denominator growth give $O(s(1+\sqrt J)\operatorname{poly}(b+\log J))$ bit cost. The same run covers all endpoints and Boolean functions. The multiplier continued-fraction search and square gcd are classical. The conclusion here connects the outcome of that finite search to the prediction bound. [Gower–Wagstaff, history of continued-fraction factoring and relation to SQUFOF](https://homes.cerias.purdue.edu/~ssw/squfof.pdf) · [Lehman, multiplier square tests](https://doi.org/10.1090/S0025-5718-1974-0340163-2)

## Why every surviving correlation yields a convergent

On the full $n$-grid replace each interval sign and the target $H$ by its Fejér mean of degree $K$. On any unit slope the argument runs over a uniform grid, so the mean absolute error is $O(\log(2K)/K+1/n)$. The symmetric kernel has mass $O(1/(Kz))$ outside a neighborhood of radius $z$. Sum this bound by distance from the two endpoints, using two as a uniform bound. Applying a Boolean function's multilinear extension costs at most the sum of the errors of the individual signs, because the extension is the expectation on independent signs with given means. The target's smoothed constant coefficient is zero. Its nonzero frequencies have $1\le |k|\le K$.

Unless there is a relation
$$
 x=l+\sum_i m_i a_i\equiv kr\pmod n,
 \qquad |l|+\sum_i|m_i|\le hK,
$$
the full-grid correlation of the smoothed product is exactly zero by additive orthogonality. The unit-grid correlation then differs from zero by at most the claimed error since the omitted fraction is $O(n^{-1/2})$ on the balanced inputs. It remains to recover a divisor whenever such a relation exists.

Put $L=(h+1)K$, $\beta=\sum_i m_i\sqrt{j_i}$, $E=x-\sqrt n\,\beta$ and $D=(x^2-k^2)/n$. The relation makes $D$ an integer. We have $|E|\le L$, $|\beta'|\le L\sqrt J$ for every conjugate, and
$$
 |D-\beta^2|\le 2 L^2\sqrt{J/n}+2L^2/n.
$$
The algebraic integer $\beta^2$ belongs to the field of degree $d$ above because $\sqrt{j_i j_l}=\sqrt{j_1j_i}\sqrt{j_1j_l}/j_1$. With $Z=16(L+1)^2(J+1)$ every conjugate of $D-\beta^2$ has magnitude at most $Z$, and the distinguished one has magnitude below $Z/(2\sqrt n)$. The definition of $K$ gives $Z^d\le\sqrt n/4^d$. Unless $D=\beta^2$ the absolute field norm would therefore be a positive integer strictly below one. Hence $D=\beta^2$.

If $\beta=0$ then $x=\pm k$, forcing one of the primes $p,q$ to divide $k$ by the mixed signs of $r$. Both exceed $K$. If $\beta\ne0$, its square is rational, so every automorphism of the full multiquadratic field sends $\beta$ to $\pm\beta$. The signs form one character under composition. The distinct squarefree radicands among the $j_i$ transform by distinct characters. Their linear combinations decompose uniquely by the elementary orthogonality of characters of the sign group. Therefore after collecting terms with the same squarefree part, exactly one coefficient survives and $\beta=m\sqrt v$ for an integer $0<|m|\le L\sqrt J\le n^{1/4}$ and a squarefree part $v$ that the algorithm tries. In particular
$$
                         x^2-v n m^2=k^2.
$$
Let $g=\gcd(|x|,|m|)$, which divides $k$. For $x'=|x|/g$, $y'=|m|/g$ and $z'=|k|/g$,
$$
 0<x'/y'-\sqrt{vn}=
 \frac{(z')^2}{(y')^2(x'/y'+\sqrt{vn})}<\frac1{2(y')^2}
$$
since $k^2<\sqrt n/2$. Legendre's continued-fraction criterion places $x'/y'$ among the enumerated convergents. Both $x'-z'$ and $x'+z'$ are positive and smaller than $n$, using $|x|\le \sqrt n\,L\sqrt J+L$ and the definition of $K$. Since their product is divisible by $n$, a proper gcd follows. This proves the dichotomy.

The argument concerns all centers at one fixed modulus. The previous size-window result counts the balanced prime pairs where a schedule *of centers* near multiples of $\sqrt n$ finds an unshifted sign error. Here the *slope of a predictor* may be near $\sqrt{jn}$ while its center ranges over every unit. [Prior size-window count](salie-and-quarter-parity.md#searching-for-a-disagreeing-frequency-near-a-square-root)

## Exact replay

Run `python3 experiments/radical-quarter.py`. The script verifies 788 short rational approximations against exact quadratic-irrational convergents. Among the 9,045 unordered prime pairs in $(1000,2000)$, the first Fermat test alone splits 1,784, the prescribed short convergents at $j=1$ split 1,298, and the five multipliers $1,2,3,5,6$ split 3,163. The first Fermat test uses $\lceil\sqrt n\rceil$, which need not be a convergent with denominator one. These finite counts measure the named searches on this population. [Replay](../experiments/radical-quarter.py)

For $n=1{,}964{,}600{,}776{,}727$, the first Fermat test misses, but the convergent $49{,}057{,}476/35$ has norm one and gives $1{,}962{,}299$ by gcd. It has numerator $35\lfloor\sqrt n\rfloor+6$. The replay also includes a 241-bit fixture with $49p-25q=2$ and the same convergent denominator. On each fixture it checks 171,171 combinations of coefficients, offsets and target harmonics for the slopes from $1,2,8,3$. The two resonant combinations on each input reduce to a single square class as predicted. PARI's `isprime` certified the two large primes printed in the script, as well as the two small ones.
