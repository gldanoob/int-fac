# Complete factoring from a fixed Kloosterman threshold

Let $N$ be an odd integer of $b$ bits. In deterministic polynomial bit time, choose one multiple $M=NH$ with $\log_2 H=O(b^{2/3}\log b)$ and a nonadaptive list of unit frequencies $T\bmod M^2$. Complete factorization of $N$ reduces to **one bit per frequency** about the classical sum
$$
K_M(T)=\sum_{u\bmod M^2}^{*} e_{M^2}(T(u+u^{-1})),\qquad e_D(x)=\exp(2\pi i x/D).
$$
Return zero when $|K_M(T)|/M<1-2^{-12}$ and one when $|K_M(T)|/M>1+2^{-12}$. Either answer is allowed in the intervening band, independently at every query. An exact comparison with one also works. For an even input first remove its power of two. The choice of frequencies, the number of queries and all decoding have polynomial cost. Computing the answers on an unfactored modulus remains open here.

Conversely, the factorization of $M$ gives a valid gap answer in polynomial time. Thus this fixed-gap problem and complete factoring are equivalent under deterministic polynomial-time reductions. The padding costs $o(b)$ additional bits in the base of the square modulus. A deterministic evaluator taking $2^{O(B/(\log B)^\alpha)}$ on a $B$-bit modulus would give the same exponent $\alpha$ for factoring.

At the original modulus, with varying unit frequencies, the same fixed threshold gives a Las Vegas polynomial-time reduction for arbitrary inputs and a deterministic one for bounded prime support. [Unpadded threshold proof and numerical replay](unpadded-magnitude-threshold.md)

## Where the prime powers occur in the Fourier transform

At a unit frequency, stationary phase on the classes $u=v+jm$ gives
$$
K_m(t)/m=F_m(t):=\sum_{w^2=1\bmod m^2} e_{m^2}(2tw).
$$
This identity and the two-prime decoder are derived in the companion report. The expression on the right defines an auxiliary function on all residues. If $m=\prod_i p_i^{e_i}$ is odd, put $Q=m^2$, $D_i=p_i^{2e_i}$ and $c_i=(Q/D_i)^{-1}\bmod D_i$. CRT gives
$$
F_m(t)=\prod_i 2\cos(2\pi\,2c_it/D_i).
$$
Every factor has magnitude at least $2/D_i$, since $D_i$ is odd and a grid point stays at least $1/(4D_i)$ from either quarter. In particular logarithms are finite. Given the factors, $O(b+\log b)$ bits of working precision with a sufficiently large absolute constant suffice for the fixed-gap comparison, by approximating each factor to relative error $O(2^{-14}/b)$ and multiplying. [Square-modulus stationary phase](kloosterman-localization.md#stationary-phase-at-a-square-modulus) · [Williams, *Note on the Kloosterman sum*](https://people.math.carleton.ca/~williams/papers/pdf/040.pdf)

Write $G(t)=\log|F_m(t)|$. It is a sum of local functions $h_D(s)=\log|2\cos(2\pi s/D)|$, each evaluated after multiplication by a known-in-the-proof unit and reduction modulo $D$. Use normalized Fourier coefficients. For odd $D\ge9$,
$$
\widehat h_D(0)=\frac{\log2}{D},\qquad
\sum_{k\ne0}|\widehat h_D(k)|\le H_{D-1},\qquad
\widehat h_D(2)>1/3,
$$
where $H_j=\sum_{v=1}^j1/v$. The first identity follows by multiplying $|1+e_D(2s)|$ over $s$. For the others, expand $\log|1+\rho e_D(2s)|$ as $\sum_{n\ge1}(-1)^{n-1}\rho^n\cos(2\pi\,2ns/D)/n$ and let $\rho$ increase to one. For $k\ne0$, write $2j\equiv k\bmod D$ with $1\le j<D$. Each of the two progressions $n\equiv\pm j\bmod D$ alternates in sign and has decreasing terms. This bounds the coefficient by $(1/j+1/(D-j))/2$. At $k=2$ the $n=1$ term contributes $1/2$ and the remaining error is at most $(1/(D-1)+1/(D+1))/2$.

Consequently $\sum_f|\widehat G(f)|\le4b$. For every block $p_i^{e_i}$ there is a coefficient greater than $1/3$ at a frequency $f_i$ of additive order exactly $D_i$ in $\mathbb Z/Q$. Indeed its local frequency is $4c_i$, a unit. Other components contribute zero there. Recovering $f_i$ gives $D_i=Q/\gcd(Q,f_i)$ and its square root is the full block.

## A deterministic set of dilations and translations

For a cyclic group of order $Q$ and $0<\epsilon<1/2$, one can enumerate in $\operatorname{poly}(\log Q,1/\epsilon)$ time the support of a distribution with $|\mathbb E e_Q(da)|\le\epsilon$ for every nonzero $d\bmod Q$. Use a uniform prime $\ell$ from the first $\lceil4\log_2 Q/\epsilon\rceil$ primes, a uniform $0\le v<\ell$ conditional on $\ell$, and an independent uniform $0\le u<\lceil16/\epsilon^2\rceil$. Take $a=\lfloor Qv/\ell\rfloor+u\bmod Q$. If the signed representative has $|d|/Q\ge\epsilon/16$, the geometric sum in $u$ has magnitude at most $\epsilon/2$. Otherwise the floor changes the phase by less than $2\pi\epsilon/16$. The ideal average in $v$ vanishes unless $\ell\mid d$, an event of probability at most $\epsilon/4$. Enumerating every triple covers the support with no random algorithmic choices. Small-bias sampling and deterministic recovery of significant Fourier coefficients over cyclic groups are established methods. [Akavia, *Deterministic Sparse Fourier Approximation via Fooling Arithmetic Progressions*](https://people.csail.mit.edu/akavia/akaviaCOLT10.pdf) · [Akavia, Bohr-set discrepancy](https://doi.org/10.1016/j.ipl.2014.05.002)

Trial-divide $N$ through $b^5$, writing $N=tm$ with $t$ completely factored and $m$ coprime to $t$. Stop if $m=1$. Put $L=\lceil2^{14}b\rceil$, and for $|k|\le L$ let
$$
w_k=\frac{L+1-|k|}{(L+1)^2},\qquad
P_L(y)=\sum_{|k|\le L} w_k e^{2\pi i k y}
      =\left|\frac1{L+1}\sum_{j=0}^L e^{2\pi i j y}\right|^2.
$$
The kernel is nonnegative, $P_L(0)=1$, $\sum_k w_k=1$, and $|P'_L|\le2\pi L$. For sufficiently large $b$, every nonzero element of $\mathbb Z/Q$ has additive order greater than $L$. For a fixed desired frequency $f$ and any $f'\ne f$, an $\epsilon=1/(2^{14}b)$-biased dilation therefore gives
$$
\mathbb E P_L(a(f'-f)/Q)\le 1/(L+1)+\epsilon.
$$
Weight by $|\widehat G(f')|$ and sum over $f'\ne f$. There is a dilation in the enumerated support with total interference at most $4b(1/(L+1)+\epsilon)<1/2048$. It may depend on $f$. The algorithm tries the same support for every frequency.

We also need a translation $s$ for which the sample locations $s+ka+u$ are units and $|G(s+ka+u)|\le A=\lceil b^{2/3}\rceil$. The shifts are $u=0,1,2,4,\ldots,2^J$ with $J=\lceil\log_2 Q\rceil$. For each fixed $a$ there are $O(b^2)$ locations before translation.

Under uniform translation, $\mathbb E |G|^{24}=O(b^{12})$. Each $h_D$ has uniformly bounded absolute moments of every fixed order. To check this, the fraction of grid values with $h_D<-v$ is $O(e^{-v}+1/D)$ for $v\ge1$, by distance to the two zeros of cosine. Also $h_D\ge-\log D$ and $h_D\le\log2$. Integrating the tail gives the claimed local bound, including $O((\log D)^{24}/D)$. The local variables are independent by CRT. After subtracting their means, a term in the expansion of the 24th power can survive only when every index occurs at least twice, so there are $O((1+\omega(m))^{12})$ terms of bounded expectation. Their total mean before subtraction is $\sum_i(\log2)/D_i=O(1)$.

Take translations from a second small-bias support with $\epsilon'=b^{-120}$. The Fourier coefficient absolute sum of $G^{24}$ is at most $(4b)^{24}$ by convolution. Thus the moment calculation changes by at most $\epsilon'(4b)^{24}$ at any translated location. The probability of $|G|>A$ at one location is $O(b^{-4})$. Its probability of being a nonunit is at most $\sum_{p\mid m}(1/p+\epsilon')\le b(b^{-5}+\epsilon')$ by expanding the divisibility indicator in additive characters. The union bound over $O(b^2)$ locations tends to zero. Some enumerated translation works for all these shifts and indices. The finitely many input sizes preceding the asymptotic inequalities can be handled directly.

## Obtaining log samples from one-bit answers

Use $R=\lceil8(A+1)\rceil$ distinct fresh primes in $[b^2,2b^2]$ coprime to $N$, and let $H$ be their product. The prime number theorem supplies enough for sufficiently large $b$. Sieving and gcd tests find them deterministically. For each factored block $p^e\parallel t$, with $D=p^{2e}$, choose a unit $v_D$ within two of $D/6$. The known log contribution $c_t=\sum_D\log|2\cos(2\pi v_D/D)|$ is $O(1)$ in absolute value. For $D\ge100$ each term is $O(1/D)$ by the mean value theorem near $2\cos(\pi/3)=1$. The smaller odd moduli contribute an absolute constant.

Take the fixed grid of thresholds $\theta\in[-A-1,A+1]\cap 2^{-8}\mathbb Z$. At each fresh prime $P$, set $D=P^2$ and choose a unit $v_D$ for which
$$
\log(2\cos(2\pi v_D/D))=(-\theta-c_t)/R+O(1/D).
$$
The desired positive cosine factor stays in a compact interval inside $(0,2)$ because $|\theta+c_t|/R<1/3$ for large $b$. Round a solution of the real cosine equation to a nearby integer and adjust by one for coprimality. Approximating that real position to absolute error $1/4$ suffices. The total log gain from the known components is $-\theta+O(R/b^4)$, within $2^{-12}$ of $-\theta$ for large $b$.

At a unit sample location $v\bmod Q$, choose the global unit given by the CRT congruences
$$
T\equiv v(M/m)^2\pmod Q,\qquad
2T\equiv v_D(M^2/D)\pmod D
$$
for each known component of $(M/m)^2$. The normalized log magnitude at this global frequency is $G(v)-\theta$ to within $2^{-12}$. Issue all threshold queries. On $|G(v)|\le A$, the greatest grid threshold receiving one is within $1/128$ of $G(v)$, even for adversarial answers in the allowed band. Indeed $|\log(1\pm2^{-12})|<2^{-11}$, and the threshold spacing is $1/256$. One may use a finite default value if every threshold returns zero. Discard translations containing nonunits using gcds before issuing queries.

## Recovering and checking every factor

For each tried dilation, translation and mesh point $x\in[0,1)$ with spacing at most $1/(2^{16}bL)$, form
$$
H_u(x)=\sum_{|k|\le L}w_k\,\widetilde G(s+ka+u)e^{-2\pi i k x}.
$$
At the exact tag $x=af/Q$, the ideal result differs from $\widehat G(f)e_Q((s+u)f)$ by at most the interference bound. Moving to the nearest mesh point costs at most $(4b)2\pi L/(2^{16}bL)$ in absolute value. The weights sum to one, so the log-sample errors cost at most $1/128$. These errors leave room for numerical rounding and keep the total below $1/64$.

For a desired coefficient $\widehat G(f)>1/3$ the ratios $H_{2^j}(x)/H_0(x)$ are consequently within $1/10$ of $e_Q(2^j f)$. Skip tags with $|H_0(x)|<1/4$. Round each direction to the nearest of 32 equally spaced directions. The error is less than $1/16$ turn, because $2/10+\pi/32<2\sin(\pi/16)$. Starting at the last direction, choose in reverse order the one of the two modular halves nearest the preceding observed direction. The correct choice is within $1/16+1/32<1/4$ and halves the previous error. Multiplication by $Q$ and nearest integer rounding recover $f\bmod Q$. All grid choices can use fixed slack, with polynomial-bit trigonometric arithmetic and exact rational halving. [Detailed halving argument](kloosterman-localization.md#keeping-the-error-bounded-through-doubling)

For each proposed nonzero frequency test whether $Q/\gcd(f,Q)$ is the square of a full prime-power divisor of $m$. Check with integer roots, primality testing and division. Every prime-power block appears for some dilation, translation and tag. All queries are determined by $N$ before any replies, and every enumeration above has polynomial size. This is a paper runtime bound. Rubinstein uses estimates of Kloosterman sums in a different factoring algorithm. Publication priority for the threshold reduction has not been established. [Rubinstein, *The distribution of solutions to xy=N mod a with an application to factoring integers*](https://arxiv.org/abs/math/0610612)


## Finite replay

The bit-only replay uses twelve known padding primes and 65 gain settings per sampled local frequency. Every reply is Boolean. Inside the allowed gap the synthetic oracle answers with the parity of the global frequency, and the decoder receives no local factors. The fixture generator uses the factors to supply stationary values and to verify the output. For $N=1{,}041{,}537{,}223$ the decoder recovered $1009,1013,1019$ from 2,053,675 unit queries, including 115 replies in the gap. It also recovered four distinct primes on $N=1{,}063{,}409{,}504{,}683$ and the blocks $307^2,1013,1019$ on $N=97{,}288{,}247{,}503$. The latter two runs used 2,713,555 and 2,511,210 bits, respectively. Direct inverse sums at $35^2$ and $105^2$ separately check both comparison outcomes and CRT transfer.

Run `python3 -B experiments/kloosterman-threshold.py`. The finite code shortens the theorem's exhaustive search to one publicly chosen dilation, omits nonunit samples, clips the log levels and uses a floating-point FFT to select tags. Exact squaring, gcds and division verify the proposed blocks. The uniform guarantee is supplied by the full search in the proof. [Finite bit-only decoder](../experiments/kloosterman-threshold.py)
