# Small represented squares across discriminant multipliers

For $X\le N\le 2X$, let the positive multiplier $t$, the leading coefficient $a$ of a reduced positive form of discriminant $-tN$, and a coordinate bound $H$ all be at most $X^{o(1)}$. Even allowing **every** such multiplier and form, at most $X^{1/2+o(1)}$ integers $N$ have a square represented at $|u|\le H$, $1\le v\le H$. The exponent $1/2$ is attained by a family giving proper splits. Here the $o(1)$ bounds are uniform on the dyadic interval. This counts the exceptional inputs, independently of how an algorithm selects the multiplier.

## Counting the inputs

Write $F=(a,b,c)$, $F(u,v)=k^2$ and $s=2au+bv$. Reduction gives $|b|\le a$. The identity

$$
4ak^2-s^2=tNv^2>0
$$

gives $|s|\le3aH$ and $k\le H(3\sqrt a+\sqrt{2TX/a})/2$ for $t\le T$. For every triple $(a,s,k)$, the eligible $N$ divide the same positive integer $4ak^2-s^2$. A positive integer of size $X^{O(1)}$ has at most $X^{o(1)}$ divisors. Summing the number of triples over $a\le A$ gives

$$
\#N\ \ll\ X^{o(1)}H^2\big(\sqrt{TX}\,A^{3/2}+A^{5/2}\big)
$$

for polynomially bounded parameters $A,H,T\ge1$. If all three are subpower this is $X^{1/2+o(1)}$. No coprimality, primitivity or useful second representation was required. A search restricted to first squares of split prime forms of subpower norm is covered because those forms have a representative with leading coefficient $p^2$ and their reduced minimum is at most $p^2$. [Divisor bound, Lemma 30](https://terrytao.wordpress.com/2014/11/23/254a-notes-1-elementary-multiplicative-number-theory/) · [Earlier first-square result](represented-square-height.md)

In particular the fraction of comparable-size semiprimes reached by this search in $[X,2X]$ is at most $X^{-1/2+o(1)}$. The prime number theorem in residue classes gives $\gg X/(\log X)^2$ such semiprimes there, even with $N\equiv3\bmod4$: take the two primes in disjoint fixed subintervals of $[\sqrt X,\sqrt{2X}]$, one $1\bmod4$ and the other $3\bmod4$. Those inputs also survive any subpower trial division for large $X$.

**Sharpness for proper splits.** Fix $p=3$ and take $N=4p^2k^2-1$ with $k$ odd and large. The reduced first square of the split form $(p,1,pk^2)$ is $(p^2,1,k^2)$. The two coordinate vectors represent $p^2$ and $k^2$. The modular roots of $p^2$ are $p$ and $(2k)^{-1}$, and their difference gives the proper factor $2pk-1$ by gcd. There are $\asymp\sqrt X$ such inputs in $[X,2X]$ already at height one. The construction displays the two factors explicitly. No primality assumption on either factor is needed.

**Smooth values in the same boxes.** For fixed $K>1$, requiring $F(u,v)$ to have all prime factors at most $(\log X)^K$ gives at most $X^{1-1/K+o(1)}$ inputs when $A,H,T=X^{o(1)}$ and $v>0$. Indeed $F(u,v)\le X^{1+o(1)}$. For each $(a,s,v,t)$ and candidate smooth value $w$, the equation $tNv^2=4aw-s^2$ determines at most one $N$. There are $X^{o(1)}$ parameter choices. To bound the number of smooth $w$, use Rankin’s inequality with $\sigma=1-1/K+\epsilon<1$. The truncated Euler product has logarithm $O_\sigma(\sum_{n\le(\log X)^K}n^{-\sigma})=o(\log X)$. Let $\epsilon$ decrease after taking the exponent bound. Lenstra–Pomerance uses a larger smoothness bound and samples different group elements. [Lichtman–Pomerance on the Rankin bound](https://math.dartmouth.edu/~carlp/smooth051317.pdf) · [Lenstra–Pomerance, §10](https://cr.yp.to/bib/1992/lenstra.pdf)

## Recovering roots from convergents

Let $N$ be odd and nonsquare. Write $a=h z^2$ with $h$ squarefree. Assume $\gcd(2akt,N)=1$ and $htN$ nonsquare. A unit square witness gives the root $s/(2zk)$ of $h$ modulo $N$. Several forms can have the same squarefree part $h$, so their roots can be compared directly.

If $9a^2\sqrt h\,H^2<\sqrt{tN}$, one list of convergents of $\sqrt{htN}$ contains the witness for every such $a$ with this $h,t$. Indeed
$$
(2hzk)^2-htNv^2=h s^2,\qquad
\left|\frac{2hzk}{v}-\sqrt{htN}\right|\le
\frac{\sqrt h\,s^2}{2v^2\sqrt{tN}}<\frac{1}{2v^2}.
$$
Legendre’s criterion applies after reduction to $P/Q$ with $Q\le H$. Put $d=\gcd(2hzk,v)$ and $R=P^2-htNQ^2$. Then $hR=(hs/d)^2$ is an integer square, since a rational number whose square is integral is an integer. Also $P$ is a unit modulo $N$. For each convergent, test $R\ge0$, test whether $hR$ is a square, and retain $\sqrt{hR}/P\bmod N$ up to sign. On the specified witness this is $\pm s/(2zk)$. The method uses $O(1+\log H)$ exact continued-fraction steps per $(h,t)$, with polynomial bit cost per step. Any two retained roots of the same $h$ that differ up to sign yield a proper divisor by gcd, even when their multipliers differ. [Legendre’s criterion, Theorem 8.1.5](https://webspace.science.uu.nl/~beuke106/getaltheorie/getalscript.pdf#page=88)

For example $N=7199$ and $h=2$. The forms $(2,1,30^2)$ and $(2,1,283^2)$ have discriminants $-N$ and $-89N$. At height one their canonical roots are 120 and 1132, giving $\gcd(1132-120,7199)=23$. Morrison–Brillhart already pool smooth residues from different multipliers. The calculation here identifies which normalized root to recover from a represented square with a nonsquare leading coefficient. [PARI reproduction](../experiments/twisted-convergents.gp) · [Morrison–Brillhart, Remark 4.7](https://doi.org/10.2307/2005475)

## An infinite run of smooth residues with no split

For odd $m\ge1$, $N=m^2+2$ has $\sqrt N=[m;\overline{m,2m}]$. This follows directly by taking reciprocals twice. At multiplier one the convergents have alternating signed residuals $-2,1$, and their numerators modulo $N$ repeat $m,-1,-m,1$. For example, adjacent two-step advances multiply the associated numbers $P+Q\sqrt N$ by the norm-one unit $m^2+1+m\sqrt N$; its rational part is $-1\bmod N$. Every dependency with a positive square product uses an even number $2j$ of the negative rows. Its numerator product is $\pm m^{2j}\equiv\pm2^j\bmod N$, so both gcd tests are trivial. The [squarefree family](represented-square-height.md#infinite-obstruction-to-the-bounded-first-square-search) supplies infinitely many composite examples with large least prime factor. This obstruction lasts the whole multiplier-one run. Other multipliers introduce different residues.

Lehman has an all-input difference-of-squares search with trial division and multipliers on the $N^{1/3}$ scale. Schoof’s real-quadratic Algorithm 6.5 uses small auxiliary primes under its analytic hypotheses and searches at half a regulator, costing $N^{1/5+o(1)}$. The multiplier analyses of SQUFOF and the represented-value variant SQUFOF2 include distributional hypotheses. Lenstra–Pomerance’s Theorem 9.1 already gives four explicit discriminant choices per odd residue class, but relation sampling in Algorithm 10.1 still uses randomness. The pinned upstream algorithm tests a **supplied factored square** by a meet-in-the-middle search whose cost depends on the exponents. These results give no uniform deadline for obtaining a useful dependency from a short list of small convergents. [Lehman](https://doi.org/10.1090/S0025-5718-1974-0340163-2) · [Schoof, Algorithm 6.5](https://reneschoof.github.io/mcpaper.pdf) · [Bradford–Wagstaff, Theorem 4](https://homes.cerias.purdue.edu/~ssw/squfof2.pdf) · [Lenstra–Pomerance](https://cr.yp.to/bib/1992/lenstra.pdf) · [Pinned square search](https://github.com/1337isnot1337/integer-factoring/blob/1b331929bb774ae8dcb8f50cdd10a3243b7c649f/research/factored-square-box-search.md)
