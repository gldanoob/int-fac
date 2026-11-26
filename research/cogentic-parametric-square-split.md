# Parametric square splits for manual monic pairs

A three-mark signed product is an exact square in both orders of a canonical manual quadratic and cubic pair on infinitely many composite inputs. Its two roots give proper gcds, and an infinite subfamily has no prime divisor below the one-third trial scale. The factors are already explicit in the same parameters. The original signed certificate at 247 and unit certificate at 323 have sharp restrictions on which seed data can be preserved. [247 square certificate](cogentic-monic-large-primes.md) · [323 unit certificate](cogentic-monic-unit-corrections.md)

## Exact signed square family

Take positive integers $u,v$ with $u^2-2v^2=-1$, and set $n=2uv$ and $w=u^2+2v^2$. Then $w^2=1+2n^2$. Choose a positive odd integer $c$ divisible by the odd part of $nw$. Define

\[
m=1+c^2n^2,\qquad N=m^2+2c^2,\qquad
F=X^2+2c^2,\qquad G=X^3+(1-m)X^2+2c^2.
\]

The argument $m$ is odd and $m^2\le N<(m+2)^2$. The manual degree-two carry takes $K=(N-m^2)/2=c^2$, an odd digit below $m$, so it selects exactly $F,G$. Both are Eisenstein at two. This provides different fields and the evaluation maps $X\mapsto m\bmod N$ on their power orders. [Monic construction and carry](cogentic-monic-pair.md)

Use the three primitive marks

\[
(2cn,1),\qquad (-2cn,1),\qquad (2c^2n^4-1,2n^2).
\]

The last is primitive since its first coordinate is $-1\bmod 2n^2$. Put $L=2n^2(X+1-m)+1$. The product of the three mark polynomials $a-bX$, with common sign minus, is $S=(X^2-4c^2n^2)L$. Define $R_F=wX(1+n^2X)$ and $R_G=XL$. The exact identities are

\[
R_F^2-S=(w^2n^4X^2+2n^2L)F,\qquad
R_G^2-S=2n^2LG.
\]

They follow from $(1+n^2X)^2-L=n^4F$, $w^2X^2-(X^2-4c^2n^2)=2n^2F$, and $X^2L-(X^2-4c^2n^2)=2n^2G$. Thus the signed norm products are squares in the integers and the corresponding elements are squares in the power orders themselves. At $m$ the roots are $mw(1+n^2m)$ and $mw^2$. Here $m$ is a unit modulo $N$ because it is odd and coprime to $c$. Every odd prime of $nw$ divides $c$ and has $N\equiv1$ there. In particular $mw^2$ is a unit, so the common value $S(m)$ and every individual mark residue are units.

Put $P=m+4c^2v^2$ and $Q=m-2c^2u^2$. The Pell equation gives $1+n^2m-w=2u^4P$ and $1+n^2m+w=8v^4Q$. The product of these identities is $n^4N=n^4PQ$. Both $P,Q$ exceed one because $m-2c^2u^2=1+2c^2u^2(2v^2-1)$. Their difference is $2c^2w$, a unit modulo $N$, so they are coprime. Taking the difference and sum gcds of the two exact roots gives $P$ and $Q$, respectively, since all the extra factors are units modulo $N$.

## A one-parameter subfamily and its sizes

Fix $u=v=1$, so $n=2,w=3$, and let $c$ range over positive odd multiples of three. Then

\[
m=1+4c^2,\qquad
N=(8c^2+1)(2c^2+1),\qquad
(P,Q)=(2m-1,(m+1)/2).
\]

For $c=3$, the construction gives $m=37$, $N=1387$ and the gcds $73,19$. The three marks in this subfamily are $(4c,1),(-4c,1),(32c^2-1,8)$. Their box heights are respectively $\Theta(N^{1/4})$, $\Theta(N^{1/4})$ and $\Theta(N^{1/2})$. In the general Pell formula the individual heights are $2cn,2cn,2c^2n^4-1$, with $2cn=\Theta(N^{1/4})$ and $2c^2n^4-1=\Theta(n^2N^{1/2})$. The coefficient lists, marks and roots have $O(\log N)$ bits. Checking the supplied identities or reconstructing the simple family from $N$ uses polynomial bit complexity. An exhaustive grid would have to reach polynomial height in $N$, beyond $\exp(O(W))$ for $W=(\log N)^{1/3}(\log\log N)^{2/3}$.

In the simple subfamily, the greatest odd argument at most $\sqrt N$ gives $m$, and $(m-1)/4=c^2$ supplies the parameter check. The factors follow directly from $m$. In the general family, the same argument gives $c^2=(N-m^2)/2$ and $n^2=(m-1)/c^2$. Then $w^2=1+2n^2$, $u^2=(w-1)/2$ and $v^2=(w+1)/4$ recover the candidate parameters by integer square roots. Thus both constructions give the factors with only a constant number of exact integer operations on $O(\log N)$-bit inputs, with integer square roots computed in polynomial bit complexity.

The degree stays at two and eventually falls below the automatic degree. The existing discriminant-coprime relation collector excludes the first two marks, whose quadratic norms $2c^2w^2$ share primes with the discriminant $-8c^2$. The direct power-order identities have unit root residues and use only the three supplied marks, with no ideal-parity filter or smoothness search.

A simultaneous unimodular change of projective coordinates preserves the determinant of the second and third marks up to sign. Its absolute value is $4cn^3+2c^2n^4-1$, whereas two marks of height at most $A$ have determinant of magnitude at most $2A^2$. Thus even after such a change, the same three marks need height $\Omega(cn^2)$, which is already $\Omega(N^{1/4})$ with $n=2$.

## Avoiding small trial divisors

In the simple subfamily take $c=6a+3$ with $a\in[X,2X)$ integral and $X$ a large integer. The inputs are odd and congruent to one modulo three. For each prime $5\le p\le Z=\exp(\sqrt{\log X})$, at most four residue classes of $a\bmod p$ give $p\mid N$, from the degree-four polynomial $(8c^2+1)(2c^2+1)$. Write $e_p$ for the forbidden density and $S_0=\sum_p e_p$. Then $e_p\le4/5$ and $S_0=O(\log\log Z)$. For the latter bound, take $s=1+1/\log Z$ and use $p^{-1}\le e\,p^{-s}$ for $p\le Z$, $\sum_p p^{-s}\le\log\zeta(s)$ from the Euler product, and $\zeta(s)\le1+\log Z$ from the integral bound.

For a set of $k$ primes the CRT makes the count of indices in all its forbidden sets equal to $X$ times the product of their densities, with error at most $4^k$. Apply inclusion-exclusion to the count avoiding every prime, through the smallest odd $J\ge100(S_0+1)$. This gives a lower bound with rounding error at most $\sum_{k\le J}(4Z)^k=X^{o(1)}$. The full density product is at least $e^{-5S_0}$, since $\log(1-e_p)\ge-5e_p$. The absolute sum of its terms of degrees above $J$ is at most $\sum_{k>J}S_0^k/k!\le\sum_{k>J}(e/100)^k<\tfrac12e^{-5S_0}$. Consequently the count of survivors is at least $\tfrac12 X e^{-5S_0}-X^{o(1)}>0$ for all sufficiently large $X$.

For these inputs $\log N=(4+o(1))\log X$, so the least prime factor exceeds $\exp((1/2+o(1))\sqrt{\log N})$. This exceeds $\exp(CW)$ for any fixed positive $C$ at sufficiently large size. The argument counts suitable parameters and supplies no efficient procedure for choosing one from an interval. The algebraic factors remain explicit for every parameter.

Run `gp -fq experiments/cogentic-parametric-square-split.gp` for a replay of the polynomial identities, carry, norm squares and gcds in the simple subfamily and at a second Pell solution. [Replay](../experiments/cogentic-parametric-square-split.gp)

## A fixed cubic and rational-function roots

More generally, fix any monic irreducible `F ∈ Z[X]` and take the inputs `N = F(m) > 1`. Suppose the two proposed root residues are evaluations of fixed rational functions `U_1(T)/D_1(T)` and `U_2(T)/D_2(T)`, with integer polynomial numerators and denominators. Restrict to arguments for which both denominators and both root residues are units modulo `N`. This covers fixed polynomial field elements as well as fixed words in polynomial unit candidates, including negative exponents when those inverses exist after evaluation.

Put `H_- = U_1 D_2 - U_2 D_1` and `H_+ = U_1 D_2 + U_2 D_1`. If the two roots have equal squares for infinitely many positive integers `m`, then `F(m)` divides `H_-(m) H_+(m)` for those arguments. Divide `H_- H_+` by the monic `F` over `Z[T]`. At each such argument the integer remainder value is a multiple of `F(m)`. Its degree is lower than that of `F`, so for all sufficiently large such `m` its magnitude is smaller than `F(m)`. Infinitely many zeros force the remainder to vanish identically. Irreducibility over `Q[T]` now puts `F` entirely in one of `H_-` and `H_+`. Monic division again gives divisibility over `Z[T]`. The proposed roots consequently have one global sign modulo every admissible input and give only trivial difference and sum gcds. In particular, a fixed pair of these rational functions can yield a proper split at only finitely many arguments.

Both the fixed input polynomial and the use of the shared argument as the rational-function parameter matter. If instead `m = M(t)` and the roots are rational functions of `t`, the same proof excludes a split whenever `F(M(t))` is irreducible over `Q[t]`, after clearing fixed denominators and restricting to modulus values coprime to them. A reducible composition may put different signs on different polynomial factors. For example, `F(T) = T² + 2` and `M(t) = (t² + 1)/2` give

\[
F(M(t))=\frac{((t-1)^2+2)((t+1)^2+2)}4.
\]

This example supplies a known factorization from the parameter alone. The division argument imposes no square identities in the two power orders for such compositions.

## The signed 247 certificate

Freeze the cubic `F = X³ + 4X² + 4X + 2` and let `G_m = F + (X-m)X³`. For every odd `m ≥ 3`, the manual degree-three carry selects this pair at `N = F(m)`. Its digits are `(1,2,2)`, and `m³ ≤ F(m) < (m+2)³`. The two seed marks multiply to `S(X) = (31+3X)(1+X)`.

The norm of `S` in the cubic is `-139²`, which forces the shared sign to be minus. For odd `m ≥ 13`, the quartic has a positive real root between zero and one because `G_m(0)=2` and `G_m(1)=12-m<0`. At the associated real embedding, `-S` is negative and therefore cannot be a square. For the five smaller arguments, the quartic norm of either sign is

\[
(89373m+865558)(m+2).
\]

The values at `m=3,5,7,9,11` are respectively `5668385, 9186961, 13420521, 18369065, 24032593`. Only `9186961=3031²` is a square. The known field identities at `m=5` supply the roots and give the proper gcd 19. Thus the fixed signed dependency has exactly one productive argument, even allowing the root polynomials to be chosen afresh at every argument.

There is also a sign obstruction when varying the cubic while keeping these two marks and a negative cubic product norm. Write a canonical manual cubic as `F_m=X³+A X²+B X+C`. Its digit bounds give `B,C=O(m)` and `A=O(1)` as $m\to\infty$. Hence `F_m(m/2)=O(m³)`, whereas `G_m(m/2)=F_m(m/2)-m⁴/16<0` for sufficiently large `m`. Since `G_m(m)=N>0`, a positive real quartic root again excludes the minus sign. The assumed negative cubic norm excludes the plus sign. This argument concerns a shared scalar sign and the specified marks.

## The 323 cubic units

Allow all three lower coefficients of the manual cubic to vary. For `s(X)=-1-2X` and `v(X)=1-2X`, write `F=X³+A X²+B X+C`. The seed requires `Norm_F(s)=-1` and `Norm_F(v)=1`. Evaluating `8F(-1/2)` and `8F(1/2)` then forces `B=0` and `C=-A/4`. An integer polynomial with the carry's `C≡2 mod 4` requires `A≡8 mod 16`. The carry has `A≥0`, so `A≥8`.

For `m≥7`,

\[
F(m)\ge m^3+8m^2-2>(m+2)^3.
\]

That shared argument is outside the carry window. At `m=3,5`, the same window allows only `A=8`. The quartic mark norm is `2m-1`, which is 5 at the first argument and 9 at the second. A field square obtained from the mark by an order unit requires its norm to be a square up to sign. The argument `m=3` therefore admits no such correction, even with the entire unit group.

## The 323 quartic root

Independently, retain only the cubic condition `Norm_F(s)=-1`, the same definition of `G_m`, and the seed quartic root `r=β-1`. The norm identity gives `Norm_G(s)=2m-1`. If `r²=u s` for a power-order unit `u`, then `Norm(u)=1` and `2m-1=t²` with `t=|Norm(r)|`. The quotient of the quartic power order by `(s)` is

\[
\mathbb Z[X]/(G_m(X),-1-2X)
\cong \mathbb Z[1/2]/(16G_m(-1/2))
\cong \mathbb Z/t²\mathbb Z .
\]

The reduction of `r²` in this quotient is `9/4`. Its vanishing forces $t^2\mid 9$. With odd `m≥3`, this gives exactly `t=3` and `m=5`. The 323 quartic identity attains this bound. Multiplying the quartic root by an arbitrary power-order unit leaves this obstruction in force.

For a maximal-order unit correction with the same root, `s` is a unit times `r²` and `s+2r=-3`. Thus `r` divides 3 as an algebraic integer, and `t=|Norm(r)|` divides `3⁴`. In particular `m≤3281`. This weaker bound still excludes an infinite family, even if the maximal-order index contributes to divisibility.

## Scope

The fixed-seed obstructions use exact norms, a real embedding and polynomial divisibility. The degree-two family instead varies the order constants and uses three different primitive marks. The family proves productive square certificates at an unbounded range of sizes for the manual carry. An infinite family for the automatic degree schedule or the one-third box remains open here.
