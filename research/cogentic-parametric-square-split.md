# Obstructions to lifting the 247 and 323 monic square certificates

The signed certificate at 247 has exactly one shared argument when its cubic and marked dependency are fixed. The unit-corrected certificate at 323 has exactly one shared argument when its original quartic root and cubic mark norm are fixed, even if the other cubic unit is allowed to change. These are restrictions on the certificate data. [247 square certificate](cogentic-monic-large-primes.md) · [323 unit certificate](cogentic-monic-unit-corrections.md)

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

There is also a sign obstruction when varying the cubic while keeping these two marks and a negative cubic product norm. Write a canonical manual cubic as `F_m=X³+A X²+B X+C`. Its digit bounds give `B,C=O(m)` and `A=O(1)` as `m\to\infty`. Hence `F_m(m/2)=O(m³)`, whereas `G_m(m/2)=F_m(m/2)-m⁴/16<0` for sufficiently large `m`. Since `G_m(m)=N>0`, a positive real quartic root again excludes the minus sign. The assumed negative cubic norm excludes the plus sign. This argument concerns a shared scalar sign and the specified marks.

## The 323 cubic units

Allow all three lower coefficients of the manual cubic to vary. For `s(X)=-1-2X` and `v(X)=1-2X`, write `F=X³+A X²+B X+C`. The seed requires `Norm_F(s)=-1` and `Norm_F(v)=1`. Evaluating `8F(-1/2)` and `8F(1/2)` then forces `B=0` and `C=-A/4`. An integer polynomial with the carry's `C≡2 mod 4` requires `A≡8 mod 16`. The carry has `A≥0`, so `A≥8).

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

The reduction of `r²` in this quotient is `9/4`. Its vanishing forces `t²\mid 9`. With odd `m≥3`, this gives exactly `t=3\) and \(m=5`. The 323 quartic identity attains this bound. Multiplying the quartic root by an arbitrary power-order unit leaves this obstruction in force.

For a maximal-order unit correction with the same root, `s` is a unit times `r²` and `s+2r=-3`. Thus `r` divides 3 as an algebraic integer, and `t=|Norm(r)|` divides `3⁴`. In particular `m≤3281`. This weaker bound still excludes an infinite family, even if the maximal-order index contributes to divisibility.

## Scope

The results use exact norms, a real embedding and polynomial divisibility. They require no bound on an ideal-parity search or on the size of an order unit. They exclude lifting the specified seed data at manual degree three and give no positive subfamily for the automatic degree schedule. At the two remaining seed inputs, the proper factors are recovered by the original constant-size certificates, and trial division also finds them. Varying the marked dependency, changing the quartic base root outside its unit associates or using nonrational parameter advice can evade individual hypotheses above. No productive unbounded family using such additional data is established here.
