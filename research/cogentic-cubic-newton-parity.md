# Cubic private ideal parity from Newton slopes

For a nonzero element of a cubic field, its monic characteristic polynomial decides whether its principal ideal has all even valuations above an unfactored composite rational norm divisor. The calculation uses Newton polygons, the defining discriminant, gcds, and integer square tests. It needs no integral basis, overorder, or integer factorization. Named prime ideals remain necessary to label bounded shared rows on a grid. [Implementation and replay](../experiments/cogentic-cubic-newton-parity.py)

## A single rational prime

Let $Q(T)$ be the monic minimal polynomial of a nonrational integral cubic element $z\ne0$. For a known rational prime $p$, group the intervals of the lower Newton polygon of $Q$ by their distinct slopes. Write $\lambda\ge0$ for the negative of a polygon slope and $h$ for the horizontal length of that edge. The corresponding $h$ roots have valuation $\lambda$ with $v_p(p)=1$. Their product factor belongs to $\mathbb Q_p[T]$ since valuation is invariant under local Galois action. Each prime ideal $\mathfrak p$ represented in this group has normalized valuation $e_{\mathfrak p}\lambda$ and contributes $e_{\mathfrak p}f_{\mathfrak p}$ roots to the group.

| Length $h$ | Slope valuation $\lambda$ | Criterion for all normalized valuations to be even |
| ---: | --- | --- |
| 1 | Integer | $\lambda$ is even |
| 3 | Integer or denominator 3 | The numerator of $\lambda$ in lowest terms is even |
| 2 | Denominator 2 | The criterion fails |
| 2 | Even integer | The criterion holds |
| 2 | Odd integer | The degree-two local factor is a ramified quadratic field |

For length three and nonintegral slope, the denominator forces ramification index three. For an odd integer slope and odd group length, at least one branch has odd ramification index because $\sum e_{\mathfrak p}f_{\mathfrak p}$ is odd. For length two and nonintegral slope, the ramification index is two and the normalized valuation is odd. For length two and odd integer slope, the two roots can give two linear fields, an unramified quadratic, or a ramified quadratic. Only the last possibility has even normalized valuations.

In this last case the complementary linear root has a different slope. Write $Q=Q_2Q_1$ for the quadratic and linear factors over $\mathbb Q_p$. The identity

$$\operatorname{disc}(Q)=\operatorname{disc}(Q_2)\operatorname{Res}(Q_2,Q_1)^2$$

shows that the full polynomial discriminant has the same local squareclass as the quadratic discriminant. For odd $p$, this class gives a ramified quadratic exactly when its $p$-valuation is odd. For $p=2$, write the full discriminant as $2^k u$ with $u$ odd. The local quadratic is ramified exactly when $k$ is odd or $u\equiv3\pmod4$. To see the even-$k$ case, odd units congruent to 1 modulo 8 are squares, units congruent to 5 give the unramified quadratic using $T^2-T+(1-u)/4$, and units congruent to 3 modulo 4 give the Eisenstein polynomial of $\sqrt u-1$. This also distinguishes wild ramification with even discriminant valuation from an unramified companion case.

A rational nonzero element can be handled separately. At every rational prime some branch in degree three has odd ramification index. Hence all ideal valuations there are even exactly when its rational valuation is even. For fractional elements one can first multiply by a rational square to make the element integral.

## Test an odd composite without finding its prime divisors

Let $M$ be a positive odd divisor of $|Q(0)|$. Build pairwise coprime gcd-free atoms from $M$, the nonzero coefficients of $Q$, and $|\operatorname{disc}(Q)|$. For an atom $q$ dividing $M$, read the exponent of $q$ in each input integer by exact division. If $p\mid q$ and $w=v_p(q)$, the actual coefficient and discriminant valuations at $p$ are those exponents multiplied by $w$. Missing coefficients have infinite valuation. Scaling by $w>0$ leaves the polygon edge lengths intact and multiplies every base slope valuation $\lambda_0$ by $w$.

Each base edge can therefore be checked on the whole atom as follows.

- For length one or three, an odd numerator of $\lambda_0$ requires $q$ to be a square. Multiplying by $w$ and canceling a possible factor three from the denominator preserves parity of the numerator.
- For length two and base slope of denominator two, require $q$ to be a fourth power. If $w$ is odd, the scaled slope is still half-integral and fails. If $w\equiv2\pmod4$, the scaled slope is an odd integer and the discriminant valuation is even because it is a multiple of $w$. That branch also fails. A multiple of four gives an even integer slope.
- For length two and base slope an odd integer, require $q$ to be a square when the atom's discriminant exponent is even. An odd $w$ gives an odd slope and is allowed exactly when the discriminant valuation is odd. An even $w$ always passes. An even integer base slope also always passes.

These checks use only exact integer square and fourth-power tests. Every gcd refinement decreases the sum of the logarithms of the distinct positive atoms by at least $\log 2$. The input list has constant length. All exponents and Newton hull operations have polynomial bit cost in the coefficient size and $\log M$. For an all-prime test, apply this procedure to the odd part of $|Q(0)|$ and apply the separate dyadic test at 2 when needed.

## Use on raw mark grids

For a raw monic cubic $P$ and $z=a-b\alpha$, with $b\ne0$, compute the integral monic polynomial

$$Q(T)=(-b)^3P((a-T)/b).$$

Its discriminant is $b^6\operatorname{disc}(P)$. At a prime dividing a primitive mark norm, $b$ is a unit, so the same discriminant squareclass can be taken directly from $P$. Remove the rational primes through a cutoff $Y\ge2H^2$ from each norm on the height-$H$ grid. For the remaining odd residual, the composite test gives exact parity at all prime ideals above its support. A prime ideal over $p>Y$ is private to its mark, since two distinct primitive marks sharing it would force $p\mid ab'-a'b$ with $0<|ab'-a'b|\le2H^2$. Thus an odd residual decision permits deletion of precisely those columns with a nonzero private row. The retained columns need only the exact bounded named-prime rows. Those can be computed using the [named-prime algorithm](cogentic-monic-named-primes.md) or the factor-free local models in the [singular ideal parity construction](cogentic-monic-singular-ideals.md). The raw grid requires neither a full maximal order nor the composite tame-overorder calculation for its cubic tails. The standard box and cutoff scales give total $\exp(O(W))$ arithmetic for this ideal-parity stage. Subsequent squareclass and splitting constraints remain separate.

Run `python3 -B experiments/cogentic-cubic-newton-parity.py`. The replay compares 2,340 marked residual, all-prime and dyadic decisions with PARI maximal-order ideal valuations. Its dyadic controls cover all four odd unit classes modulo eight with even discriminant valuation. For $Q=T^3+2T^2+2q$, with $q=(13\cdot19)^k$, the residual $q$ passes only at $k=4$ among $k=1,2,3,4$. A mixed exponent control with $q=13^4\cdot19^2$ fails. A separate 150-bit composite atom checks the same square versus fourth-power distinction without asking the oracle to factor it. The oracle is used only on the comparison fixtures.
