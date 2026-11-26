# Smooth relation supply at the one-third scales

Write $L=\log N$, $W=L^{1/3}(\log L)^{2/3}$ and $V=L^{2/3}(\log L)^{1/3}$. The [raw monic pair](cogentic-monic-pair.md) has degrees $d,d+1$ with $d\sim(L/\log L)^{1/3}$, coefficient height $\exp(O(V))$, and odd common argument $m=\exp((1+o(1))V)$. A one-third relation bound needs a useful set of primitive marks from a grid of height $A=\exp(cW)$ at a smoothness bound $B=\exp(\beta W)$ for fixed $c,\beta>0$. The [square-class dimension criterion](cogentic-monic-square-rank.md) applies once the marks are given. It does not supply them.

## What fixed-form theorems give

For a fixed integral binary form $P$ with no repeated irreducible factor, Balog, Blomer, Dartyge and Tenenbaum give $\gg_{P,\varepsilon} A^2$ points of $[1,A]^2$ at which $|P(a,b)|$ is $B$-smooth, provided $B\ge A^{\alpha_P+\varepsilon}$ and $A$ is sufficiently large for that form. If the largest irreducible factor has degree $g$, occurs once, and exactly $\ell$ other factors have degree $g-1$, the exponent is $g-1-1/(\ell+1)$ outside the exceptional quadratic/cubic case. The product of the two distinct irreducible homogeneous forms has $g=d+1$ and $\ell=1$, hence $\alpha_P=d-1/2$. Smoothness of the product is equivalent to simultaneous smoothness. [Balog–Blomer–Dartyge–Tenenbaum, Theorem 1](https://ems.press/content/serial-article-files/43293)

This theorem yields a primitive-mark lower bound in its fixed-form range. If the all-points lower bound is $\gamma A^2$, the number of pairs with gcd exceeding an integer $D$ is at most $A^2\sum_{k>D}k^{-2}\le A^2/D$. Choose $D>2/\gamma$. Reduce each surviving pair to its primitive pair by dividing by its gcd. By homogeneity the reduced product still has a $B$-smooth absolute value, and at most $D$ of the original pairs reduce to any one pair. This gives at least $\gamma A^2/(2D)$ primitive simultaneous smooth marks. The argument does not impose the unit test modulo $N$ or exclusions for the defining discriminants.

There are two separate gaps in using this fixed-form result on the schedule. Its constants and the starting height depend on the form, which changes with $N$. Even if they were uniform, the stated range forces

$$
  \log B\ge(d-1/2+\varepsilon)\log A=(c+o(1))V,
$$

since $dW\sim V$. Conversely, fixing $\log B=\beta W$ permits at most $\log A=O(W/d)$ under this condition. That has only $\exp(o(W))$ points and cannot by itself meet the nominal full-factor-base threshold $(2d+1)(\pi(B)+1)$. It could still supply relations when occupied support or measured parity rank is much smaller.

Lachand's primitive-pair asymptotic applies to the specific fixed norm form $X^3+2Y^3$, including a range $B=A^{o(1)}$ such as $B=\exp(\log A/(\log\log A)^{1/2-\varepsilon})$ for fixed $0<\varepsilon<1/2$. The asymptotic counts one form. It neither covers successive growing degrees nor counts simultaneous values with a second algebraic form. Square sieves bound perfect-square values or related equations, and square-free sieves control square prime divisors. These conclusions give no lower bound on the values whose every prime factor is at most $B$. [Lachand, Theorem 1.1](https://aif.centre-mersenne.org/item/10.5802/aif.3189.pdf) · [Heath-Brown, square sieve](https://doi.org/10.1007/BF01475576) · [Helfgott, square-free sieve](https://arxiv.org/abs/math/0309109)

## A rigorous randomized relation theorem at the target scales

Lee and Venkatesan's Theorem 2.5 supplies a randomized relation search at the right degree, height and box scales. It uses the rational linear value $a-bm$ and one homogeneous algebraic form. Their algebraic polynomial is the base-$m$ polynomial plus an independently randomized coefficient perturbation vanishing at $m$. The proof averages over the base and perturbation, using the latter to turn each fixed marked algebraic value into an approximately uniform progression. In their notation choose $\delta=1$, $\kappa=11/10$, $\sigma=2$, and $\beta=\beta'=1$, with the degree rounded to an odd integer. Equations (4.1)–(4.2) have strict slack. In particular $\kappa>1$, $(\kappa+\sigma\delta)/2>1$, and $2\sigma=4>1+1/3+(\sigma\delta+\kappa)/3=71/30$. Theorem 2.5 then supplies $\exp((1+o(1))W)$ distinct relations for its sampled pair, in expected $\exp(\lambda W)$ time for any fixed $\lambda>71/30$, asymptotically. The tuple set in Definition 4.1 counts distinct points and does not itself impose primitivity. A normalization preserving smoothness need not preserve the count of distinct points. [Lee–Venkatesan, Theorem 2.5, Definition 4.1 and Remark 4.2](https://arxiv.org/pdf/1805.08873)

For the raw pair the first coefficient exponent is $\kappa=1+o(1)$ at $\delta=1$. Merely weakening its upper bound to $\exp(1.1V)$ does not create the independent perturbation in Definition 4.1. Nor does the identity

$$
  G_{\rm hom}(a,b)-bF_{\rm hom}(a,b)=(a-mb)a^d
$$

transfer smoothness from $a-bm$ and $F_{\rm hom}$ to $G_{\rm hom}$. Smoothness is not stable under addition. The recent Cogentic randomized factoring manuscript uses a different relation supply, with random fields and a smoothness descent rather than a lower bound for this predetermined primitive grid. Its Theorem 1.1 and the Lee–Venkatesan relation theorem both leave the fixed-pair supply unresolved. [Cogentic, §§4–6](https://github.com/google-research/google-research/blob/4a7bc8ab0bc770e71a259b7966c500496b99010a/cogentic_research_papers/integer_factorization/paper.pdf)

## Exact separation from planted norm two

For the raw pair, take $|a|\le A$, $1\le b\le A$, and assume $m>A$. If $a\ne0$, its displayed difference identity implies

$$
 \max\{|F_{\rm hom}(a,b)|,|G_{\rm hom}(a,b)|\}
 \ge\frac{|a-mb|\,|a|^d}{1+b}
 \ge\frac{m-A}{2}\,|a|^d.
$$

When $m>A+4$ this rules out simultaneous absolute norms at most two for every nonzero numerator. The only primitive candidate with $a=0$ and $b>0$ is $(0,1)$, where both norms equal $F(0)$ and simultaneous norm two occurs exactly if $|F(0)|=2$. On the one-third schedule $A=o(m)$. Apart from this exception, if both raw norms are $B$-smooth then at least one needs $(1/\beta+o(1))V/W$ prime factors counted with multiplicity, by the size lower bound alone. This does not rule out smooth larger norms.

The [planted norm-two pair](cogentic-planted-norm-two.md) instead guarantees $\lfloor h/2\rfloor$ distinct marks with both norms two on surviving sufficiently large inputs, at degrees $h+\lfloor h/2\rfloor$ and one higher. This exceeds the raw cap of one for that exact norm target. Its relations use the prime over two, so a sieve that discards every polynomial-discriminant prime discards them. The ideal support can instead be handled directly as in the planted construction. Their number is polynomial in $\log N$, and the [signature construction](cogentic-planted-unit-signatures.md) shows that they can already be independent in square classes. The exact-norm separation therefore supplies neither extra general smooth marks nor productive modular signs.
