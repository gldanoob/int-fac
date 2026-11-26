# Exact unit corrections split the monic pair at 323

The single parity dependency at $N=323$ yields a factor after multiplying its cubic and quartic elements by units. The corrected elements are exact squares with a common value modulo $N$. Their roots reduce to $72$ and $4$, giving $\gcd(72-4,323)=17$. The certificate uses exact arithmetic in the two power orders and ordinary modular arithmetic. [Monic pair and parity dependency](cogentic-monic-pair.md)

## Exact certificate

Let $m=5$ and write

$$
F(X)=X^3+8X^2-2,\qquad G(X)=X^4-4X^3+8X^2-2.
$$

Write $\alpha$ and $\beta$ for the corresponding order generators and $\rho_F,\rho_G$ for evaluation at $m$ modulo $N$. Both maps exist since $F(5)=G(5)=323$. The dependency is the mark $(-1,2)$. Its elements are $s_F=-1-2\alpha$ and $s_G=-1-2\beta$, both reducing to $-11$. The norm formula for a linear element gives $\mathrm N(s_F)=-1$, $\mathrm N(1-2\alpha)=1$ and $\mathrm N(s_G)=9$. An element of a power order with norm $\pm1$ is a unit of that order because its integral multiplication matrix has determinant $\pm1$.

Take the cubic root candidate $r_F=(1-2\alpha)s_F^{-2}$. It is a power-order unit, as is its correction $u_F=r_F^2/s_F$. In the quartic take $r_G=\beta-1$ and

$$
u_G=2\beta^3-9\beta^2+20\beta-9.
$$

The identity

$$
(-1-2X)(2X^3-9X^2+20X-9)-(X-1)^2=-4G(X)
$$

gives $u_Gs_G=r_G^2$. Since $\mathrm N(r_G)=G(1)=3$, the correction has norm $3^2/9=1$ and is a power-order unit. Reduction now gives

$$
\rho_F(r_F)=-9/121=72,\qquad \rho_G(r_G)=4\pmod {323}.
$$

Both squares are $16$ modulo $323$. Since the original elements reduce to the same unit, the corrections themselves also reduce to the same value. The gcd is a proper divisor, with quotient $19$.

## Criterion once base corrections are available

Suppose two orders admit compatible reductions to $R=\mathbb Z/N\mathbb Z$ and their dependency products $s_i$ have the same invertible reduction. Given base identities $r_i^2=u_i s_i$ with order units $u_i$, put $q=\rho_1(r_1)/\rho_2(r_2)$. For any selected subgroups of the two unit groups let $J$ be the product of their images in $R^\times$. The ratios of corrected roots obtained by multiplying the base roots by these units are exactly $qJ$. A common corrected value exists within this family if $qJ$ meets $\{z\in R^\times:z^2=1\}$. A proper gcd from the two roots exists exactly when this intersection contains an element other than $1$ and $-1$. Indeed the root in the denominator is invertible, so the difference gcd is $\gcd(z-1,N)$. If that gcd equals $1$, $(z-1)(z+1)=0$ in $R$ forces $z=-1$, and if it equals $N$ then $z=1$.

Equivalently, alignment is possible exactly when $q^2\in J^2$. If one alignment $z$ is known, the full set of aligned ratios is $zJ[2]$, where $J[2]=\{j\in J:j^2=1\}$. This follows because the quotient of any two alignments belongs to $J$ and has square one. In particular, after a trivial alignment $z=\pm1$, the full unit search can split exactly when $J[2]$ itself contains a nontrivial root of unity. This criterion has no unit word length bound.

For maximal orders with reduction maps and their full unit groups, this criterion covers every unit correction. The quotient of any alternate root by the corresponding base root has square an order unit. That quotient and its inverse are algebraic integers, so the quotient itself is a unit of the maximal order. The certificate at $323$ only requires the two specified power orders.

An explicitly supplied modular square root $t$ of a correction ratio can also rescale the second root. With $q$ now the ratio of the two chosen root residues, $t^2=q^2$, so the proper gcd criterion becomes $q/t\notin\{1,-1\}$. Taking $t=\pm q$ supplies only a trivial gcd. The displayed certificate uses equal correction residues directly.

## Bounded replay

Run from the repository root.

```sh
python3 -B - <<'PY'
import runpy

run_gp = runpy.run_path("experiments/cogentic-monic-pair.py")["run_gp"]
run_gp("monic_unit_fixture", (35, 77, 143, 221, 323),
       "cogentic-monic-pair-squares.gp", "cogentic-monic-unit-corrections.gp")
PY
```

The [replay](../experiments/cogentic-monic-unit-corrections.gp) uses the existing relation grid $|a|\le64$, $1\le b\le64$, and smoothness bound $151$. The four smaller fixtures have nullity zero. For the one singleton dependency at $323$, it searches for base roots among $1$ and $X+c$ for $-8\le c\le8$, using exact division and an integral norm-unit test. It keeps the power-order units among $a-bX$ and $-a-bX$ on both sides. It searches products of those units with total absolute exponent at most eight, in order of increasing total, until their corrected residues have the same square and their ratio differs from $\pm1$. The first success uses the cubic exponents $(-2,1)$ and no quartic multiplier. The expected factors are checked only after the result is returned by the search.

The existing relation replay uses PARI for number-field initialization, ideal computations and exact field square tests. Given the mark, the following standalone call repeats the unit search using only polynomial quotient arithmetic, resultants to evaluate norms, and modular arithmetic.

```sh
gp -fq <<'GP'
read("experiments/cogentic-monic-unit-corrections.gp");
print(monic_unit_search(323,5,[x^3+8*x^2-2,x^4-4*x^3+8*x^2-2],[-1,2])[4]);
GP
```

| $N$ | Parity nullity | Returned divisor and quotient |
| ---: | ---: | --- |
| 35 | 0 | |
| 77 | 0 | |
| 143 | 0 | |
| 221 | 0 | |
| 323 | 1 | $17,19$ |

The finite certificate establishes that the mixed-sign obstruction for this dependency can be removed while preserving a common modular value. The replay gives no bound for finding suitable dependencies, base corrections or a splitting unit word as $N$ grows.

## Fixed holdout

The holdout inputs, in order, are $187,209,247,299,391,437,10403$. The fixed parameters are manual cubic and quartic degrees, the existing grid $|a|\le64$, $1\le b\le64$, smoothness bound $151$ and cap of $1023$ nonzero signed parity dependencies. The unit search advances only if the nullity is one, the dependency is a singleton and the sign check yields no certificate. It uses base roots $1$ and $X+c$ for $-8\le c\le8$, the same mirrored-mark unit candidates and total absolute exponent at most eight. All seven cases share the Python harness's 15-second GP timeout. These inputs and limits were set before execution.

```sh
python3 -B - <<'PY'
import runpy

run_gp = runpy.run_path("experiments/cogentic-monic-pair.py")["run_gp"]
run_gp("monic_unit_holdout", (187, 209, 247, 299, 391, 437, 10403),
       "cogentic-monic-pair-squares.gp", "cogentic-monic-unit-corrections.gp")
PY
```

| $N$ | Retained marks | Parity nullity | Dependencies tested | Unit search started | Splits |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 187 | 16 | 0 | 0 | 0 | 0 |
| 209 | 16 | 0 | 0 | 0 | 0 |
| 247 | 14 | 0 | 0 | 0 | 0 |
| 299 | 1 | 0 | 0 | 0 | 0 |
| 391 | 17 | 0 | 0 | 0 | 0 |
| 437 | 2 | 0 | 0 | 0 | 0 |
| 10403 | 2 | 0 | 0 | 0 | 0 |

The first holdout run took about $0.76$ seconds wall time. Every retained parity matrix had full column rank. No base roots, unit candidates or unit words were tested, so this holdout measures the lack of dependencies at these parameters. It leaves the success rate of unit correction given a dependency unmeasured.
