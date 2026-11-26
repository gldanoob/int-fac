# Productive mixed relations with fixed primitive marks

Four fields of independently growing even degrees can have distinct one-dimensional square kernels on the same four fixed primitive marks. The generators sum to zero across the four fields, and their square roots give a proper gcd. Every pairwise square kernel on this pool is zero. The construction uses a designed input family and supplies simple common roots on all four branches. [Mixed-field square relations](cogentic-mixed-square-graphs.md)

## Field design

Take an integer $v\ge2$ and set $m=2v^2$, $N=m^2+1$. Below we require $v$ to be divisible by finitely many fixed primes. Use the following linear marks and auxiliary linear polynomials.

| $j$ | $\ell_j(X)$ | $h_j(X)$ |
| ---: | --- | --- |
| 1 | $3-4X$ | $2-X$ |
| 2 | $-3-4X$ | $1-2X$ |
| 3 | $15-8X$ | $4-X$ |
| 4 | $5-12X$ | $3-2X$ |

All four marks are primitive and have height at most $15$. The identities $h_j(X)^2\equiv\ell_j(X)\pmod {X^2+1}$ give modular root residues $h_j(m)$. These are units if $5,13,17\mid v$. In fact $h_j(m)h_j(-m)$ reduces to one of $5,13,17$ and $N\equiv1$ at those primes. Index $j$ cyclically and put
\[
 D_-=m+1-2v,\qquad D_+=m+1+2v,\qquad z=(1+m)/(2v)\pmod N .
\]
The factors $D_-,D_+$ are greater than one, have product $N$, and are coprime since their difference is $4v$ and neither has a prime divisor in common with $2v$. In particular $z=1$ modulo $D_-$ and $z=-1$ modulo $D_+$. This choice is explicit from $v$.

For each edge $i$ joining columns $i,i+1$, choose a monic polynomial $q_i$ of degree $d_i\ge5$ with
\[
 q_i(3)=0,\qquad q_i\equiv X^{d_i}+1\pmod 2,\qquad
 q_i(m)\equiv z^{[i=1]}h_i(m)h_{i+1}(m)\pmod N .
\]
Here $[i=1]$ is one for the first field and zero otherwise. Define $F_i=q_i^2-\ell_i\ell_{i+1}$. These monic polynomials vanish modulo $N$ at $m$. Modulo two they are $X^{2d_i}$. The mark constants alternate between $3$ and $1$ modulo four, so each adjacent product is $3$. Since $q_i(0)$ is odd, $F_i(0)\equiv2\pmod4$ and each $F_i$ is Eisenstein at two. Choosing distinct $d_i$ ensures distinct field degrees. For a root $\alpha_i$ of $F_i$, the product $\ell_{i+1}(\alpha_i)/\ell_i(\alpha_i)$ is a square with root $q_i(\alpha_i)/\ell_i(\alpha_i)$. The product of their reductions is $z$, since the $h_i(m)$ each occur twice and their squares cancel the denominator. The gcd is $D_-$.

### Enforcing exact square kernels

Let $c_j$ be the rational zero of $\ell_j$. For each field, give each of its two off-edge columns a separate auxiliary prime $p$ at which $\ell_i(c_j)\ell_{i+1}(c_j)$ is a nonzero square. The following explicit data give $(j,p,t)$ with $t^2\equiv\ell_i(c_j)\ell_{i+1}(c_j)\pmod p$.

| Field $i$ | First off-edge column | Second off-edge column |
| ---: | --- | --- |
| 1 | $(3,37,1)$ | $(4,19,6)$ |
| 2 | $(1,11,1)$ | $(4,23,9)$ |
| 3 | $(1,29,14)$ | $(2,43,6)$ |
| 4 | $(2,41,17)$ | $(3,59,8)$ |

Each prime avoids the mark denominators and the differences between the four cuts and $3$. Require $v$ divisible by all eight primes. At the prime for column $j$, impose the following values of $q_i$ at the cuts modulo $p^2$.

- At $c_j$, use whichever of $t$ and $t+p$ makes $q_i(c_j)^2-\ell_i(c_j)\ell_{i+1}(c_j)$ have valuation one. At most one lift has its square exactly equal to the product modulo $p^2$.
- At the two edge cuts use one. Their products vanish.
- At the other off-edge cut use zero. Its product is nonzero modulo $p$.

The norm of $\ell_j(\alpha_i)=a_j-b_j\alpha_i$ is $b_j^{2d_i}F_i(c_j)$, and $p\nmid b_j$. The conditions isolate valuation one for the appointed off-edge column and valuation zero for all others. Any field-square word therefore has even exponents at both off-edge columns. Also $F_i(3)<0$ because both edge marks are negative there. Monicity gives a real root greater than $3$, where both edge marks are negative. The real signature at that embedding forces their remaining parities to be equal. The edge square identity then proves that the exact square kernel is the single adjacent-column line. The four lines are distinct and any two intersect trivially, while their generators sum to zero.

### Satisfying the construction constraints

Write $q_i=(X-3)H_i$ with $H_i$ monic of degree $d_i-1$. Take $H_i\equiv1+X+\cdots+X^{d_i-1}\pmod2$. At each of the two auxiliary primes in field $i$, prescribe the four values of $H_i$ by dividing the assigned values of $q_i$ by $c_j-3$. The cuts are distinct modulo $p$, so their pairwise differences are units modulo $p^2$. Interpolate a polynomial of degree at most three for the required values after subtracting $X^{d_i-1}$. Coefficientwise CRT with the parity condition gives an initial $H_i$ of the correct degree with bounded nonleading coefficients, modulo the fixed modulus $M_i=2\prod p^2$ for that field.

We have $\gcd(M_i(m-3),N)=1$, since the auxiliary primes divide $v$ and any divisor of $m-3$ and $N$ divides $10$. Adjust $H_i$ by $M_i$ times a radix-$m$ polynomial of degree at most two so that $q_i(m)$ has its prescribed value. Every residue has a representative in $[0,m^2]$ and this adjustment preserves the other conditions. To force $F_i'(m)\equiv1\pmod N$, further adjust $H_i$ by $M_i(X^2+1)S(X)$. This changes the derivative modulo $N$ by $4m(m-3)M_i q_i(m)S(m)$ with a unit multiplier. Every residue is represented by a linear radix-$m$ polynomial, using $-1$ for the representative $m^2$ if needed. Thus $S$ can be chosen linear and all corrections are below the leading degree. The coefficients of $H_i$ have height $O(m)$ and those of $F_i$ have height $O(d_i m^2)$ with fixed constants. The construction takes polynomial bit work in the degree and $\log N$.

## Linear algebra from partial local identities

The mixed sign test can take partial multiplicative certificates from each field as its input. At vertex $i$ suppose the certified identities have exponent matrices $A_i,B_i$ such that
\[
 u_i^{A_{ij}}=\ell(\alpha_i)^{B_{ij}}
\]
for each supplied column $j$. Here $u_i$ is a list of field elements with unit reductions, and the rows of $B_i$ correspond to the common marks. Let $s$ be the vector of common mark residues. Solve the one binary system with the block diagonal rows $A_i$ and the shared rows $(B_1\ \cdots\ B_r)$. For a binary solution $c=(c_1,\ldots,c_r)$, the certified square roots are $u_i^{A_i c_i/2}$, and the normalized modular ratio is
\[
 Z(c)=\frac{\prod_i \rho_i(u_i)^{A_i c_i/2}}{s^{(\sum_i B_i c_i)/2}} .
\]
The denominator corresponds to subtracting the full even excess mark exponents at one vertex. The resulting total exponent vector is zero, so $Z(c)^2=1$. Changing any integer relation coefficient by twice an integer changes the numerator and denominator by the same factor, by reduction of the supplied identities. Thus basis values generate the whole mixed sign image of these certified relations. A proper gcd follows from any basis value outside the two global signs.

For the four-field construction, take one identity per vertex with $u_i=q_i(\alpha_i)/\ell_i(\alpha_i)$, $A_i=[2]$ and $B_i=e_{i+1}-e_i$. The binary kernel is generated by $(1,1,1,1)$. The denominator is one and the ratio is $z$. Neither the elimination nor the verification needs a factorization as input.

The [PARI/GP replay](../experiments/cogentic-primitive-mixed-fields.gp) verifies the Eisenstein conditions, all isolated valuation data, the simple modular branches, the real signature condition and the mixed gcd for three degree ranges on a 199-bit member. Run `gp -fq < experiments/cogentic-primitive-mixed-fields.gp` from the repository root. The family uses the identity $N=4v^4+1$ to obtain its prescribed mixed branch, and its choice $m\asymp N^{1/2}$ differs from the scheduled growing-degree common argument.
