# Certifying monic relation valuations at the mark root

The monic relation collector can keep odd primes dividing the global polynomial discriminants when the mark certifies their individual prime-ideal valuations. The opt-in `mark_local=True` mode tests each factor of a norm at its mark root. The separate `include_ramified_two` switch keeps its existing dyadic rule. The mark grid, smoothness cutoff, residual square test, and large-prime count limits retain their existing settings. [Replay](../experiments/cogentic-monic-local-roots.py)

## The local valuation certificate

For monic irreducible $P$ of degree $e$, let $K=\mathbb Q(\alpha)$ with $P(\alpha)=0$. A primitive mark $(a,b)$ has field element $z=a-b\alpha$ and rational norm $M=P_h(a,b)=b^eP(a/b)$. If $p\mid M$, then $b$ is a unit modulo $p$: otherwise $M\equiv a^e\pmod p$ would be a unit. The image $r=ab^{-1}\bmod p$ is a root of $P\bmod p$. A prime ideal of $\mathcal O_K$ above $p$ divides $(z)$ exactly when its contraction to $\mathbb Z[\alpha]$ is $(p,\alpha-r)$. In one direction $z\equiv0$ forces $\alpha\equiv r$ because $b$ is a unit. In the other, $z$ already lies in that power-order prime. Thus all maximal-order primes over the mark root contribute to the norm valuation

$$v_p(M)=\sum_{\mathfrak p\mid (p,\alpha-r)} f(\mathfrak p/p)\,v_{\mathfrak p}(z).$$

Two conditions individually give a unique prime above the mark root and hence a sound row label consisting of the field, $p$, and $r$.

- If $P'(r)\ne0\pmod p$, Hensel's lemma splits off $X-\widetilde r$ over $\mathbb Z_p$, with the complementary factor prime to it modulo $p$. The decomposition of $\mathbb Q_p[X]/P$ then has one $\mathbb Q_p$ factor at $r$, and the other factors have no integral root reducing to $r$ in their residue fields. The prime there has residue degree and ramification index one. Its valuation of $z$ equals $v_p(M)$, even when the power-order index or the discriminant is divisible by $p$ at another root.
- If $v_p(M)=1$, every term in the displayed sum is a positive integer. There is one term with residue degree and valuation both one, including when $P'(r)=0\pmod p$. This case needs no determination of its ramification index.

An explicitly factored odd $p$ with $P'(r)=0$ and $v_p(M)\ge2$ is unresolved by these tests. The collector rejects the mark if either field has such a factor. A larger valuation at a multiple root can come from several prime ideals or from a residue degree above one, each of which affects ideal parity.

## Unfactored square tails

With trial primes through $Y$, remove all explicit factors. In the complete-parity mode a residual $T>1$ can be omitted from the parity column only when it is a perfect square and

$$\gcd(T,D_h(a,b))=1,\qquad D_h(a,b)=b^{e-1}P'(a/b).$$

For every $p\mid T$, the gcd certifies a simple root because $D_h(a,b)\equiv b^{e-1}P'(r)\pmod p$ and $b$ is a unit. Its unique ideal exponent is $v_p(T)$, which is even. The product of all omitted ideals is therefore a square ideal. A residual which is a nonsquare or shares a factor with $D_h(a,b)$ is rejected. No tail prime has to be identified for this decision. Primes removed explicitly still receive the ordinary valuation test, including any exponent-one multiple roots below the cutoff.

With the scheduled monic bounds, norms and homogenized derivatives have $O(V)$ bits for $|a|,|b|\le\exp(O(W))$. After computing the norm and its bounded factorization, the additional operations are a polynomial number of bit operations in $L=\log N$ for each mark and field. They use exact homogenized derivative evaluation, residues at the listed factors, and one gcd against the tail. Enumerating the whole grid and trial-prime list costs $\exp(O(W))$ when both the grid height and $Y$ are $\exp(O(W))$. The method needs no factorization of $N$ or either discriminant, and no maximal-order computation. The code retains the supplied discriminant product only to preserve the preexisting decision at two when the dyadic row is disabled.

## Exact replay

Run `python3 -B experiments/cogentic-monic-local-roots.py`. The replay compares with the previous odd-discriminant exclusion using the dyadic row in both runs. Every old column must be preserved. It also runs with the dyadic row disabled and checks that the even marks remain excluded. Across raw, repaired, planted, and targeted pairs, PARI independently factors the principal ideals in the maximal orders, verifies the residue roots and exact exponents, constructs parity columns, and computes their nullity. It checks 31,700 field columns at base 151, tail cutoff 8,192 except for one targeted control, and grid height at most 64.

| Input | Pair | Old columns | Old nullity | Local columns | Local nullity |
| ---: | --- | ---: | ---: | ---: | ---: |
| 143 | Raw | 307 | 0 | 920 | 22 |
| 323 | Raw | 916 | 7 | 1,005 | 28 |
| 391 | Raw | 572 | 0 | 1,009 | 49 |
| 17 | Repaired | 728 | 18 | 2,426 | 1,013 |
| 1787 | Repaired | 68 | 0 | 255 | 0 |
| 631 | Planted | 45 | 1 | 105 | 1 |
| 15629 | Planted | 11 | 2 | 16 | 2 |

Three controls isolate the local cases. Use the displayed cubic as $F$, take $m=3$ and $G=F+(X-3)X^3$, and inspect the primitive mark $(0,1)$.

- For $F=X^3-2X^2+(p+1)X+2p^2$ and $p=8209$, both rational norms are $2p^2$. The cubic reduces to $X(X-1)^2$ modulo $p$. It has a simple mark root and a globally bad discriminant at $p$. The second field also has a simple root at the mark. The replay keeps the square tail and records only the known rows at two.
- For $F=X^3+2X^2+2pX+2p^2$ and the same $p$, the rational norms are still $2p^2$ but the mark roots are multiple. In the cubic, $F(pY)/p^2\equiv2(Y^2+Y+1)\pmod p$. Its two distinct nonzero roots lift because $p\equiv1\pmod3$. They give two distinct prime ideals above $p$ with exponent one in the mark, which PARI verifies. The collector rejects this mark both when $p$ is in the tail and when the prime cutoff is increased to include $p$ explicitly.
- For $F=X^3+2X^2+10X+10$, both norms are $10$ and both mark derivatives vanish modulo $5$. The exponent-one rule admits the two odd rows at five alongside the two rows at two.

These tests certify ideal parity for additional marks. Uniform supply of enough such marks, conversion of ideal parity to simultaneous field squares, and separation of modular root signs still require their own bounds.
