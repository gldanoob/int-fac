# Two prescribed unit marks at a common multiple

For every odd $N>1$, two distinct monic Eisenstein fields of degrees six and ten can share an argument modulo $N$ and have two prescribed primitive marks of norm one. Their two-mark word is an exact square in both power orders. The construction takes polynomial bit time. Its two roots have the same residue by default, and a productive variant requires a separating modular square root. [Common-multiple obstructions](cogentic-bounded-degree-multiples.md)

Set $m=2N+3$ and take the primitive marks $(1,1)$ and $(-5,1)$, whose product is $S(X)=(X-1)(X+5)$. Then $S(m)\equiv S(3)=16\bmod N$, $S\equiv(X+1)^2\bmod2$, and $S(0)=-5\equiv3\bmod4$.

For a desired residue $s$ with $s^2\equiv16\bmod N$, take $e=1$ or $3$ and write $J_e(X)=X+X^3+\cdots+X^e$. Select the unique integer $E\in[1,2N]$ congruent to $(s-1)/16\bmod N$ and with the same parity as $J_e(m)$. Define
\[
H(X)=J_e(X)+E-J_e(m),\qquad
P(X)=1+S(X)H(X),\qquad
F(X)=P(X)^2-S(X).
\]
The parity choice gives $H\equiv J_e\bmod2$. Therefore $P\equiv X^{e+2}+X+1\bmod2$ and $F\equiv X^{2e+4}\bmod2$. Also $F(0)\equiv1-3\equiv2\bmod4$. Thus $F$ is monic Eisenstein of degree $2e+4$, and the two choices of $e$ give distinct fields. All coefficients have $O(\log N)$ bits.

At the common argument, $P(m)\equiv s$ and $F(m)\equiv0\bmod N$. The integer $F(m)$ is positive because $H(m)=E\ge1$ and $S(m)>1$. At both marked arguments $a=1,-5$, $P(a)=F(a)=1$. Thus the two mark elements have norm one and are power-order units, and $P(\alpha)^2=S(\alpha)$ is an exact square identity in either field. Both marks reduce to units since their product reduces to 16. The large common argument lies outside the centered square and cube regimes, and the coefficient magnitudes can grow as powers of $N$.

Taking $s=4$ in both fields gives a nonempty square word unconditionally. To split $N$, two prescribed residues $s_1,s_2$ must have ratio different from both global signs. Their ratio is a square root of one, and a nontrivial coprime factorization conversely supplies such a ratio by assigning the two signs by CRT. The construction gives precise control of the field identities and the marked norms while leaving the separating residue as input.

Run `gp -fq experiments/cogentic-prescribed-unit-marks.gp` for the two field degrees, unit norms, and a split with a deliberately supplied CRT sign. [Replay](../experiments/cogentic-prescribed-unit-marks.gp)
