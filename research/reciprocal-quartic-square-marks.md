# When the three reciprocal quartic marks supply a square

Fix an integer $n\ge3$ with $n\equiv2\pmod3$. The [quartic tower construction](cogentic-private-mark-tower-scarcity.md#high-height-quartics-with-unit-or-square-norms) gives
$$
 F_n(X)=X^4+2nX^3-(5n+4)X^2+2nX+1.
$$
In $K=\mathbf Q(\theta)$ for a root of $F_n$, take the units $u=-\theta$, $v=2-\theta$, $w=1-2\theta$. There exists a nonempty subset of these units whose product is a square **if and only if** $n+2$ is an integer square. Whenever $n+2=a^2$, the product of all three units has square root $(\theta-1)^2/a$.

## Proof

Put $t=\theta+\theta^{-1}$ and $E=\mathbf Q(t)$. Then $t=-n\pm\sqrt{(n+2)(n+3)}$ and $K=E(\sqrt{t^2-4})$. The quartic is irreducible modulo three. The larger value of $t$ lies strictly between $2$ and $5/2$, so the two corresponding roots $\theta$ are positive and lie in $(1/2,2)$. The other two roots are negative. For a square $u^i v^j w^k$, the signs at the positive roots require $i=k$ modulo two. All three units are positive at the negative roots, so admitting a global minus sign adds no squares.

The relative norms of $u,v,w$ are respectively $1,\eta,\eta$, where $\eta=5-2t$. The identity $(t-2)^2=(n+2)\eta$ shows that $\eta$ has the same square class in $E$ and $K$ as the rational number $n+2$. In $E$, a square root of $n+2$ exists exactly when $n+2$ or $n+3$ is a rational square. This follows by squaring $b+c\sqrt{(n+2)(n+3)}$ with rational $b,c$. The second possibility is excluded modulo three.

The only quadratic subfield of $K$ is $E$. A second such field would make $K$ biquadratic and give $K=E(\sqrt h)$ with $h\in\mathbf Q$. Then $t^2-4$ would equal $h$ times a square in $E$, and its rational norm would be square. That norm is $(n+2)(9n+2)$, strictly between $(3n+3)^2$ and $(3n+4)^2$. Hence $n+2$ retains its nonsquare class in $K$ whenever it is nonsquare in $E$.

In that case the relative norm test forces $j=k$. Together with the signs this leaves just the triple among nonempty masks. Its value is $uvw=\theta^2\eta$, also nonsquare. When $n+2=a^2$, the identities above and $\theta(t-2)=(\theta-1)^2$ give the stated square root.

## What a lift supplies for one integer

Let $N>1$ be odd and coprime to $15$, and choose $n\ge\max(3,N)$ with $n\equiv2\pmod3$ and $F_n(3)=46+15n\equiv0\pmod N$. A usable lift with any nonempty square mask on these three marks exists exactly when $-15$ has a square root modulo $N$. The conversion is effective in both directions.

* Given such a lift, compute $a=\sqrt{n+2}$ over the integers. Since $a^2\equiv-16/15\pmod N$, $a$ is a unit. The triple root evaluates to $4/a$, whose square is $-15\pmod N$.
* Given $r^2\equiv-15\pmod N$, choose $a\equiv4/r\pmod N$, $a\equiv1\pmod3$ sufficiently large and set $n=a^2-2$. This gives an admissible lift, its triple root evaluates to $r$, and $F'_n(3)\equiv64/15$ is a unit. A lift with polynomial bit length suffices.

If any prime divisor of $N$ sees $-15$ as a quadratic nonresidue, every admissible lift has trivial square kernel on these marks. When two given roots differ by more than a global sign, their difference gives a proper gcd with odd $N$. On $323$, the roots $40$ and $74$ give lifts $n=9407$ and $206114$, and $\gcd(74-40,323)=17$. This is a check of the conversion with supplied roots. Its cost does not pay for discovering either root.

## Varying the modular evaluation

Put $\Delta=m(2m-1)(m-2)$. When $F_n(m)=0\pmod N$ and $\Delta$ is invertible,
$$
 n+2\equiv-(m-1)^4/\Delta,\qquad n+3\equiv-(m^2-3m+1)^2/\Delta\pmod N.
$$
For the exceptional lift $n=a^2-2$ with $a$ a unit, the triple therefore supplies $y=(m-1)^2/a$ with $y^2=-\Delta$. The change $X=-2m$, $Y=2y$ yields $Y^2=X(X+1)(X+4)$. The [exact Sage replay](../experiments/reciprocal-quartic-square-marks.py) computes rank zero with proof enabled. The rational points are infinity, the three points with $Y=0$, and $(-2,\pm2),(2,\pm6)$. The last four give $m=\pm1$. In either case $F'_n(m)=2m F_n(m)$, so these rational points give a repeated modular evaluation whenever they give a modular root. This rules out obtaining a simple evaluation by reduction of a rational point on this particular fixed curve. Searching directly for modular points remains a different problem.
