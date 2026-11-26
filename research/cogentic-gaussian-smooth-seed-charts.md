# Two independent sign reductions from fixed smooth Gaussian seeds

Three fixed primitive marks in compatible Gaussian charts give two independent modular sign reductions on an infinite, publicly recognizable family. Their norms are $2$, $2\cdot113^2$, and $2$. The projective charts use a single unit denominator and keep the mark height at 97. The first member is $40{,}001=13\cdot17\cdot181$. The construction and recognition require only exact arithmetic on the public integer. [Replay and recognizer](../experiments/cogentic-gaussian-smooth-seed-charts.py) · [Compatible charts](cogentic-compatible-quadratic-charts.md)

## A projective chart from a fixed first mark

Let $P$ be monic irreducible quadratic with root $\alpha$ and $P(m)=N$. Fix a unit mark $z_1=a-b\alpha$ with $b>0$ and $\gcd(b,N)=1$. Write $h=a/b$. For a second chart generator $A+B\alpha$ with integer $A,B$ and $B\ne0$, use the rational function
\[
G(X)=A+BX-\frac{B P(X)}{X-h}.
\]
Its quadratic numerator term cancels. The remaining fractional linear function has nonzero determinant because its numerator takes the value $-BP(h)$ at the pole $h$. It gives the same algebraic generator as the affine chart, and it reduces compatibly since $m-h$ is a modular unit.

For $z_2=c-d(A+B\alpha)$, let $s_1=a-bm$ and $s_2=c-d(A+Bm)$ be the affine labels. The projective label is
\[
s'_2=c-dG(m)=s_2-\frac{bdB N}{s_1}.
\]
Thus $s_1s'_2=s_1s_2-bdB N$. This is the exact evaluation at $m$ of the reduced linear representative of $z_1z_2$. The same fixed first mark supplies the pole for every other chart. When a joined seed product is a field square, a positive rational square test on this reduced evaluation supplies its comparison root. [Projective evaluation labels](cogentic-projective-quadratic-charts.md)

## The seeds and their lifted labels

Take positive integers $t,s$ with $s\ge10$ satisfying
\[
t^2-15s^2=-56,\qquad r=2s^2,\qquad N=r^2+1,\qquad \gcd(t,N)=1.
\]
Use $i^2=-1$ with reduction $i\mapsto r\pmod N$. The three defining polynomials evaluated at the listed integer arguments give exactly $N$. Their derivatives are $2r,2r,-2r$ and are units. All marks are primitive.

| Generator | Polynomial | Integer argument | Mark $(a,b)$ | Element | Norm |
| :--- | :--- | :--- | :--- | :--- | ---: |
| $i$ | $X^2+1$ | $r$ | $(1,1)$ | $z_1=1-i$ | $2$ |
| $1+i$ | $X^2-2X+2$ | $r+1$ | $(-30,97)$ | $z_2=-127-97i$ | $2\cdot113^2$ |
| $2-i$ | $X^2-4X+5$ | $2-r$ | $(1,1)$ | $z_3=-1+i$ | $2$ |

The norms exclude each seed from the individual unsigned field square space. Their products satisfy
\[
z_1z_2=(1+15i)^2,\qquad z_1z_3=(1+i)^2.
\]
The three seed classes therefore agree and are nonzero in $\mathbb Q(i)^\times/\mathbb Q(i)^{\times2}$. Merging the charts gives the two independent even-word masks supported on $(z_1,z_2)$ and $(z_1,z_3)$.

Use pole $h=1$ in the second and third charts. Their natural projective arguments come from
\[
G_2(X)=\frac{-2}{X-1},\qquad G_3(X)=\frac{3X-1}{X-1}.
\]
These send $i$ to $1+i$ and $2-i$ respectively. The common denominator evaluates to $r-1$, coprime to $N$ since $N\equiv2\pmod{r-1}$ and $r$ is even. The determinants are $2,-2$. Keep the first label $L_1=1-r$ and use the projective labels
\[
L_2=-30+\frac{194}{r-1},\qquad L_3=\frac{-2r}{r-1}.
\]
Then $L_1L_2=30r-224=(2t)^2$ and $L_1L_3=2r=(2s)^2$. These show all three labels are units. The two normalized roots of unity are
\[
R_1=\frac{1+15r}{2t}\pmod N,\qquad R_2=\frac{1+r}{2s}\pmod N.
\]

## Independence and infinitude

The Pell equation gives $0<t<4s$. For $s\ge10$, the four differences and sums $1+15r\pm2t$ and $1+r\pm2s$ are positive and less than $N=4s^4+1$. It follows that neither normalized root is a global sign. The cross-products satisfy
\[
0<(1+15r)s-(1+r)t<(1+15r)s+(1+r)t<(19r+5)s<N.
\]
The lower bound follows from $(1+15r)s-(1+r)t>(11r-3)s$. The final inequality follows from $r=2s^2$ and $s\ge10$. Thus $R_1$ and $R_2$ are distinct even up to a global sign. Two distinct nonzero classes in the binary group of square roots of one modulo global sign are independent.

At each odd prime power dividing $N$, a square root of one has exactly one sign. If at most two sign patterns occurred across the prime powers for the pair $(R_1,R_2)$, their classes would have rank at most one modulo global sign. Hence at least three patterns occur. Refine the modulus by the two successive difference gcds to get at least three pairwise coprime proper factors. These blocks can be composite.

There are infinitely many instances. Start at $t+s\sqrt{15}=38+10\sqrt{15}$ and multiply by powers of $4+\sqrt{15}$. Its norm is one and the integer recurrence $(t,s)\mapsto(4t+15s,t+4s)$ is invertible modulo 113. Its orbit returns to the starting residues after 16 steps. For all such returns, $N\equiv-1\pmod{113}$. Indeed $s\equiv10$ and $r\equiv200\pmod{113}$. If a prime divides both $t$ and $N$, then $30r\equiv224$ at that prime and $r^2\equiv-1$, so it divides $30^2+224^2=226^2$. Since $N$ is odd, only 113 is possible. The return progression avoids it. The first three accepted values along the full recurrence are $40{,}001$, $148{,}060{,}225$, and $568{,}503{,}936{,}065$, whose common gcd is one.

To recognize a family member from $N$, use integer square roots to test $N=r^2+1$, $r=2s^2$ and $t^2=15s^2-56$, then test the unit condition. The charts and marks are fixed. Root recovery, inverses and gcd refinement take polynomial bit time. The first instance yields $R_1=18{,}461$ and $R_2=38{,}011$. Their difference gcds with $N$ are 13 and 181, leaving the factor 17. At this instance the three pair products of the original affine labels are all nonsquares over $\mathbb Q$, so the unsigned affine-label control has zero matching kernel.

Run `python experiments/cogentic-gaussian-smooth-seed-charts.py` to verify four constructed instances, including the first Pell return. Pass a single integer to run the recognizer. This replay checks a proved family, with no empirical claim about unselected inputs. [Exact replay](../experiments/cogentic-gaussian-smooth-seed-charts.py)

## What the unit denominator supplies

The projective step makes evaluation commute with one chosen product reduction. It does not force the reduced evaluation to be square. For the Gaussian chart, if $z_1z_2=(A+Bi)^2$ has reduced evaluation $T^2$, then $(A+Br-T)(A+Br+T)=B^2N$. With unit $B,T$, the rational parameter $q=(A+Br-T)/B$ pairs with $N/q$. Choosing a public rational unit $q$ and using its modular inverse makes the minus leg a unit and the plus leg zero modulo $N$, giving a global sign. Productive signs come from the square comparison and the resulting distribution of nonunit prime powers, which the Pell conditions here certify directly. Repeating the same three seeds with the same rational labels enlarges the even-word dimension while leaving the sign image generated by $R_1,R_2$. General supplies of independent comparisons across inputs remain open.
