# A Gaussian width bound for thin terminal slope strips

Consider a homogeneous binary polynomial
$$
P(X,Y)=\sum_{j=0}^D c_jX^jY^{D-j},\qquad D\ge2.
$$
Use a discrete Gaussian on its coefficient lattice with arbitrary positive definite ambient covariance parameter $\Sigma$. In the convention here its weights are proportional to $\exp(-c^{\mathsf T}\Sigma^{-1}c/2)$. Assume $\sqrt{\Sigma_{jj}}\le S K^j$, with $K\ge1$. These bounds concern the continuous Gaussian parameters used in Poisson summation. The discrete coordinate variances alone do not imply them.

Let $(a_i,b_i)$ for $i=1,2$ be two primitive positive marks with distinct slopes, $b_i\asymp V$, and mutually comparable $a_i/b_i$. If the Gaussian mass on the two-value evaluation kernel has relative error at most $\varepsilon<1$ uniformly over all real shifts in the kernel, then
$$
S\gg \frac{V^2}{D^2K^2}\sqrt{\log(1/\varepsilon)} .
$$
The implicit constant depends only on the fixed comparability constants. In particular a terminal strip on slope scale $K^{-1}$ with $\log K=O(H)$ does not allow a fixed saving on the $DH$ height scale through this smoothing argument. [Earlier shifted-kernel bound for ordinary boxes](keybreak-skewed-top-box.md#the-coefficient-law)

## A short dual functional in either slope range

Write $r_i=a_i/b_i$ and let $L$ be the integral evaluation kernel. Gauss's lemma, using primitive marks and distinct slopes, gives precisely the polynomials
$$
P=(b_1X-a_1Y)(b_2X-a_2Y)Q,\qquad Q\in\mathbb Z[X,Y]_{D-2}.
$$
In particular, the coefficient $q_0$ of $Y^{D-2}$ in $Q$ is an integral functional on $L$ and assumes value one there, by taking $Q=Y^{D-2}$.

If $\max_i r_i>1/K$, comparability gives $a_i\gg V/K$ at both marks. In this case use the ambient extension $q_0=c_0/(a_1a_2)$, with $\Sigma$-standard deviation at most $O(SK^2/V^2)$.

If both $r_i\le1/K$, write $Q=\sum_j q_j X^jY^{D-2-j}$ and set $q_j=0$ for $j>D-2$. The high-end identity is
$$
\frac{c_{l+2}}{b_1b_2}=q_l-(r_1+r_2)q_{l+1}+r_1r_2q_{l+2},\qquad 0\le l\le D-2.
$$
Its inverse, terminated at the top degree, gives the ambient linear functional
$$
q_0=\frac1{b_1b_2}\sum_{l=0}^{D-2} h_l(r_1,r_2)c_{l+2},
\qquad
h_l(r_1,r_2)=\sum_{j=0}^l r_1^j r_2^{l-j}.
$$
Indeed the $h_l$ are the coefficients of $1/((1-r_1z)(1-r_2z))$, or the formula follows by telescoping the displayed triangular recurrence. As $|h_l|\le(l+1)K^{-l}$, the covariance norm triangle inequality, valid also with correlated coefficients, gives
$$
\sqrt{\operatorname{Var}_\Sigma(q_0)}
 \le\frac1{|b_1b_2|}\sum_{l=0}^{D-2}
         (l+1)K^{-l}\sqrt{\Sigma_{l+2,l+2}}
 \ll \frac{D^2SK^2}{V^2}.
$$
This uses a functional with integer values even though its ambient extension uses rational coefficients. If both numerators also satisfy $a_i\asymp U$ with $U\ge V$, the first formula gives the stronger $S\gg U^2\sqrt{\log(1/\varepsilon)}$. In particular the two slope ranges together yield the stated bound with $V^2$ replaced by $\max(U,V)^2$ when both coordinate scales are available.

## The fiber variance and its Fourier coefficient

Put $W_0=L\otimes\mathbb R$. The metric on a Gaussian fiber is the restriction of the ambient precision $\Sigma^{-1}$ to $W_0$. Thus the squared dual norm of the restriction of an ambient functional $u$ is
$$
\|u|_{W_0}\|_*^2
=\sup_{x\in W_0\setminus\{0\}}\frac{|u(x)|^2}{x^{\mathsf T}\Sigma^{-1}x}
\le u^{\mathsf T}\Sigma u .
$$
Equivalently the covariance on the fiber of an evaluation map $E$ is $\Sigma-\Sigma E^{\mathsf T}(E\Sigma E^{\mathsf T})^{-1}E\Sigma$ on the coefficient space. In particular the fiber bound follows from the ambient variance even for highly correlated coefficients.

The shifted lattice mass divided by its torus mean has Fourier coefficient $\exp(-2\pi^2\|u|_{W_0}\|_*^2)$ at each dual functional. This follows by integrating the periodized Gaussian over a fundamental domain and applying the Fourier transform of a Gaussian on $W_0$. Uniform relative error at most $\varepsilon$ bounds the absolute value of each nonzero Fourier coefficient by $\varepsilon$, since the constant term integrates to zero against that character. Substituting $q_0$ proves the necessary bound. Relative error for every shift on a full-rank sublattice of $L$ has the same obstruction, since the restriction of $q_0$ is still nonzero and integral.

## Converting terminal evaluation widths to coefficient widths

Suppose instead that the continuous standard deviation of $P(s,1)$ is at most $W$ for every $s$ in $[\alpha/K,\beta/K]$, with fixed $0<\alpha<\beta$. Apply interpolation to $P(x/K,1)$ on $D+1$ equally spaced points in $[\alpha,\beta]$. Each coefficient of this polynomial is a linear combination of its sampled values whose total absolute weight is bounded by $(C D)^D$ for a constant $C$ depending only on the fixed interval. Indeed the $\ell^1$ coefficient size of a Lagrange numerator is at most $(1+\beta)^D$, and each of its $D$ denominator factors has magnitude at least $(\beta-\alpha)/D$. The covariance norm triangle inequality then gives $\sqrt{\Sigma_{jj}}\le(CD)^D WK^j$. Therefore
$$
\log W\ge 2\log V-2\log K-O(D\log D)
$$
for fixed $\varepsilon$. In the KeyBreak scales $\log K=O(H)$ and $D\log D=o(DH)$, so only a lower-order reduction is possible under these hypotheses. This conclusion requires control of every kernel shift and, in the interpolation consequence, a terminal slope interval of the stated width. It gives no lower bound for a method that compares distributions only at the actual lattice shifts realized by its evaluations.
