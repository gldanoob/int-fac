# A separating marking throughout a variable-\(j\) conic family

A winning normalized chart \((0,1,b,-1)\) from the [moving elliptic menu](cogentic-moving-elliptic-separation.md) gives two explicit rational one-parameter extensions. At any pair of odd primes for which the chart supplies the stated labels, at least one extension has a single omitted index among \(0,1,b\) whose stacked Kummer rank is three at every good parameter. The elliptic \(j\)-invariant for that marking varies with the parameter. Thus the choice that witnesses separation need not change as the curves vary.

## A finite condition with one free label

As in the moving menu, write \(L(s)\) for the two Legendre bits of a rational unit, with addition given by XOR. Put
\[
 z=L(-1),\qquad a=L(b),\qquad h=L(b-1).
\]
Use \(a,h\) independent if \(z=0\). Otherwise use \(h=0\) and \(a\notin\{0,z\}\). For the coordinates \((0,1,b,c)\), impose \(L(c)=z\), and write \(u=L(c-1)\) and \(f=L(c-b)\). In the order of the six lower-triangular differences of the original calculation the labels are \((0,a,h,z,u,f)\).

For each permitted \((z,a,h)\), intersect the sets of successful markings among the first three over all four \(u\)'s, keeping \(f\) fixed. The intersection is nonempty for every \(f\) if \(z=0\). If \(z\ne0\), it is nonempty exactly when \(f\ne a\mathbin{\oplus}z\). The same finite calculation shows that for any one choice of \(u,f\) there is already a successful marking among the first three. To verify both statements, reuse the Kummer matrices from the moving menu for all \(12\cdot4^2=192\) configurations and test the ranks of the three \(4\)-row stacks. [Exact check](../experiments/cogentic-moving-elliptic-conic.py)

## Two conics and good parameters

For a seed \(t_0\) equal to \(1\) or \(b\), let \(w=t_0^2+b\) and use
\[
    t^2+b=w s^2,\qquad c=-t^2.
\]
The point \((t_0,1)\) lies on the conic. Intersect it with \(s=1+H(t-t_0)\) and use the second intersection, giving
\[
         t(H)=t_0+\frac{2(wH-t_0)}{1-wH^2}.
\]
If \(b,b-1,b+1\) are units at both primes, so is \(w\) for either seed. At a good parameter all four coordinates are distinct in both reductions, and then \(L(c)=z\) and \(f=L(-w)\). The two seeds give respectively
\[
          f_1=z\mathbin{\oplus}L(b+1),\qquad
          f_b=z\mathbin{\oplus}a\mathbin{\oplus}L(b+1).
\]
They are distinct since \(a\ne0\). Thus at least one seed gives the fixed-marking condition. The seed is used on the conic, so it need not itself give distinct elliptic marks. The public menu can simply include both seeds and all three markings.

At any odd prime where \(b,b-1,b+1\) are units, the numerator and denominator of \(t(H)\) have no common zero. Indeed \(wH^2=1\) and \(wH=t_0\) together force \(b=0\). As \(t_0\) is also a unit, \(t(H)\) has degree two there. Its denominator excludes at most two finite parameters, and \(t(H)=0\), \(t(H)^2=-1\), or \(t(H)^2=-b\) exclude at most \(2+4+4\) more. Thus each prime excludes at most twelve finite parameters per seed. For each marking under consideration the two fixed unomitted coordinates \(e_1,e_2\) give
\[
 \lambda(H)=\frac{-t(H)^2-e_1}{e_2-e_1},\qquad
 j(H)=256\frac{(1-\lambda(H)+\lambda(H)^2)^3}{\lambda(H)^2(1-\lambda(H))^2}.
\]
The scale \(D_m\) in the moving menu does not affect this invariant. The map \(\lambda(H)\) has degree four, so \(j(H)\) has degree \(24\), also in the indicated odd characteristics. Every fixed good \(j\) therefore has at most \(24\) finite parameter preimages. In particular the separating marking is nonisotrivial. The three varying markings are generically pairwise nonisogenous in characteristic zero. At \(c\) equal to one of \(0,1,b\), the marking omitting that fixed coordinate has finite \(j\), while the other two have a pole. Pull back such a place through the nonconstant parameter map. Potential good reduction is equivalent to integral \(j\) and is invariant under isogeny. [Silverman, *The Arithmetic of Elliptic Curves*, VII.7](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf)

## Distinct local invariants and orders

For a winning base entry the factors \(b,b-1,b+1\) and the denominator of \(b\) are units after the original gcd guards, or a proper factor has already been found. Enumerate \(U\) consecutive integer parameters, with \(U<\min(p,q)\). Check the parameter denominators and six coordinate differences individually by gcd before clearing denominators. A proper gcd gives a factor. A full gcd rejects the entry. Even if other primes divide \(N\), a rejected parameter for a particular seed must be one of the at most twelve exceptional residues at \(p\). Hence for a pair that reaches the separating seed, the menu contains at least \((U-12)/24\) distinct local \(j\)-invariants from separating entries at each of \(p,q\), or it returns a divisor. Clearing denominators multiplies all coordinates by a common unit. The resulting changes of the Weierstrass coordinates are fourth and sixth powers as in the original menu. The parameters have polynomial bit length in \(\log N+\log(2U)\); enumerating the extended menu costs \(U\operatorname{poly}(\log N+\log(2U))\). The condition on \(U\) can be enforced by trial division up to \(U\).

There is also an order-diversity statement for the entire local parameter range. Fix a good parameter residue at \(q\). As the parameter ranges over its good residues at \(p\), CRT realizes these reductions together using integers. The one separating marking gives at least \((p-12)/24\) local \(j\)-invariants at \(p\). For \(p>3\), the weighted number of curves in any one trace class is \(O(\sqrt p\log p(\log\log p)^2)\). Automorphism groups over \(\mathbb F_p\) have bounded size, so the same bound applies to distinct \(j\)-invariants of that trace. Therefore the complete range gives
\[
   \gg \frac{\sqrt p}{\log p(\log\log p)^2}
\]
distinct group orders on separating entries at \(p\). This uses a complete local parameter range, and the trace bound gives no useful multiplicity saving for a short interval of \(\exp(O((\log N)^{1/3}(\log\log N)^{2/3}))\) parameters on balanced inputs. Neither diversity statement guarantees a smooth order or a small odd residual order. [Lenstra, *Factoring integers with elliptic curves*, Proposition 1.9(a)](https://cr.yp.to/bib/1987/lenstra-fiec.pdf)

The [exact replay](../experiments/cogentic-moving-elliptic-conic.py) checks all 192 label configurations and every pair of good local conic parameters on five finite prime pairs. Two fixtures have the second seed singular as an elliptic chart at one prime, and the conic parametrization still supplies good separating entries. The original \(b=52/49\) norm lift gives six and eight distinct separating \(j\)-invariants at \(53,73\), respectively.
