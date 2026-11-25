# Locating the exceptional Hasse intervals

By the verified ordinary RH the exceptional primes for the [many-prime Hasse estimate](mean-time-elliptic-factoring.md) in \((P,2P]\) lie in \(\exp(O(\sqrt{\log P\log\log P}))\) intervals of length \(O(\sqrt P)\). The existence proof and the cost of evaluating a single Fourier coefficient leave open how to compute their locations. A finite-dimensional obstruction describes what additional information a deterministic algorithm would need.

## Fixed bins and computable coefficients

Use order-coordinate bins of width \(\lfloor\sqrt P/4\rfloor\). For any \(p+1\) in a bin, every center in that bin, with a short window of radius \(\sqrt P/8\), has its window inside \(|n-(p+1)|\le\sqrt p\). Thus a bad prime requires the entire bin to have short counts below the required threshold. The kernel windows in the many-prime estimate obey the same containment. Every interior bin has logarithmic measure \(\gg P^{-1/2}\). The total exceptional logarithmic measure is \(P^{-1/2}\exp(O(\sqrt{\log P\log\log P}))\), which gives the stated bin count after two boundary bins are included. The same argument works with the exceptional measure from the [classical zero-density estimate](zero-density-hasse-intervals.md).

The cofactor Dirichlet polynomial is accessible at a chosen frequency. The cofactors are all products of exactly \(k\) distinct primes from a short fixed prime range. At frequency \(t\) the transform \(D(t)\) is the coefficient of \(X^k\) in

\[
 \prod_{r\ \mathrm{in\ the\ cofactor\ range}}
                 (1+Xr^{-1-it}).
\]

One can compute this coefficient by updating the coefficients of degrees \(k,k-1,\ldots,1\) for each prime. There are at most \(Y\) primes, so this takes \(O(kY)\) arithmetic operations. The same scalar prime transform is reused in all of the repeated prime slots. Standard fixed-precision approximations suffice at prescribed polynomially many bits: all intermediate absolute coefficient sums are bounded by \(\exp(\sum 1/r)\) on this prime interval. Computing Fourier coefficients of the squared *physical-space* error would instead require a convolution of pairs of frequencies.

## A deterministic Fourier-query obstruction

On a cyclic grid with \(n\) coordinates, suppose an algorithm queries individual Fourier coefficients of an unknown nonnegative signal. Even if the signal differs from one by squared Euclidean norm at most two, deterministic sublinear sampling cannot guarantee a short list containing every zero. This statement concerns that general query model.

Run the deterministic algorithm on the constant signal one. Let \(\Omega\) include its queried frequencies and their conjugates, and let \(m=|\Omega|<n/2\). If any coordinate \(j\) is omitted from the returned list, let \(P_\Omega\) be the orthogonal projection onto those Fourier modes. Define

\[
 f=\mathbf 1-\frac{(I-P_\Omega)e_j}{1-m/n}.
\]

All its queried Fourier responses agree exactly with those of one, including along the entire adaptive transcript. The projection matrix is real by conjugate symmetry, has diagonal \(m/n\), and has off-diagonal entries bounded in absolute value by \(m/n\). Consequently \(f_j=0\), every other value is at least \((n-2m)/(n-m)>0\), and

\[
 \|f-\mathbf1\|_2^2=\frac{1}{1-m/n}\le2.
\]

So positivity, a small mean-square error, and cheap access to individual Fourier coefficients do not alone turn the bin-count estimate into a deterministic recovery algorithm. An arithmetic recovery argument could exploit the extra structure of the smooth-product measure, or a different query that measures errors over selected sets of bins.

The exact replay checks 70,065 prime instances and 732,000 short centers at three finite dyadic scales, 40 elementary-symmetric evaluations over finite fields, and 672 exact rational projection examples. It tests the stated identities, without approximating the analytic exceptional count. [Finite replay](../experiments/hasse-exception-clusters.py)
