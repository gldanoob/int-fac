# The limiting cost with short modular squares

The infimum of the private and terminal cost inequalities for coordinate widths \(\theta>2/3\) is
\[
 2.07377842496623257501<C_*<2.07377842496623257502.
\]
The single-input algorithm attains \(L_N[1/3,C_*]\) in the leading exponent under Dirichlet GRH and the pinned KeyBreak analytic inputs. This assertion uses a sequence of fixed schedules with widths strictly above \(2/3\). An explicit 4096-stage witness at \(\theta=.666667\) gives \(2.07387\), and a 1536-stage witness at \(.667\) gives \(2.0741\). Lean verifies the infimum of the finite inequalities and Sage checks the limiting parameter identities and strict margins. The analytic factoring theorem remains at manuscript level. [Lean sharp infimum](../formal/cogentic/Cogentic/RandomizedScaledSchedule.lean) · [Sage certificate and finite witness](../experiments/keybreak-lattice-limit.py) · [Full single-input construction](keybreak-uniform-window-integration.md)

Write \(p_\theta(u)=4\theta/(9u^2)+2u/3\). At the limiting width \(\theta_0=2/3\), the active private and terminal inequalities are
\[
 b=C_*-p_{\theta_0}(u),\qquad
 6b(C_*-b)=3u^2/2+4\sqrt{C_*},\qquad
 6(C_*-2b)p'_{\theta_0}(u)=-3u .
\]
The term \(4\sqrt{C_*}\) is the minimum of \(4/\delta+C_*\delta\). Set \(z=u^3\); eliminating \(b,C_*\) and squaring gives a polynomial with the required root in \((.26871505639057413116,.26871505639057413117)\):
\[
332150625z^6-212576400z^5+632375424z^4-235892736z^3-143327232z^2+28311552z+4194304.
\]
The certificate checks the unsquared relations, positivity, the endpoint signs and the full terminal box. Here \(u=.645303469872249\ldots\), \(b=.93203790958477\ldots\), and \(\delta=2/\sqrt{C_*}=1.388829138584636\ldots\). The tangent lower bound for \(p_{\theta_0}\) and the tangent upper bound for \(6b(C_*-b)\) exclude a lower budget; increasing \(\theta\) can only increase the moment requirement. The Lean proof constructs finite grids for every budget strictly above \(C_*\) and widths arbitrarily close to \(2/3\) from above. [Finite private and terminal inequalities](../formal/cogentic/Cogentic/RandomizedScaledSchedule.lean)

For the other costs, fix top and high ratios \(1.70\) and \(1.85\). At the limiting parameters, the algebraic and rational top and high charges, sparse extraction, character costs, and the algebraic part of the low search are all below \(2.07\). Use the positive terminal perturbation from the full-width construction to give the box and bottom mean strict margins. The private end weight tends to \(4\theta_0/(9u^2)-u/3>0\); the single-coordinate factor count relative to \(k_0\) tends to \(2\theta_0p_{\theta_0}(u)/(4\theta_0/(9u^2))<4\). The top parent/child separations, rational error exponent and low fixed-point inequality all have strict room in the exact replay. First choose \(\theta>2/3\) and \(\alpha>1/2\) sufficiently close to their limits, perturb the terminal height and mean, then choose a sufficiently fine fixed positive grid and rational allowances. Continuity preserves all strict margins. The per-width sampler has negligible epoch error for each fixed choice before \(N\) tends to infinity. [Full-width perturbation and grid argument](keybreak-sparse-dependency.md#exact-limiting-coefficient) · [Short-square sampler and endpoint condition](keybreak-linearized-square-sampler.md)

This proves the stated bound with \(C_*+\epsilon\) for every fixed \(\epsilon>0\). To use one algorithm for every \(\epsilon\), enumerate the rational finite schedules and use the charged doubling simulation with fresh randomness and verified integer divisions. A fixed valid schedule with index \(j\) has only a fixed \(2^{O(j)}\) overhead at a given work scale. Once its allocation exceeds four times its expected work, its independent miss probability is at most \(1/4\) per phase and the remaining geometric time sum converges. The verification and primality guards permit unsuccessful schedules in the enumeration. Taking the leading upper limit for each fixed \(j\) gives the coefficient \(C_*\) for the same algorithm. This limit argument with the floor-sum sampler requires only widths above the threshold. Gentry’s exact sampler also supplies an independent fixed window of width at least eight times \(N^{2/3}\). [Charged doubling argument](keybreak-sparse-dependency.md#how-close-the-schedule-is-to-its-cost-floor) · [Lean restart bound](../formal/cogentic/Cogentic/RandomizedRestartBudget.lean)
