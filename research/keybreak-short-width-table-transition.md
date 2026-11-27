# A transition cost for asymmetric tables at width two thirds

A single shared terminal table can pass its intended inequalities below the symmetric short-width coefficient. An intermediate sequence of full tables does not complete that schedule if large incoming tags must reach the terminal cutoff and every crossing is charged at the full request population. The reason is that a transition across the rational cutoff restores the original symmetric terminal inequality, regardless of the chosen outgoing cutoff or the number of intermediate levels. This is a cost-model obstruction. [Shared table ledger](keybreak-shared-terminal-prebuild.md) · [Sharp symmetric short-width ledger](keybreak-lattice-limit.md)

## Checking a crossing edge

Use work exponents in units of $H=(\log N)^{1/3}(\log\log N)^{2/3}$. Write $r>0$ for the global rational cutoff, $\delta>0$ for the field degree coefficient, and $A$ for the leading algebraic height outside the search box. Let a level with box scale $v>0$ take an incoming algebraic tag of exponent $y$ and aim for factors of exponent at most $y'>0$. For an incoming tag in its prescribed field, the modeled search mean has exponent $2v-y-s_R-s_A$. Under the ordinary rational height and local rational cutoff at most $r$, the rational loss is at least $R=1/(3\delta r)$, even if the test is shared. The algebraic loss is at least $(A+\delta v)/(3y')$. These are the ordinary height and tag-lattice assumptions of the shared terminal ledger. Write $\ell=s_R+s_A$.

For an edge with $y\ge r$ and $y'\le r$, the nonnegative mean requirement and the two loss bounds imply
$$
2v\ge r+\ell,\qquad \ell\ge R+\frac{A+\delta v}{3r}.
$$
Thus $\Delta=1-\delta/(6r)>0$. In the full table mode $2v\le C$, and therefore
$$
\Delta C\ge \Delta(2v)\ge r+R+\frac A{3r}.
$$
In the per-request mode suppose that the population and per-request search together are charged at least $r+\ell$. The budget gives $\ell\le C-r$, while $v\ge(r+\ell)/2$. Hence
$$
\Delta(C-r)\ \ge\ \Delta\ell\ \ge\ R+\frac A{3r}+\frac\delta6.
$$
This is the same necessary constraint $\Delta C\ge r+R+A/(3r)$. Both arguments grant free lookup and extra slack for any other charges. They allow $v$ and $y'$ to vary arbitrarily by level.

With the physical height $A\ge 1/\delta+3u^2/4$, multiplying by $6r$ yields the old symmetric terminal condition
$$
6r(C-r)\ge \frac32u^2+\frac4\delta+C\delta .
$$
At width $2/3$ the full private charge $C\ge r+8/(27u^2)+2u/3$ then gives the same floor $C_*=2.07377842496623\ldots$ as the symmetric model, using its supporting inequality. A smaller $C$ can be moved up to $C_*$ in the terminal inequality since $6r-\delta>0$, giving strict private slack there and the existing contradiction. [Physical height and scaling](keybreak-lattice-limit.md) · [Formal cost floor](../formal/cogentic/Cogentic/RandomizedScaledSchedule.lean)

Any finite chain beginning above $r$ and ending at or below an algebraic cutoff $a<r$ contains a crossing edge. This holds even for nonmonotone intermediate cutoffs or a single jump over a range of exponents. If every crossing must use one of the two charged modes above, adding more full intermediate tables cannot remove the floor.

## The terminal-only witness

Take
$$
(C,u,r,a,\delta,v,y)=(2.073,.6625,.9562,.9094,1.372,1.0364,.9095).
$$
With $A=1/\delta+3u^2/4$, the private charge is less than $2.072946$, the table charge is $2.0728$, and the solve charge $2\max(r,a)$ is $1.9124$. The terminal mean surplus $2v-y-R-(A+\delta v)/(3a)$ exceeds $.0001986$. These statements follow by rational arithmetic. The crossing cost for these same parameters, however, is at least
$$
\frac{r+R+A/(3r)}{1-\delta/(6r)}
=\frac{621496923029}{299452720000}
>2.07544 .
$$

A narrow gap between table and request regimes is visible with the same numbers. A decreasing table edge at parent $y$ must satisfy $y(C-R-y)\ge(A+\delta C/2)/3$. Its upper root is less than $.92966$, already below $r$. The estimate is only illustrative. The crossing inequality rules out jumping directly past the gap under the stated charge assumptions.

## Request counts and scope

The original search ledger charges every active level against a full relation population. A per-request crossing step justifies the charge used above if that step handles $\exp((r+o(1))H)$ separately searched requests. With a bounded number of levels or types, the same conclusion follows if that many separate searches are required across all crossing types, since one type then has that leading exponent. Counting retained rows alone does not prove this if earlier levels can already supply smaller children, or if distinct rows reuse a much smaller number of searched tags. The full table charge still applies to any chosen level whose physical box is swept in full, even if its table serves other levels.

More generally, if the exponent of separately searched requests is only $f<r$, the per-request inequality becomes $C\ge f+\ell$. The argument then gives
$$
C\ \ge\ f+\frac{R+A/(3r)+\delta/6}{1-\delta/(6r)} .
$$
For the witness, this allows a per-request crossing at $C=2.073$ only if $f<.95376$. Obtaining an appropriate crossing count and sufficient supply of completed rows under that smaller exponent would require an additional argument. An algorithm that collects rational candidates without sweeping their full box, changes the rational height, or only needs a smaller quotient of the final rank also uses a different ledger.
