# Higher-degree terminal marks in the charged KeyBreak model

In the standard rectangular smoothness ledger, primitive terminal marks of any fixed degree (kge2) cannot lower the linear limit (C_*approx2.1546302153). Even granting optimistic proposal supply and free polynomial-time access to all necessary ideal labels, the degree-(k) ledger excludes (Cle2.177). This comparison keeps the existing private field construction and charges all terminal requests to one input. [Linear limit and private constraints](keybreak-sparse-dependency.md#exact-limiting-coefficient) · [Asymmetric linear ledger](keybreak-asymmetric-terminal-budget.md)

## Norm and proposal scales

Put (D=(log N/loglog N)^{1/3}) and (H=Dloglog N). Use a field polynomial (F) of degree (dsimdelta D) with coefficient height (exp((A+o(1))DH)). The private construction charges (Age1/delta+3u^2/4), where its work cost is at least (b+p(u)), (p(u)=4/(9u^2)+2u/3), and (b) is the larger terminal factor-base exponent in (H) units. These are the same private constraints for every proposed terminal degree.

Write the radix as (m=r_0/Q), with (log Q=o(DH)) and (log |m|sim DH/delta). Let (P(X)=sum_{i=0}^k c_iX^i) be primitive of exact degree (k), with (|c_i|le W=exp((v+o(1))H)). The integral rational value is (G_k(P)=Q^kP(r_0/Q)). At a degree-one label ((q,s_0)) with (q
mid Q), the algebraic proposal condition is (P(s_0)=0mod q). On the rational side the corresponding condition is (P(r_0/Q)=0mod q). Testing exact valuation one or avoiding bad primes only restricts the proposal set. When the field evaluation is defined, the ordinary identity is (1=(Q^k/G_k(P))psi(P(	heta))mod N), subject to unit checks.

For fixed (k), the rational value has logarithmic height at most ((k/delta+o(1))DH), with this leading height uniformly for nonzero leading coefficient since (Wll |m|). The resultant satisfies
[
|operatorname{Res}(F,P)|le M(F)^k M(P)^d
 le exp((kA+delta v+o(1))DH),
]
where (M) is Mahler measure and each measure is at most the Euclidean coefficient norm. The resultant estimate is an upper bound. Using its height exponent to price smoothness is a hypothesis of the box ledger. Special families with smaller resultant, or conditional smoothness better than the ordinary Dickman prediction, require a different analysis. Removing one prescribed prime of logarithm (O(H)) changes neither height coefficient.

The full coefficient box has at most ((2W+1)^{k+1}) marks, regardless of primitive or irreducible restrictions. The raw volume exponent ((k+1)v) is attainable before the root condition, even restricting to primitive vectors: one can take (c_0,c_1in[1,W]) coprime, then choose the remaining coefficients independently with (c_k
eq0) (for (k=1), the first pair already suffices). Averaged over all residues (s_0mod q), the number of primitive proposals is at most (k(2W+1)^{k+1}/q): a primitive (P) has nonzero reduction and at most (k) roots. This average gives no pointwise bound or lower supply for particular field roots. For example (s_0=0) can give a larger slice when (q>2W). In the following comparison we grant the standard index-(q) volume and smoothness model, including the possibility of efficient generation of those proposals. Unequal coefficient widths only decrease the box volume at a given maximum width in this ledger.

## Elimination including asymmetric cutoffs

Let (a,r>0) be the algebraic and rational cutoff exponents, (b=max(a,r)), (y) be the incoming prime exponent, and (s) the aggregate reciprocal smoothness exponent. The optimistic constraints are
[
sge rac{k}{3delta r}+rac{kA+delta v}{3a},qquad
(k+1)vge y+s,qquad Cge b+s,qquad Cge b+p(u).
]
Removing strict mean slack only weakens the constraints. Put (lambda=delta/(k+1)). The first two inequalities give
[
sge rac{kA+ka/(delta r)+lambda y}{3a-lambda},
]
with positive denominator necessary for feasibility. If (yge b), enlarge both cutoffs to (b) and decrease (y) to (b). If the incoming label is algebraic and (a<b=r), put (y=a). The right side becomes ([kA+a(k/(delta b)+lambda)]/(3a-lambda)), which decreases with (a), so setting (a=b) again weakens the bound. In either case one obtains
[
 6b(C-b)ge rac{3k}{2}u^2+rac{2(k+1)}{delta}
                  +rac{2delta C}{k+1}
 ge rac{3k}{2}u^2+4sqrt C. 	ag{1}
]
For a rational incoming label with (r=tb<b=a), put (y=r). The two (delta)-dependent terms in the middle expression of (1) instead become
[
rac{2(1+k/t)}{delta}+rac{2delta(C-b+bt)}{k+1}.
]
For the budgets considered here (C>2b), since the private charge has (p(u)ge (4/3)^{1/3}>1.1) and (Cle2.177). The identity
[
(1+k/t)(C-b+bt)-(k+1)C=(1-t)igl[k(C-b)/t-bigr]ge0
]
then gives the last bound of (1) by AM–GM.

The symmetric expression reproduces the original (delta C+4/delta+3u^2/2) at (k=1). For (k=2) it is (2delta C/3+6/delta+3u^2), and at (k=3) it is (delta C/2+8/delta+9u^2/2). Rescaling to (delta_{m eff}=2delta/(k+1)) absorbs both degree-dependent terms involving (delta) exactly. The remaining surcharge over the linear constraint is (3(k-1)u^2/2). This is the extra height inherited from the private field; extra box dimension pays for the extra radix term but leaves this surcharge.

## Uniform gap

Take (C_0=2.154630), for which the existing linear lower certificate excludes (6b(C_0-b)ge3u^2/2+4sqrt{C_0}) jointly with (C_0ge b+p(u)). If (Cle C_0), monotonicity is unnecessary: (1) and the private bound already give a linear candidate at budget (C) via (delta_{m eff}=2/sqrt C) in the ledger, and the original inequalities with that same degree parameter remain feasible after increasing the budget to (C_0). Indeed the derivative of (6b(C-b)-delta_{m eff}C) is positive since (1) implies (6bge4/sqrt C).

If (C_0<Cle2.177), put (Delta=C-C_0) and (b'=b-Delta>0), using (bge2/(3sqrt C)) from (1). The private constraint still holds at ((C_0,b')). The terminal product falls by (6Delta(C-b)le6Delta C), while (4sqrt C) decreases. For every (kge2), the degree surcharge is at least (2/(3C)), by (4/(9u^2)le C). The rational check
[
 9(2.177-2.154630)(2.177)^2=0.95416910757<1
]
shows (6Delta C<2/(3C)). The new point thus meets the forbidden linear inequalities at (C_0). [Certified linear obstruction](../formal/cogentic/Cogentic/RandomizedScheduleFloor.lean)

The result leaves open outside-box proposal laws and direct enumeration of small-resultant or unusually smooth strata. It also leaves open using a different private field height or sharing terminal searches across requests with a proved coverage and cost bound.
