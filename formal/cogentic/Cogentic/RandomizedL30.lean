import Cogentic.RandomizedPaperLeafStatements
import Cogentic.RandomizedOneThirdAsymptotic

/-!
# L30: the genus-two partial factorer (KB Proposition H.3)

The C5 leaf `C5Leaf.genusTwoPartialFactorer` is the bounded genus-two
smoothness test of KeyBreak Proposition H.3 (p. 129).  The proposition supplies,
for `x, y ≥ 2`, `b(x) ≤ n`, `k_y = ⌈√(b(y) b(b(y)))⌉`, `z_y = 2^{k_y}`, and an
integer confidence `L_c ≥ 1`, a procedure `Smooth (x, y, L_c)` which returns a
verified `y`-smooth factorization, a verified prime factor `> y`, or `FAIL`,
with:

* accepting outputs always correct;
* bit cost `z_y 2^{⌈101 k_y / 100⌉} poly (n + b(y)) L_c` on every tape (H.5);
* under RH, for every sufficiently large `y`, `Pr [FAIL] ≤ 2 n exp (-64 L_c)`,
  uniformly over `y`-smooth inputs `x` with `b(x) ≤ n`.

The last line is exactly the `SubexpLoss` shape: with `L_c` chosen to dominate
`B · H + log (2 n)` it gives `Pr [FAIL] ≤ D^{-B}` for every `B`.  This file
decomposes the proposition into the paper's named inputs and proves that
reduction.

## What is decomposed

* `YounisShortIntervalEstimate` — Younis, arXiv:2409.05761, Theorem 1.3 under
  the ordinary Riemann hypothesis: the short-interval count of smooth integers
  in the central genus-two order interval `(p² - p^{3/2}/2, p²]`.
* `LPPOrderFibreEstimate` — Lenstra–Pila–Pomerance II, Theorem 1.1: the
  order-fibre count of quintic models attached to each eligible smooth order.
* `CantorArithmeticCostBound` — the H.5 cost of the gcd-checked Cantor
  arithmetic on the genus-two Jacobian modulo the input, together with a named
  correctness input `cantor_arithmetic`.
* `UsefulPrimeSplitBound` — the useful-prime argument of H.3 (H.13)–(H.14),
  fed by the `p^5` model supply of `modelCount_lower`: each unresolved node
  splits with probability at least `z_y^{-201/200}`.
* `CurveTrialCap`, `FactorTreeNodes`, `FailureUnionBound` — the trial cap, the
  fewer-than-`2 n` compressed factor tree, and the union bound over its nodes.
* `confidence_dominates` — the explicit choice of the confidence parameter
  `L_c`, which is what turns the paper's `2 n exp (-64 L_c)` into `D^{-B}`.

The proof of `SubexpLeaf` below is the real work: it combines the split bound
and the trial cap into `p R ≥ 64 L_c`, applies the Chernoff inequality
`(1 - p)^R ≤ exp (-p R)`, takes the union over the factor-tree nodes, and then
specializes the confidence parameter to every `B`.  The cost conclusion
`cost_sublinear` is recorded as an explicit H.5 input for audit; the C5 ledger
does not consume it (C4 charges the work), so the `SubexpLeaf` reduction does
not depend on it.

**Audit note.**  The blueprint paraphrases L30 as a *success* probability
`≥ exp (-δ H)`.  A lower bound on success alone is not a `SubexpLoss`; the
proposition itself states the upper bound `Pr [FAIL] ≤ 2 n exp (-64 L_c)`, and
that is the statement used here.  The deficit is a genuine positive failure
probability (`loss_pos`), not a zero loss.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL30

open Filter Real
open scoped Topology
open Cogentic.RandomizedEpochAnalyticInputs
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

/-! ## The paper-level sub-lemmas -/

/-- **Younis, Theorem 1.3 (under RH).**  In the central genus-two Hasse
interval `(p² - p^{3/2}/2, p²]`, the number of `Y`-smooth integers is at least
`p^{3/2} exp (-(1 + ε) t_p)`, where `t_p = √(log p · log log p)` and `ε → 0`.
The relative error is an explicit sequence so that the estimate is a statement
about the counting function rather than an opaque `o (1)`. -/
def YounisShortIntervalEstimate
    (p t err smoothOrders : ℕ → ℝ) : Prop :=
  ∀ n, p n ^ ((3 : ℝ) / 2) * exp (-(1 + err n) * t n) ≤ smoothOrders n

/-- **Lenstra–Pila–Pomerance II, Theorem 1.1.**  An eligible odd-trace order in
the central genus-two interval contributes at least
`p^{7/2} exp (-(1 + ε) t_p)` quintic models per order, after the `p - 1`
normalization which makes the quintic monic; the `1 / polylog p` loss is
absorbed into `err`.  Combined with `YounisShortIntervalEstimate`, the supply of
good monic models is `p^5 exp (-(1 + o(1)) t_p)` (`modelCount_lower`). -/
def LPPOrderFibreEstimate
    (p t err fibrePerOrder : ℕ → ℝ) : Prop :=
  ∀ n, p n ^ ((7 : ℝ) / 2) * exp (-(1 + err n) * t n) ≤ fibrePerOrder n

/-- **KB H.3 / (H.5), cost half.**  The bounded call with confidence `L_c` costs
at most `z_y · 2^{⌈101 k_y / 100⌉} · poly · L_c`.  Since
`z_y = exp (log 2 · k_y)` and the ceiling is at most `101 k_y / 100 + 1`, this
is bounded by `exp ((201 / 100) log 2 · k_y) · poly · L_c` after absorbing the
fixed factor `2` into `poly`. -/
def CantorArithmeticCostBound
    (k polyFactor Lc trialCost : ℕ → ℝ) : Prop :=
  ∀ n, trialCost n ≤
    exp (((201 : ℝ) / 100) * (Real.log 2 * k n)) * polyFactor n * Lc n

/-- **KB H.3, useful-prime split bound (H.13)–(H.14).**  At every unresolved
factor-tree node, one original curve trial splits a composite containing a prime
`z_y < p ≤ y` with probability at least
`z_y^{-201/200} = exp (-((201 / 200) log 2) k_y)`. -/
def UsefulPrimeSplitBound (k pTrial : ℕ → ℝ) : Prop :=
  ∀ n, exp (-(((201 : ℝ) / 200) * (Real.log 2 * k n))) ≤ pTrial n

/-- **KB H.3, trial cap (H.14).**  At most `R_curve = 2^{⌈101 k_y / 100⌉} L_c`
independent curve trials are performed at each node. -/
def CurveTrialCap (k Lc : ℕ → ℝ) (Rcurve : ℕ → ℕ) : Prop :=
  ∀ n, exp ((((101 : ℝ) / 100) * (Real.log 2 * k n))) * Lc n ≤ (Rcurve n : ℝ)

/-- **KB H.3, union bound over the compressed factor tree.**  The FAIL
probability is at most the number of nodes times the per-node trial failure
probability. -/
def FailureUnionBound
    (pTrial : ℕ → ℝ) (Rcurve nodes : ℕ → ℕ) (failure : ℕ → ℝ) : Prop :=
  ∀ n, failure n ≤ (nodes n : ℝ) * (1 - pTrial n) ^ (Rcurve n)

/-- **KB H.3, factor-tree size.**  A compressed factor tree has fewer than
`2 n` nodes. -/
def FactorTreeNodes (nodes : ℕ → ℕ) : Prop := ∀ n, nodes n ≤ 2 * n

/-! ## The decomposed L30 inputs -/

/-- The explicit inputs of KB Proposition H.3.

The numerical functions are indexed by the input bit bound `n`; this is the
same convention as the C5 slots.  `p` is the prime whose smooth order is being
counted, `t` is the paper's `t_p`, `err` is the explicit `o (1)` in Younis and
LPP, and `smoothOrders`/`fibrePerOrder` are the two counting functions of those
theorems.  The remaining fields are the H.3 proof's split/trial/tree data and
its H.5 cost. -/
structure L30Inputs where
  /-- The prime whose smooth genus-two order is counted at scale `n`. -/
  p : ℕ → ℝ
  /-- The prime is at least `2`. -/
  p_ge_two : ∀ n, 2 ≤ p n
  /-- The prime is positive. -/
  p_pos : ∀ n, 0 < p n
  /-- `t_p = √(log p · log log p)`. -/
  t : ℕ → ℝ
  /-- `t_p` is nonnegative. -/
  t_nonneg : ∀ n, 0 ≤ t n
  /-- The explicit relative error in the Younis/LPP estimates. -/
  err : ℕ → ℝ
  /-- The relative error is nonnegative. -/
  err_nonneg : ∀ n, 0 ≤ err n
  /-- The relative error tends to zero.  This is the `1 + o (1)` in the two
  analytic estimates. -/
  err_tendsto : Tendsto err atTop (𝓝 0)
  /-- The number of smooth orders in the central Hasse interval. -/
  smoothOrders : ℕ → ℝ
  /-- The smooth-order count is nonnegative. -/
  smoothOrders_nonneg : ∀ n, 0 ≤ smoothOrders n
  /-- The number of quintic models per smooth order. -/
  fibrePerOrder : ℕ → ℝ
  /-- The fibre count is nonnegative. -/
  fibrePerOrder_nonneg : ∀ n, 0 ≤ fibrePerOrder n
  /-- The ordinary Riemann hypothesis, consumed by Younis's theorem. -/
  rh : Prop
  /-- The ordinary Riemann hypothesis holds. -/
  rh_holds : rh
  /-- **Younis, Theorem 1.3**, conditional on `rh`. -/
  younis_short_interval :
    rh → YounisShortIntervalEstimate p t err smoothOrders
  /-- **Lenstra–Pila–Pomerance II, Theorem 1.1** (order-fibre count). -/
  lpp_order_fibre : LPPOrderFibreEstimate p t err fibrePerOrder
  /-- `k_y = ⌈√(b(y) b(b(y)))⌉`, recorded as a real. -/
  k : ℕ → ℝ
  /-- `k_y` is nonnegative. -/
  k_nonneg : ∀ n, 0 ≤ k n
  /-- The asymptotic range of H.3: `k_y ≥ 1200`, which is precisely what makes
  the trial cap beat the split probability by the factor `64`. -/
  k_large : ∀ n, 1200 ≤ k n
  /-- The confidence parameter `L_c ≥ 1`. -/
  Lc : ℕ → ℝ
  /-- The confidence parameter is at least one. -/
  Lc_ge_one : ∀ n, 1 ≤ Lc n
  /-- **Confidence amplification.**  `L_c` dominates every fixed multiple of the
  ledger scale together with the `log (2 n)` of H.3's failure bound.  This is
  the explicit choice of the free confidence parameter in the proposition. -/
  confidence_dominates : ∀ B : ℝ, 0 < B →
    ∀ᶠ n : ℕ in atTop, B * scale n + Real.log (2 * (n : ℝ)) ≤ 64 * Lc n
  /-- The probability of a proper split in one original curve trial. -/
  pTrial : ℕ → ℝ
  /-- The split probability is nonnegative. -/
  pTrial_nonneg : ∀ n, 0 ≤ pTrial n
  /-- The split probability is at most one. -/
  pTrial_le_one : ∀ n, pTrial n ≤ 1
  /-- **The useful-prime split bound** (H.13)–(H.14).  The `p^5` model
  supply of `modelCount_lower`, together with the CRT split argument and the
  odd scalar, gives this bound at every unresolved node. -/
  useful_prime_split : UsefulPrimeSplitBound k pTrial
  /-- The number of curve trials at each factor-tree node. -/
  Rcurve : ℕ → ℕ
  /-- **The trial cap** (H.14). -/
  curve_trial_cap : CurveTrialCap k Lc Rcurve
  /-- The number of nodes in the compressed factor tree. -/
  nodes : ℕ → ℕ
  /-- The factor tree has at least one node at every positive input. -/
  nodes_pos : ∀ n, 1 ≤ n → 0 < nodes n
  /-- **The factor-tree size bound.** -/
  factor_tree_nodes : FactorTreeNodes nodes
  /-- The FAIL probability of `Smooth (x, y, L_c)`. -/
  failure : ℕ → ℝ
  /-- The failure probability is positive: the deficit is not set to zero. -/
  failure_pos : ∀ n, 0 < failure n
  /-- **The union bound** over the compressed factor tree. -/
  failure_union : FailureUnionBound pTrial Rcurve nodes failure
  /-- The polynomial factor `poly (n + b(y))` of H.5. -/
  polyFactor : ℕ → ℝ
  /-- The polynomial factor is nonnegative. -/
  polyFactor_nonneg : ∀ n, 0 ≤ polyFactor n
  /-- The per-call cost bound of H.5. -/
  trialCost : ℕ → ℝ
  /-- The per-call cost is nonnegative. -/
  trialCost_nonneg : ∀ n, 0 ≤ trialCost n
  /-- **The H.5 cost bound**, including the confidence factor `L_c`. -/
  cantor_cost : CantorArithmeticCostBound k polyFactor Lc trialCost
  /-- The total cost of the bounded factorer, including the factor-tree
  traversal. -/
  totalCost : ℕ → ℝ
  /-- The total cost is nonnegative. -/
  totalCost_nonneg : ∀ n, 0 ≤ totalCost n
  /-- The total cost is bounded by the per-call cost. -/
  total_cost_le : ∀ n, totalCost n ≤ trialCost n
  /-- **KB H.3, cost conclusion:** the bounded factorer costs `exp (o (H))`. -/
  cost_sublinear : ∀ δ : ℝ, 0 < δ →
    ∀ᶠ n : ℕ in atTop, totalCost n ≤ exp (δ * scale n)
  /-- The genus-two Jacobian/Cantor-arithmetic correctness statement: every
  gcd-checked Mumford operation is correct on each prime component, and a
  disagreement on a composite modulus exposes a proper factor.  This is the
  arithmetic half of H.3 and is recorded as a named input rather than
  formalized. -/
  cantor_arithmetic : Prop
  /-- The Cantor-arithmetic correctness input holds. -/
  cantor_arithmetic_holds : cantor_arithmetic

namespace L30Inputs

variable (I : L30Inputs)

/-! ## The Chernoff and counting steps -/

/-- **Chernoff bound for a single node.**  If a trial succeeds with probability
`p ∈ [0, 1]`, then `R` independent trials all fail with probability at most
`exp (-p R)`. -/
theorem one_sub_pow_le_exp {p : ℝ} (hp1 : p ≤ 1) (R : ℕ) :
    (1 - p) ^ R ≤ exp (-(p * (R : ℝ))) := by
  have hbase : 1 - p ≤ exp (-p) := by
    have h := Real.add_one_le_exp (-p)
    linarith only [h]
  have hpow : (1 - p) ^ R ≤ (exp (-p)) ^ R :=
    pow_le_pow_left₀ (by linarith only [hp1]) hbase R
  have hR : (exp (-p)) ^ R = exp (-(p * (R : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa [hR] using hpow

/-- The single-node failure probability is at most the Chernoff majorant. -/
theorem failure_le_chernoff (n : ℕ) :
    I.failure n ≤
      (I.nodes n : ℝ) * exp (-(I.pTrial n * (I.Rcurve n : ℝ))) := by
  have hcher := one_sub_pow_le_exp (I.pTrial_le_one n) (I.Rcurve n)
  exact (I.failure_union n).trans
    (mul_le_mul_of_nonneg_left hcher (Nat.cast_nonneg _))

/-- **The split probability times the trial cap.**  The loss `201/200` of the
split bound and the cap `101/100` leave `1/200` of `k_y`; the asymptotic range
`k_y ≥ 1200` makes the exponent at least `6 log 2`, hence at least `64`. -/
theorem pTrial_mul_Rcurve_ge (n : ℕ) :
    64 * I.Lc n ≤ I.pTrial n * (I.Rcurve n : ℝ) := by
  set a : ℝ := Real.log 2 * I.k n with ha
  have hp : exp (-(((201 : ℝ) / 200) * a)) ≤ I.pTrial n := by
    simpa [a] using I.useful_prime_split n
  have hr : exp ((((101 : ℝ) / 100) * a)) * I.Lc n ≤ (I.Rcurve n : ℝ) := by
    simpa [a] using I.curve_trial_cap n
  have hp_nn : 0 ≤ exp (-(((201 : ℝ) / 200) * a)) := (exp_pos _).le
  have hb_nn : 0 ≤ exp ((((101 : ℝ) / 100) * a)) * I.Lc n :=
    mul_nonneg (exp_pos _).le (by linarith [I.Lc_ge_one n])
  have hmul := mul_le_mul hp hr hb_nn (hp_nn.trans hp)
  have hprod :
      exp (-(((201 : ℝ) / 200) * a)) *
          (exp ((((101 : ℝ) / 100) * a)) * I.Lc n) =
        exp (((1 : ℝ) / 200) * a) * I.Lc n := by
    rw [← mul_assoc]
    rw [show exp (-(((201 : ℝ) / 200) * a)) *
          exp ((((101 : ℝ) / 100) * a)) = exp (((1 : ℝ) / 200) * a) by
      rw [← Real.exp_add]
      congr 1
      ring]
  rw [hprod] at hmul
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : (1200 : ℝ) ≤ I.k n := I.k_large n
  have hklog : (1200 : ℝ) * Real.log 2 ≤ I.k n * Real.log 2 :=
    mul_le_mul_of_nonneg_right hk hlog2.le
  have h6 : (6 : ℝ) * Real.log 2 ≤ ((1 : ℝ) / 200) * a := by
    dsimp [a]
    nlinarith only [hklog]
  have h64 : (64 : ℝ) ≤ exp (((1 : ℝ) / 200) * a) := by
    have h64eq : (64 : ℝ) = exp (6 * Real.log 2) := by
      have hlog : Real.log 64 = 6 * Real.log 2 := by
        rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
        norm_num
      rw [← hlog, Real.exp_log (by norm_num)]
    rw [h64eq]
    exact exp_le_exp.mpr h6
  have hLc_nn : 0 ≤ I.Lc n := by linarith [I.Lc_ge_one n]
  have hscale := mul_le_mul_of_nonneg_right h64 hLc_nn
  linarith only [hmul, hscale]

/-- **H.3's failure bound.**  The union bound, the Chernoff step, the trial cap,
and the `2 n` node bound give `Pr [FAIL] ≤ 2 n exp (-64 L_c)`. -/
theorem failure_le_two_n_exp (n : ℕ) :
    I.failure n ≤ 2 * (n : ℝ) * exp (-(64 * I.Lc n)) := by
  have hcher := I.failure_le_chernoff n
  have hpR := I.pTrial_mul_Rcurve_ge n
  have hexp :
      exp (-(I.pTrial n * (I.Rcurve n : ℝ))) ≤ exp (-(64 * I.Lc n)) :=
    exp_le_exp.mpr (by linarith only [hpR])
  have hnodes : (I.nodes n : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast I.factor_tree_nodes n
  calc
    I.failure n ≤
        (I.nodes n : ℝ) * exp (-(I.pTrial n * (I.Rcurve n : ℝ))) := hcher
    _ ≤ (2 * (n : ℝ)) * exp (-(64 * I.Lc n)) :=
      mul_le_mul hnodes hexp (exp_pos _).le (by positivity)
    _ = 2 * (n : ℝ) * exp (-(64 * I.Lc n)) := by ring

/-- **KB Proposition H.3, FAIL bound** (the form used by the ledger). -/
theorem h3_failure_bound (n : ℕ) :
    I.failure n ≤ 2 * (n : ℝ) * exp (-(64 * I.Lc n)) :=
  I.failure_le_two_n_exp n

/-- **KB Proposition H.3, H.5 cost bound** on one bounded call. -/
theorem h3_cost_bound (n : ℕ) :
    I.trialCost n ≤
      exp (((201 : ℝ) / 100) * (Real.log 2 * I.k n)) *
        I.polyFactor n * I.Lc n :=
  I.cantor_cost n

/-! ## The C5 deficit -/

/-- The L30 deficit charged to the C5 ledger: the actual FAIL probability of
the bounded smoothness test. -/
noncomputable def loss (n : ℕ) : ℝ := I.failure n

/-- The deficit is nonnegative. -/
theorem loss_nonneg (n : ℕ) : 0 ≤ I.loss n := (I.failure_pos n).le

/-- The deficit is positive: no loss is set to zero. -/
theorem loss_pos (n : ℕ) : 0 < I.loss n := I.failure_pos n

/-- **The L30 paper statement.**  For every `B`, the confidence choice
`confidence_dominates` makes the H.3 failure bound at most `D^{-B}`. -/
theorem loss_le_exp_neg (B : ℝ) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, I.loss n ≤ exp (-B * scale n) := by
  filter_upwards [I.confidence_dominates B hB,
    eventually_ge_atTop (1 : ℕ)] with n hconf hn
  have hmain := I.failure_le_two_n_exp n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < 2 * (n : ℝ) := by nlinarith only [hn1]
  calc
    I.loss n = I.failure n := rfl
    _ ≤ 2 * (n : ℝ) * exp (-(64 * I.Lc n)) := hmain
    _ = exp (Real.log (2 * (n : ℝ))) * exp (-(64 * I.Lc n)) := by
      rw [Real.exp_log hnpos]
    _ = exp (Real.log (2 * (n : ℝ)) + -(64 * I.Lc n)) := by
      rw [← Real.exp_add]
    _ = exp (Real.log (2 * (n : ℝ)) - 64 * I.Lc n) := by ring_nf
    _ ≤ exp (-B * scale n) := by
      apply exp_le_exp.mpr
      linarith only [hconf]

/-- The manuscript's `D^{-B}` statement for the L30 deficit. -/
theorem subexpLoss : SubexpLoss I.loss := fun B hB => I.loss_le_exp_neg B hB

/-- **The L30 `SubexpLeaf`.** -/
noncomputable def toSubexpLeaf : SubexpLeaf where
  loss := I.loss
  loss_nonneg := I.loss_nonneg
  paper := I.subexpLoss

/-- The `B = 2` instance is exactly the `C5Inputs.l30` eventuality. -/
theorem slot_le {slots : C5LossSlots}
    (h : slots .genusTwoPartialFactorer = I.loss) :
    ∀ᶠ n : ℕ in atTop,
      slots .genusTwoPartialFactorer n ≤ exp (-(2 : ℝ) * scale n) := by
  rw [h]
  exact I.subexpLoss 2 (by norm_num)

/-! ## Combining the two analytic supply estimates -/

/-- The smooth-order count times the per-order fibre count is the total supply
of good monic quintic models.  Younis gives `p^{3/2}` smooth orders and LPP
gives `p^{7/2}` models per order, so the product is `p^5 exp (-(1 + o(1)) t_p)`.
The exponent here is `2 (1 + ε)`, which is `1 + (1 + 2ε)` with `1 + 2ε → 1`. -/
theorem modelCount_lower (n : ℕ) :
    I.p n ^ (5 : ℝ) * exp (-(2 * (1 + I.err n)) * I.t n) ≤
      I.smoothOrders n * I.fibrePerOrder n := by
  have hy := I.younis_short_interval I.rh_holds n
  have hl := I.lpp_order_fibre n
  have hl_nn :
      0 ≤ I.p n ^ ((7 : ℝ) / 2) * exp (-(1 + I.err n) * I.t n) :=
    mul_nonneg (Real.rpow_nonneg (I.p_pos n).le _) (exp_pos _).le
  have hprod := mul_le_mul hy hl hl_nn (I.smoothOrders_nonneg n)
  have hrpow :
      I.p n ^ ((3 : ℝ) / 2) * I.p n ^ ((7 : ℝ) / 2) = I.p n ^ (5 : ℝ) := by
    rw [← Real.rpow_add (I.p_pos n) ((3 : ℝ) / 2) ((7 : ℝ) / 2)]
    norm_num
  have hexp :
      exp (-(1 + I.err n) * I.t n) * exp (-(1 + I.err n) * I.t n) =
        exp (-(2 * (1 + I.err n)) * I.t n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    I.p n ^ (5 : ℝ) * exp (-(2 * (1 + I.err n)) * I.t n) =
        (I.p n ^ ((3 : ℝ) / 2) * exp (-(1 + I.err n) * I.t n)) *
          (I.p n ^ ((7 : ℝ) / 2) * exp (-(1 + I.err n) * I.t n)) := by
      rw [← hrpow, ← hexp]
      ring
    _ ≤ I.smoothOrders n * I.fibrePerOrder n := hprod

end L30Inputs

/-! ## Axiom audit -/

#print axioms L30Inputs.one_sub_pow_le_exp
#print axioms L30Inputs.failure_le_chernoff
#print axioms L30Inputs.pTrial_mul_Rcurve_ge
#print axioms L30Inputs.failure_le_two_n_exp
#print axioms L30Inputs.h3_failure_bound
#print axioms L30Inputs.h3_cost_bound
#print axioms L30Inputs.loss_le_exp_neg
#print axioms L30Inputs.subexpLoss
#print axioms L30Inputs.toSubexpLeaf
#print axioms L30Inputs.slot_le
#print axioms L30Inputs.modelCount_lower

end Cogentic.RandomizedL30
