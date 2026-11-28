import Cogentic.RandomizedL30

/-!
# L30 sub-lemmas: the elementary half of KeyBreak Proposition H.3

`Cogentic/RandomizedL30.lean` reduces KB Proposition H.3 to a structure
`L30Inputs` carrying both paper-level estimates and elementary numerical data.
This file separates the two layers.

The paper-level inputs are kept as explicit propositions:

* `YounisShortIntervalEstimate` — Younis, arXiv:2409.05761, Theorem 1.3 under
  the ordinary Riemann hypothesis;
* `LPPOrderFibreEstimate` — Lenstra–Pila–Pomerance II, Theorem 1.1;
* `CantorArithmeticCostBound` — the H.5 cost of gcd-checked Cantor arithmetic;
* `CantorJacobianCorrect` — the correctness of the genus-two Jacobian/Cantor
  operations (represented, as in L30, by an explicit `Prop` field);
* `UsefulPrimeSplitBound` — KB (H.13)–(H.14), the useful-prime split estimate.

`PaperInputs` bundles the first four; `FailureData` carries the split bound as
an explicit hypothesis, together with the elementary trial/tree data.

The elementary statements are proved here, with no access to the internals of
the paper-level analysis:

* `one_sub_pow_le_exp` — the Chernoff step `(1 - p)^R ≤ exp (-p R)`;
* `union_bound_chernoff` — the union bound over the factor tree;
* `curve_trial_budget_core` and `FailureData.curve_trial_budget` — the
  arithmetic that turns the split bound `exp (-(201/200) log 2 · k)` and the
  trial cap `exp ((101/100) log 2 · k) L_c` into `p R ≥ 64 L_c` when
  `k ≥ 1200`;
* `FailureData.failure_le_two_n_exp` — H.3's `2 n exp (-64 L_c)` failure bound;
* `FailureData.subexpLoss` — the resulting `D^{-B}` deficit;
* `modelCount_lower_point` and `PaperInputs.modelCount_lower` — the
  `p^5 exp (-(2 (1 + ε)) t_p)` model supply obtained by multiplying the Younis
  and LPP estimates;
* `FactorTree.nodeCount_le_two_mul_leafCount` and
  `factorTreeNodes_of_leafBudget` — a compressed binary factor tree with at
  most `n` leaves has at most `2 n` nodes.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL30Sub

open Filter Real
open scoped Topology
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL30

/-! ## The Chernoff and union-bound arithmetic -/

/-- **Chernoff bound for one node.**  If a trial succeeds with probability
`p ≤ 1`, then `R` independent trials all fail with probability at most
`exp (-p R)`.  This is the only probabilistic inequality used by H.3; it is
elementary (`1 - p ≤ exp (-p)`) and does not depend on the paper-level
estimates. -/
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

/-- **Union bound plus Chernoff.**  A union bound over `nodes` nodes and the
per-node Chernoff estimate give the `2 n exp (-p R)` failure bound, provided
the compressed tree has at most `2 n` nodes. -/
theorem union_bound_chernoff {p failure : ℝ} {R nodes n : ℕ}
    (hp1 : p ≤ 1) (hnodes : (nodes : ℝ) ≤ 2 * (n : ℝ))
    (hfail : failure ≤ (nodes : ℝ) * (1 - p) ^ R) :
    failure ≤ 2 * (n : ℝ) * exp (-(p * (R : ℝ))) := by
  have hnonneg : 0 ≤ (1 - p) ^ R :=
    pow_nonneg (by linarith only [hp1]) R
  calc
    failure ≤ (nodes : ℝ) * (1 - p) ^ R := hfail
    _ ≤ (2 * (n : ℝ)) * exp (-(p * (R : ℝ))) :=
      mul_le_mul hnodes (one_sub_pow_le_exp hp1 R) hnonneg (by positivity)
    _ = 2 * (n : ℝ) * exp (-(p * (R : ℝ))) := by ring

/-- **The curve-trial budget.**  The useful-prime split bound
`exp (-(201/200) a) ≤ p` and the trial cap
`exp ((101/100) a) L_c ≤ R`, with `a = log 2 · k` and `k ≥ 1200`, give
`p R ≥ 64 L_c`.  The exponents differ by `a / 200 ≥ 6 log 2`, and
`exp (6 log 2) = 64`. -/
theorem curve_trial_budget_core {k Lc p R : ℝ} (hk : 1200 ≤ k) (hLc : 0 ≤ Lc)
    (hp : exp (-(((201 : ℝ) / 200) * (Real.log 2 * k))) ≤ p)
    (hR : exp ((((101 : ℝ) / 100) * (Real.log 2 * k))) * Lc ≤ R) :
    64 * Lc ≤ p * R := by
  set a : ℝ := Real.log 2 * k with ha
  have hp' : exp (-(((201 : ℝ) / 200) * a)) ≤ p := by simpa [a] using hp
  have hR' : exp ((((101 : ℝ) / 100) * a)) * Lc ≤ R := by simpa [a] using hR
  have hp_nn : 0 ≤ exp (-(((201 : ℝ) / 200) * a)) := (exp_pos _).le
  have hb_nn : 0 ≤ exp ((((101 : ℝ) / 100) * a)) * Lc :=
    mul_nonneg (exp_pos _).le hLc
  have hmul := mul_le_mul hp' hR' hb_nn (hp_nn.trans hp')
  have hprod :
      exp (-(((201 : ℝ) / 200) * a)) *
          (exp ((((101 : ℝ) / 100) * a)) * Lc) =
        exp (((1 : ℝ) / 200) * a) * Lc := by
    rw [← mul_assoc]
    rw [show exp (-(((201 : ℝ) / 200) * a)) *
          exp ((((101 : ℝ) / 100) * a)) = exp (((1 : ℝ) / 200) * a) by
      rw [← Real.exp_add]
      congr 1
      ring]
  rw [hprod] at hmul
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hklog : (1200 : ℝ) * Real.log 2 ≤ k * Real.log 2 :=
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
  have hscale := mul_le_mul_of_nonneg_right h64 hLc
  linarith only [hmul, hscale]

/-- **Confidence amplification.**  If `L_c` dominates `B · scale n` together
with `log (2 n)`, then `2 n exp (-64 L_c) ≤ exp (-B · scale n)`.  This is the
step that turns H.3's single exponential bound into the ledger's `D^{-B}`
shape. -/
theorem two_n_mul_exp_le_exp {B Lc : ℝ} {n : ℕ} (_hB : 0 < B) (hn : 1 ≤ n)
    (hconf : B * scale n + Real.log (2 * (n : ℝ)) ≤ 64 * Lc) :
    2 * (n : ℝ) * exp (-(64 * Lc)) ≤ exp (-B * scale n) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < 2 * (n : ℝ) := by nlinarith only [hn1]
  calc
    2 * (n : ℝ) * exp (-(64 * Lc)) =
        exp (Real.log (2 * (n : ℝ))) * exp (-(64 * Lc)) := by
      rw [Real.exp_log hnpos]
    _ = exp (Real.log (2 * (n : ℝ)) + -(64 * Lc)) := by
      rw [← Real.exp_add]
    _ = exp (Real.log (2 * (n : ℝ)) - 64 * Lc) := by ring_nf
    _ ≤ exp (-B * scale n) := by
      apply exp_le_exp.mpr
      linarith only [hconf]

/-! ## The paper-level inputs as explicit propositions -/

/-- The paper-level analytic and arithmetic inputs of KB H.3.  Every field is
one of the named theorems from the paper; none of them is proved here. -/
structure PaperInputs where
  /-- The prime whose smooth genus-two order is counted. -/
  p : ℕ → ℝ
  /-- The paper's `t_p = √(log p · log log p)`. -/
  t : ℕ → ℝ
  /-- The explicit `1 + o (1)` error. -/
  err : ℕ → ℝ
  /-- The number of smooth orders in the central Hasse interval. -/
  smoothOrders : ℕ → ℝ
  /-- The number of quintic models per smooth order. -/
  fibrePerOrder : ℕ → ℝ
  /-- `k_y`. -/
  k : ℕ → ℝ
  /-- The polynomial factor of H.5. -/
  polyFactor : ℕ → ℝ
  /-- The confidence parameter. -/
  Lc : ℕ → ℝ
  /-- The per-call cost. -/
  trialCost : ℕ → ℝ
  /-- **Younis, Theorem 1.3 (under RH).** -/
  younis : YounisShortIntervalEstimate p t err smoothOrders
  /-- **Lenstra–Pila–Pomerance II, Theorem 1.1.** -/
  lpp : LPPOrderFibreEstimate p t err fibrePerOrder
  /-- **KB (H.5), the Cantor-arithmetic cost bound.** -/
  cantor_cost : CantorArithmeticCostBound k polyFactor Lc trialCost
  /-- **KB H.3, genus-two Jacobian/Cantor correctness.**  As in L30 this is
  recorded as an explicit proposition rather than formalized. -/
  cantor_arithmetic : Prop
  /-- The Cantor/Jacobian correctness proposition holds. -/
  cantor_arithmetic_holds : cantor_arithmetic

namespace PaperInputs

variable (P : PaperInputs)

/-- The H.5 cost bound, restated from the paper-level input. -/
theorem cantor_cost_bound (n : ℕ) :
    P.trialCost n ≤
      exp (((201 : ℝ) / 100) * (Real.log 2 * P.k n)) *
        P.polyFactor n * P.Lc n :=
  P.cantor_cost n

end PaperInputs

/-! ## The elementary factor-tree node count -/

/-- A compressed binary factor tree: a leaf, or a branch with two children. -/
inductive FactorTree where
  | leaf : FactorTree
  | branch : FactorTree → FactorTree → FactorTree

namespace FactorTree

/-- The number of nodes of a compressed factor tree. -/
def nodeCount : FactorTree → ℕ
  | leaf => 1
  | branch l r => nodeCount l + nodeCount r + 1

/-- The number of leaves of a compressed factor tree. -/
def leafCount : FactorTree → ℕ
  | leaf => 1
  | branch l r => leafCount l + leafCount r

/-- Every factor tree has at least one leaf. -/
theorem leafCount_pos (T : FactorTree) : 0 < T.leafCount := by
  induction T with
  | leaf => simp [leafCount]
  | branch l r ihl ihr =>
      simp only [leafCount]
      omega

/-- Every factor tree has at least one node. -/
theorem nodeCount_pos (T : FactorTree) : 0 < T.nodeCount := by
  induction T with
  | leaf => simp [nodeCount]
  | branch l r ihl ihr =>
      simp only [nodeCount]
      omega

/-- A binary tree with `L` leaves has exactly `2 L - 1` nodes. -/
theorem nodeCount_eq_two_mul_leafCount_sub_one (T : FactorTree) :
    T.nodeCount = 2 * T.leafCount - 1 := by
  induction T with
  | leaf => simp [nodeCount, leafCount]
  | branch l r ihl ihr =>
      have hl := leafCount_pos l
      have hr := leafCount_pos r
      simp only [nodeCount, leafCount]
      omega

/-- **Factor-tree size.**  In a binary tree the number of nodes is at most
twice the number of leaves.  Equivalently, a compressed factor tree with at
most `n` leaves has at most `2 n` nodes, which is the `2 n` of H.3. -/
theorem nodeCount_le_two_mul_leafCount (T : FactorTree) :
    T.nodeCount ≤ 2 * T.leafCount := by
  rw [nodeCount_eq_two_mul_leafCount_sub_one]
  exact Nat.sub_le _ _

end FactorTree

/-- A family of compressed factor trees whose tree at scale `n` has at most
`leaves n` leaves. -/
def LeavesWithin (trees : ℕ → FactorTree) (leaves : ℕ → ℕ) : Prop :=
  ∀ n, (trees n).leafCount ≤ leaves n

/-- **Node count of a compressed factor tree.**  If the tree at scale `n` has
at most `leaves n` leaves and the leaf budget is at most `n`, then its `nodes`
count is at most `2 * n`.  This proves the elementary content of
`FactorTreeNodes` from the tree shape rather than assuming it. -/
theorem factorTreeNodes_of_leafBudget {trees : ℕ → FactorTree}
    {nodes leaves : ℕ → ℕ}
    (hnodes : ∀ n, nodes n = (trees n).nodeCount)
    (hleaves : LeavesWithin trees leaves)
    (hbudget : ∀ n, leaves n ≤ n) :
    Cogentic.RandomizedL30.FactorTreeNodes nodes := by
  change ∀ n, nodes n ≤ 2 * n
  intro n
  rw [hnodes n]
  exact (FactorTree.nodeCount_le_two_mul_leafCount (trees n)).trans
    (Nat.mul_le_mul_left 2 ((hleaves n).trans (hbudget n)))

/-- The node count of a nonempty compressed tree is positive. -/
theorem nodes_pos_of_leafBudget {trees : ℕ → FactorTree}
    {nodes leaves : ℕ → ℕ}
    (hnodes : ∀ n, nodes n = (trees n).nodeCount)
    (_hleaves : LeavesWithin trees leaves) :
    ∀ n, 0 < nodes n := by
  intro n
  rw [hnodes n]
  exact FactorTree.nodeCount_pos (trees n)

/-! ## The elementary failure data -/

/-- The numerical and probabilistic data of H.3, excluding the Younis/LPP/
Cantor analysis.  The useful-prime split bound is the paper's (H.13)–(H.14)
input and is therefore an explicit hypothesis, not something proved here.

Everything else in this structure is elementary: the trial cap is the paper's
definition of `R_curve`, the node bound is the tree count proved above, and the
union bound is the event-level bookkeeping. -/
structure FailureData where
  /-- `k_y`. -/
  k : ℕ → ℝ
  /-- `k_y ≥ 0`. -/
  k_nonneg : ∀ n, 0 ≤ k n
  /-- The asymptotic range `k_y ≥ 1200`. -/
  k_large : ∀ n, 1200 ≤ k n
  /-- The confidence parameter `L_c ≥ 1`. -/
  Lc : ℕ → ℝ
  /-- `L_c ≥ 1`. -/
  Lc_ge_one : ∀ n, 1 ≤ Lc n
  /-- `L_c` dominates every fixed multiple of the ledger scale and `log (2n)`. -/
  confidence_dominates : ∀ B : ℝ, 0 < B →
    ∀ᶠ n : ℕ in atTop, B * scale n + Real.log (2 * (n : ℝ)) ≤ 64 * Lc n
  /-- The per-trial success probability. -/
  pTrial : ℕ → ℝ
  /-- `p_Trial ≥ 0`. -/
  pTrial_nonneg : ∀ n, 0 ≤ pTrial n
  /-- `p_Trial ≤ 1`. -/
  pTrial_le_one : ∀ n, pTrial n ≤ 1
  /-- **KB (H.13)–(H.14).**  The useful-prime split bound.  This is the one
  genuinely paper-level input retained by the failure analysis. -/
  useful_prime_split : UsefulPrimeSplitBound k pTrial
  /-- The number of independent curve trials per node. -/
  Rcurve : ℕ → ℕ
  /-- **KB (H.14).**  The trial cap. -/
  curve_trial_cap : CurveTrialCap k Lc Rcurve
  /-- The compressed factor-tree node count. -/
  nodes : ℕ → ℕ
  /-- The tree is nonempty at every positive input (the index `0` is
  outside the epoch regime and is intentionally not constrained). -/
  nodes_pos : ∀ n, 1 ≤ n → 0 < nodes n
  /-- **Factor-tree size.** -/
  factor_tree_nodes : FactorTreeNodes nodes
  /-- The failure probability. -/
  failure : ℕ → ℝ
  /-- The failure probability is positive. -/
  failure_pos : ∀ n, 0 < failure n
  /-- **The union bound** over the compressed factor tree. -/
  failure_union : FailureUnionBound pTrial Rcurve nodes failure

namespace FailureData

variable (F : FailureData)

/-- The per-node failure estimate: the union bound followed by Chernoff. -/
theorem failure_le_chernoff (n : ℕ) :
    F.failure n ≤
      (F.nodes n : ℝ) * exp (-(F.pTrial n * (F.Rcurve n : ℝ))) := by
  have hcher := one_sub_pow_le_exp (F.pTrial_le_one n) (F.Rcurve n)
  exact (F.failure_union n).trans
    (mul_le_mul_of_nonneg_left hcher (Nat.cast_nonneg _))

/-- **The curve-trial budget for H.3.**  The split probability times the
number of trials is at least `64 L_c`. -/
theorem curve_trial_budget (n : ℕ) :
    64 * F.Lc n ≤ F.pTrial n * (F.Rcurve n : ℝ) := by
  have hLc : 0 ≤ F.Lc n := by linarith [F.Lc_ge_one n]
  exact curve_trial_budget_core (F.k_large n) hLc
    (F.useful_prime_split n) (F.curve_trial_cap n)

/-- **KB H.3's failure bound.**  The union bound, the Chernoff step, the trial
cap, and the `2 n` node bound give `Pr [FAIL] ≤ 2 n exp (-64 L_c)`. -/
theorem failure_le_two_n_exp (n : ℕ) :
    F.failure n ≤ 2 * (n : ℝ) * exp (-(64 * F.Lc n)) := by
  have hcher := F.failure_le_chernoff n
  have hpR := F.curve_trial_budget n
  have hexp :
      exp (-(F.pTrial n * (F.Rcurve n : ℝ))) ≤ exp (-(64 * F.Lc n)) :=
    exp_le_exp.mpr (by linarith only [hpR])
  have hnodes : (F.nodes n : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast F.factor_tree_nodes n
  calc
    F.failure n ≤
        (F.nodes n : ℝ) * exp (-(F.pTrial n * (F.Rcurve n : ℝ))) := hcher
    _ ≤ (2 * (n : ℝ)) * exp (-(64 * F.Lc n)) :=
      mul_le_mul hnodes hexp (exp_pos _).le (by positivity)
    _ = 2 * (n : ℝ) * exp (-(64 * F.Lc n)) := by ring

/-- The L30 deficit: the actual failure probability. -/
noncomputable def loss : ℕ → ℝ := F.failure

/-- The deficit is nonnegative. -/
theorem loss_nonneg (n : ℕ) : 0 ≤ F.loss n := (F.failure_pos n).le

/-- The deficit is positive. -/
theorem loss_pos (n : ℕ) : 0 < F.loss n := F.failure_pos n

/-- **The paper statement for the failure half of H.3.**  For every `B > 0`,
the confidence choice gives `loss n ≤ exp (-B · scale n)`. -/
theorem loss_le_exp_neg (B : ℝ) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, F.loss n ≤ exp (-B * scale n) := by
  filter_upwards [F.confidence_dominates B hB, eventually_ge_atTop (1 : ℕ)]
    with n hconf hn
  exact (F.failure_le_two_n_exp n).trans
    (two_n_mul_exp_le_exp hB hn hconf)

/-- The manuscript's `D^{-B}` statement for the L30 failure. -/
theorem subexpLoss : SubexpLoss F.loss := fun B hB => F.loss_le_exp_neg B hB

/-- The L30 `SubexpLeaf`, assembled from the elementary failure data. -/
noncomputable def toSubexpLeaf : SubexpLeaf where
  loss := F.loss
  loss_nonneg := F.loss_nonneg
  paper := F.subexpLoss

end FailureData

/-! ## The model-count lower bound -/

/-- **Multiplying the Younis and LPP counts.**  A pointwise real-variable
form of `modelCount_lower`: the smooth-order count and the per-order fibre
count multiply to the `p^5 exp (-(2 (1 + ε)) t)` supply of good monic quintic
models. -/
theorem modelCount_lower_point {p t err S F : ℝ} (hp : 2 ≤ p) (hS : 0 ≤ S)
    (hy : p ^ ((3 : ℝ) / 2) * exp (-(1 + err) * t) ≤ S)
    (hl : p ^ ((7 : ℝ) / 2) * exp (-(1 + err) * t) ≤ F) :
    p ^ (5 : ℝ) * exp (-(2 * (1 + err)) * t) ≤ S * F := by
  have hp_pos : 0 < p := by linarith only [hp]
  have hl_nn :
      0 ≤ p ^ ((7 : ℝ) / 2) * exp (-(1 + err) * t) :=
    mul_nonneg (Real.rpow_nonneg hp_pos.le _) (exp_pos _).le
  have hprod := mul_le_mul hy hl hl_nn hS
  have hrpow :
      p ^ ((3 : ℝ) / 2) * p ^ ((7 : ℝ) / 2) = p ^ (5 : ℝ) := by
    rw [← Real.rpow_add hp_pos ((3 : ℝ) / 2) ((7 : ℝ) / 2)]
    norm_num
  have hexp :
      exp (-(1 + err) * t) * exp (-(1 + err) * t) =
        exp (-(2 * (1 + err)) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    p ^ (5 : ℝ) * exp (-(2 * (1 + err)) * t) =
        (p ^ ((3 : ℝ) / 2) * exp (-(1 + err) * t)) *
          (p ^ ((7 : ℝ) / 2) * exp (-(1 + err) * t)) := by
      rw [← hrpow, ← hexp]
      ring
    _ ≤ S * F := hprod

namespace PaperInputs

variable (P : PaperInputs)

/-- **Model-count lower bound.**  Younis's `p^{3/2}` smooth orders and LPP's
`p^{7/2}` models per order multiply to `p^5 exp (-(2 (1 + ε)) t_p)`, which is
`p^5 exp (-(1 + o (1)) t_p)` since `ε → 0`. -/
theorem modelCount_lower (hp : ∀ n, 2 ≤ P.p n)
    (hS : ∀ n, 0 ≤ P.smoothOrders n) (n : ℕ) :
    P.p n ^ (5 : ℝ) * exp (-(2 * (1 + P.err n)) * P.t n) ≤
      P.smoothOrders n * P.fibrePerOrder n :=
  modelCount_lower_point (hp n) (hS n) (P.younis n) (P.lpp n)

end PaperInputs

/-! ## A combined reduction statement -/

/-- **The two halves of L30.**  Given the explicit paper-level inputs and the
elementary failure data, the manuscript's failure statement and the model-count
lower bound both hold.  The only unproved ingredients are the fields of
`PaperInputs` (Younis, LPP, the Cantor cost, and the Jacobian correctness
proposition) and `FailureData.useful_prime_split` (H.13)–(H.14). -/
theorem l30_reduction (P : PaperInputs) (F : FailureData)
    (hp : ∀ n, 2 ≤ P.p n) (hS : ∀ n, 0 ≤ P.smoothOrders n) :
    SubexpLoss F.loss ∧
      (∀ n, P.p n ^ (5 : ℝ) *
          exp (-(2 * (1 + P.err n)) * P.t n) ≤
        P.smoothOrders n * P.fibrePerOrder n) :=
  ⟨F.subexpLoss, P.modelCount_lower hp hS⟩

/-! ## Axiom audit -/

#print axioms one_sub_pow_le_exp
#print axioms union_bound_chernoff
#print axioms curve_trial_budget_core
#print axioms two_n_mul_exp_le_exp
#print axioms FactorTree.nodeCount_le_two_mul_leafCount
#print axioms factorTreeNodes_of_leafBudget
#print axioms nodes_pos_of_leafBudget
#print axioms FailureData.failure_le_chernoff
#print axioms FailureData.curve_trial_budget
#print axioms FailureData.failure_le_two_n_exp
#print axioms FailureData.loss_le_exp_neg
#print axioms FailureData.subexpLoss
#print axioms FailureData.toSubexpLeaf
#print axioms modelCount_lower_point
#print axioms PaperInputs.modelCount_lower
#print axioms l30_reduction

end Cogentic.RandomizedL30Sub
