import Cogentic.RandomizedL30Sub

/-!
# L30: the useful-prime split bound from the `p^5` model supply

`Cogentic/RandomizedL30Sub.lean` leaves the useful-prime split bound
(H.13)–(H.14) as an abstract field of `FailureData`.  This file derives it from
the concrete model-count data of L30 and from the CRT/odd-scalar split
argument, and then feeds the derived data into the existing `CurveTrialCap`
and `ClusterBudget` arithmetic.

## The model count

For a prime `p`, the monic quintic models `y² = g(X)` over `𝔽_p` are the
coefficients of `g`; there are exactly `p^5` of them.  The L30 count
`PaperInputs.modelCount_lower` says that at least

```
p^5 · exp (-(2 (1 + ε)) t_p)
```

of them have a smooth Jacobian order in the central Hasse interval.  Call these
models *good*.  Writing

```
α = #good / p^5 ,
```

we have `α ≥ exp (-(2 (1 + ε)) t_p)`.

## The CRT split and the odd scalar

Choose one monic quintic uniformly modulo the composite `N = p q`.  By CRT its
reductions modulo `p` and modulo `q` are independent uniform quintics.  Let
`β` be the fraction of good models at the partner prime `q`.  The odd scalar
`σ = ∏_{r odd, r ≤ Y} r^{e_r}` (largest powers with `r^{e_r} ≤ 4N²`) kills the
marked class at a good prime and leaves it alive at a non-good prime.  Hence a
proper split occurs on the event

```
good at p  and  not good at q ,
```

whose probability under the product model is `α (1 - β)`.  We take the
capped probability `min 1 (α (1 - β))` as the per-trial split probability
`pTrial`; the cap is the trivial probability normalization and does not change
the lower bound.

## What is proved and what is assumed

The lower bound on `α` is *not* assumed: it is
`PaperInputs.modelCount_lower`.  The only genuinely missing counting input is

* `PartnerGoodSparse β` — at the partner prime at most half of the models are
  good, so `1 - β ≥ 1/2`.

This is the smallest explicit form of the sparsity of smooth orders that the
CRT argument needs.  The reduction is

```
PartnerGoodSparse β → UsefulPrimeSplitBound k pTrial .
```

The exponent `k_y` is then chosen concretely as

```
kModel n = max 1200 ((log 2 - (-(2 (1 + ε_n)) t_n)) / ((201/200) log 2)) ,
```

which absorbs the `p^5` loss, the CRT factor `1/2`, and the fixed margin
`1/200` of (H.13).  The trial cap is defined literally as

```
Rcurve n = max 1 ⌈exp ((101/100) (log 2 · kModel n)) · L_c n⌉ .
```

With these definitions `UsefulPrimeSplitBound`, `CurveTrialCap`, and the
budget inequality `64 L_c ≤ pTrial · Rcurve` all hold.  The last is packaged
in `ClusterBudget`, which is exactly the arithmetic consumed by
`FailureData.curve_trial_budget`; `failureDataOfClusterBudget` shows that the
derived data can replace the two abstract fields of `FailureData`.

Constants are positive throughout: `log 2 > 0`, `201/200 > 0`,
`101/100 > 0`, and `kModel ≥ 1200`.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Cogentic.RandomizedL30SplitBound

open Filter Real
open scoped Topology
open Cogentic.RandomizedL30Sub
open Cogentic.RandomizedL30
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic

noncomputable section

/-! ## The explicit model-count objects -/

/-- The number of monic quintic models over `𝔽_p`: the five remaining
coefficients of `X^5 + a_4 X^4 + ⋯ + a_0` range freely, so the total is
`p^5`. -/
def totalQuinticModels (p : ℕ → ℝ) (n : ℕ) : ℝ := p n ^ (5 : ℝ)

/-- The number of *good* models supplied by the L30 count: the smooth orders in
the central Hasse interval times the number of quintic models per order. -/
def goodModelCount (P : PaperInputs) (n : ℕ) : ℝ :=
  P.smoothOrders n * P.fibrePerOrder n

/-- The fraction `α = #good / p^5` at the first prime. -/
def goodFraction (P : PaperInputs) (n : ℕ) : ℝ :=
  goodModelCount P n / totalQuinticModels P.p n

/-- The logarithm of the model-supply lower bound,
`-(2 (1 + ε)) t_p`. -/
def modelExp (P : PaperInputs) (n : ℕ) : ℝ :=
  -(2 * (1 + P.err n)) * P.t n

/-- **The `p^5` model supply.**  `PaperInputs.modelCount_lower` is exactly the
statement that the good fraction is at least `exp (-(2 (1 + ε)) t_p)`. -/
theorem goodFraction_lower (P : PaperInputs)
    (hp : ∀ n, 2 ≤ P.p n) (hS : ∀ n, 0 ≤ P.smoothOrders n) (n : ℕ) :
    Real.exp (modelExp P n) ≤ goodFraction P n := by
  have hp0 : (0 : ℝ) < P.p n := by
    have h := hp n
    linarith
  have hp5 : (0 : ℝ) < totalQuinticModels P.p n := by
    unfold totalQuinticModels
    exact Real.rpow_pos_of_pos hp0 5
  unfold goodFraction
  rw [le_div_iff₀ hp5]
  unfold totalQuinticModels goodModelCount modelExp
  calc
    Real.exp (-(2 * (1 + P.err n)) * P.t n) * P.p n ^ (5 : ℝ)
        = P.p n ^ (5 : ℝ) * Real.exp (-(2 * (1 + P.err n)) * P.t n) := by
          ring
    _ ≤ P.smoothOrders n * P.fibrePerOrder n := P.modelCount_lower hp hS n

/-! ## The CRT/odd-scalar split probability -/

/-- The CRT split probability: one model at the first prime is good with
probability `α`, and the independent model at the partner prime is *not* good
with probability `1 - β`.  A good model is killed by the odd scalar, a
non-good model survives it, so the odd scalar exposes a proper factor exactly
on this event.  The result is capped at `1` so that it is literally a
probability even when the real-valued counts are only upper bounds. -/
def splitProbability (P : PaperInputs) (partnerGood : ℕ → ℝ) (n : ℕ) : ℝ :=
  min 1 (goodFraction P n * (1 - partnerGood n))

/-- The partner-prime sparsity: at most half of the models are good, so the
non-good probability is at least `1/2`.  This is the one genuinely missing
counting input of the CRT split argument. -/
def PartnerGoodSparse (partnerGood : ℕ → ℝ) : Prop :=
  ∀ n, 0 ≤ partnerGood n ∧ partnerGood n ≤ 1 / 2

/-- **Lower bound for the CRT split probability.**  The model supply gives
`α ≥ exp ((2 (1 + ε)) t_p)^{-1}` and sparsity gives `1 - β ≥ 1/2`, hence

```
pTrial ≥ exp (-(2 (1 + ε) t_p) - log 2) .
```
-/
theorem splitProbability_lower (P : PaperInputs)
    (hp : ∀ n, 2 ≤ P.p n) (hS : ∀ n, 0 ≤ P.smoothOrders n)
    (ht : ∀ n, 0 ≤ P.t n) (he : ∀ n, -1 ≤ P.err n)
    {partnerGood : ℕ → ℝ} (hsparse : PartnerGoodSparse partnerGood) (n : ℕ) :
    Real.exp (modelExp P n - Real.log 2) ≤
      splitProbability P partnerGood n := by
  have hα := goodFraction_lower P hp hS n
  have hα0 : (0 : ℝ) ≤ goodFraction P n := (Real.exp_pos _).le.trans hα
  have hβ := hsparse n
  have hnonneg : (0 : ℝ) ≤ 1 - partnerGood n := by linarith [hβ.2]
  have hhalf : (1 / 2 : ℝ) ≤ 1 - partnerGood n := by linarith [hβ.2]
  have hprod : Real.exp (modelExp P n) * (1 / 2) ≤
      goodFraction P n * (1 - partnerGood n) :=
    mul_le_mul hα hhalf (by norm_num) hα0
  have hhalfEq : Real.exp (modelExp P n) * (1 / 2) =
      Real.exp (modelExp P n - Real.log 2) := by
    rw [show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by
      rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]]
    rw [← Real.exp_add]
    congr 1
  have hlower : Real.exp (modelExp P n - Real.log 2) ≤
      goodFraction P n * (1 - partnerGood n) := hhalfEq ▸ hprod
  have hmexp : modelExp P n ≤ 0 := by
    have he1 : (0 : ℝ) ≤ 2 * (1 + P.err n) := by
      have := he n
      nlinarith
    have hprod' : (0 : ℝ) ≤ 2 * (1 + P.err n) * P.t n :=
      mul_nonneg he1 (ht n)
    unfold modelExp
    nlinarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hy1 : Real.exp (modelExp P n - Real.log 2) ≤ 1 := by
    calc
      Real.exp (modelExp P n - Real.log 2) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  unfold splitProbability
  exact le_min hy1 hlower

/-! ## The reduction to the useful-prime split bound -/

/-- **`UsefulPrimeSplitBound` from the model count and CRT data.**  The only
numerical input is the inequality

```
2 (1 + ε) t_p + log 2 ≤ (201 / 200) (log 2 · k_y) ,
```

which is exactly the fixed margin `1/200` of (H.13) after the `p^5` count and
the CRT factor `1/2` have been absorbed. -/
theorem usefulPrimeSplitBound_of_modelCount (P : PaperInputs)
    (hp : ∀ n, 2 ≤ P.p n) (hS : ∀ n, 0 ≤ P.smoothOrders n)
    (ht : ∀ n, 0 ≤ P.t n) (he : ∀ n, -1 ≤ P.err n)
    {partnerGood : ℕ → ℝ} (hsparse : PartnerGoodSparse partnerGood)
    (k : ℕ → ℝ)
    (hk : ∀ n, Real.log 2 - modelExp P n ≤
      (((201 : ℝ) / 200) * (Real.log 2 * k n))) :
    UsefulPrimeSplitBound k (splitProbability P partnerGood) := by
  intro n
  have hlow := splitProbability_lower P hp hS ht he hsparse n
  have hexp : Real.exp (-(((201 : ℝ) / 200) * (Real.log 2 * k n))) ≤
      Real.exp (modelExp P n - Real.log 2) := by
    apply Real.exp_le_exp.mpr
    linarith [hk n]
  exact hexp.trans hlow

/-! ## The concrete exponent `k_y` and trial cap -/

/-- The concrete exponent obtained from the model count.  The `max 1200`
enforces the paper's asymptotic range; the second term absorbs
`2 (1 + ε) t_p + log 2` into the `201/200` exponent of (H.13). -/
def modelK (P : PaperInputs) (n : ℕ) : ℝ :=
  max 1200
    ((Real.log 2 - modelExp P n) /
      (((201 : ℝ) / 200) * Real.log 2))

/-- `k_y ≥ 1200`. -/
theorem modelK_ge_1200 (P : PaperInputs) (n : ℕ) : 1200 ≤ modelK P n :=
  le_max_left _ _

/-- **The exponent inequality defining `modelK`.** -/
theorem modelK_exponent (P : PaperInputs) (n : ℕ) :
    Real.log 2 - modelExp P n ≤
      (((201 : ℝ) / 200) * (Real.log 2 * modelK P n)) := by
  set c : ℝ := (((201 : ℝ) / 200) * Real.log 2) with hc
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcpos : (0 : ℝ) < c := by
    dsimp [c]
    positivity
  have hx : (Real.log 2 - modelExp P n) / c ≤ modelK P n :=
    le_max_right _ _
  have hmul : c * ((Real.log 2 - modelExp P n) / c) ≤
      c * modelK P n :=
    mul_le_mul_of_nonneg_left hx hcpos.le
  rw [mul_div_cancel₀ _ hcpos.ne'] at hmul
  calc
    Real.log 2 - modelExp P n ≤ c * modelK P n := hmul
    _ = (((201 : ℝ) / 200) * (Real.log 2 * modelK P n)) := by
      dsimp [c]
      ring

/-- **The useful-prime split bound for the concrete exponent.** -/
theorem usefulPrimeSplitBound_modelK (P : PaperInputs)
    (hp : ∀ n, 2 ≤ P.p n) (hS : ∀ n, 0 ≤ P.smoothOrders n)
    (ht : ∀ n, 0 ≤ P.t n) (he : ∀ n, -1 ≤ P.err n)
    {partnerGood : ℕ → ℝ} (hsparse : PartnerGoodSparse partnerGood) :
    UsefulPrimeSplitBound (modelK P) (splitProbability P partnerGood) :=
  usefulPrimeSplitBound_of_modelCount P hp hS ht he hsparse (modelK P)
    (modelK_exponent P)

/-- The concrete trial cap `R_curve = max 1 ⌈exp ((101/100) (log 2 · k_y)) L_c⌉`. -/
def modelRcurve (k : ℕ → ℝ) (Lc : ℕ → ℝ) (n : ℕ) : ℕ :=
  max 1 ⌈Real.exp ((((101 : ℝ) / 100) * (Real.log 2 * k n))) * Lc n⌉₊

/-- **The trial cap, by construction.** -/
theorem curveTrialCap_modelRcurve (k : ℕ → ℝ) (Lc : ℕ → ℝ) :
    CurveTrialCap k Lc (modelRcurve k Lc) := by
  intro n
  unfold modelRcurve
  have hx : Real.exp ((((101 : ℝ) / 100) * (Real.log 2 * k n))) * Lc n ≤
      ((⌈Real.exp ((((101 : ℝ) / 100) * (Real.log 2 * k n))) * Lc n⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hle : ((⌈Real.exp ((((101 : ℝ) / 100) * (Real.log 2 * k n))) * Lc n⌉₊ : ℕ) : ℝ) ≤
      ((max 1 ⌈Real.exp ((((101 : ℝ) / 100) * (Real.log 2 * k n))) * Lc n⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast le_max_right (1 : ℕ)
      ⌈Real.exp ((((101 : ℝ) / 100) * (Real.log 2 * k n))) * Lc n⌉₊
  exact hx.trans hle

/-! ## Positivity and the `ClusterBudget` package -/

/-- The CRT split probability is strictly positive. -/
theorem splitProbability_pos (P : PaperInputs)
    (hp : ∀ n, 2 ≤ P.p n) (hS : ∀ n, 0 ≤ P.smoothOrders n)
    (ht : ∀ n, 0 ≤ P.t n) (he : ∀ n, -1 ≤ P.err n)
    {partnerGood : ℕ → ℝ} (hsparse : PartnerGoodSparse partnerGood) (n : ℕ) :
    0 < splitProbability P partnerGood n :=
  (Real.exp_pos _).trans_le
    (splitProbability_lower P hp hS ht he hsparse n)

/-- The CRT split probability is at most one, because it is capped at `1`. -/
theorem splitProbability_le_one (P : PaperInputs)
    {partnerGood : ℕ → ℝ} (n : ℕ) :
    splitProbability P partnerGood n ≤ 1 := by
  unfold splitProbability
  exact min_le_left _ _

/-- **The cluster budget.**  This bundles exactly the data that the L30 failure
analysis consumes: the paper's `k_y ≥ 1200`, the useful-prime split bound, the
trial cap, positivity and `pTrial ≤ 1`, and the derived budget
`64 L_c ≤ pTrial · R_curve`.  The latter is the arithmetic of
`FailureData.curve_trial_budget`. -/
structure ClusterBudget (k pTrial Lc : ℕ → ℝ) (Rcurve : ℕ → ℕ) : Prop where
  /-- The asymptotic range `k_y ≥ 1200`. -/
  k_large : ∀ n, 1200 ≤ k n
  /-- KB (H.13)–(H.14), the useful-prime split bound. -/
  split : UsefulPrimeSplitBound k pTrial
  /-- KB (H.14), the trial cap. -/
  cap : CurveTrialCap k Lc Rcurve
  /-- The confidence parameter is nonnegative. -/
  Lc_nonneg : ∀ n, 0 ≤ Lc n
  /-- The split probability is positive. -/
  trial_pos : ∀ n, 0 < pTrial n
  /-- The split probability is at most one. -/
  trial_le_one : ∀ n, pTrial n ≤ 1
  /-- The derived `64 L_c` trial budget. -/
  budget : ∀ n, 64 * Lc n ≤ pTrial n * (Rcurve n : ℝ)

/-- **The concrete cluster budget.**  The exponent is `modelK`, the split
probability is the CRT probability, and the trial cap is the literal cap.  The
`64 L_c` budget is proved by `curve_trial_budget_core`, whose only inputs are
`k_y ≥ 1200`, `L_c ≥ 0`, the split bound, and the cap. -/
theorem clusterBudget_model (P : PaperInputs)
    (hp : ∀ n, 2 ≤ P.p n) (hS : ∀ n, 0 ≤ P.smoothOrders n)
    (ht : ∀ n, 0 ≤ P.t n) (he : ∀ n, -1 ≤ P.err n)
    {partnerGood : ℕ → ℝ} (hsparse : PartnerGoodSparse partnerGood)
    (Lc : ℕ → ℝ) (hLc : ∀ n, 0 ≤ Lc n) :
    ClusterBudget (modelK P) (splitProbability P partnerGood) Lc
      (modelRcurve (modelK P) Lc) where
  k_large := modelK_ge_1200 P
  split := usefulPrimeSplitBound_modelK P hp hS ht he hsparse
  cap := curveTrialCap_modelRcurve (modelK P) Lc
  Lc_nonneg := hLc
  trial_pos := splitProbability_pos P hp hS ht he hsparse
  trial_le_one := fun n => splitProbability_le_one P n
  budget := by
    intro n
    exact curve_trial_budget_core (modelK_ge_1200 P n) (hLc n)
      (usefulPrimeSplitBound_modelK P hp hS ht he hsparse n)
      (curveTrialCap_modelRcurve (modelK P) Lc n)

/-- `ClusterBudget` gives the exact inequality used by
`FailureData.curve_trial_budget`. -/
theorem ClusterBudget.curve_trial_budget {k pTrial Lc : ℕ → ℝ}
    {Rcurve : ℕ → ℕ} (B : ClusterBudget k pTrial Lc Rcurve) (n : ℕ) :
    64 * Lc n ≤ pTrial n * (Rcurve n : ℝ) :=
  B.budget n

/-- **Compatibility with `FailureData`.**  The derived `ClusterBudget` supplies
the two formerly abstract fields `useful_prime_split` and `curve_trial_cap`,
and the remaining `FailureData` fields are carried through unchanged.  This
shows that the split bound proved in this file can replace the corresponding
hypothesis in `RandomizedL30Sub`. -/
noncomputable def failureDataOfClusterBudget {k pTrial Lc : ℕ → ℝ}
    {Rcurve : ℕ → ℕ} (B : ClusterBudget k pTrial Lc Rcurve)
    (Lc_ge_one : ∀ n, 1 ≤ Lc n)
    (confidence_dominates : ∀ B₀ : ℝ, 0 < B₀ →
      ∀ᶠ n : ℕ in atTop,
        B₀ * scale n + Real.log (2 * (n : ℝ)) ≤ 64 * Lc n)
    (nodes : ℕ → ℕ) (nodes_pos : ∀ n, 1 ≤ n → 0 < nodes n)
    (factor_tree_nodes : FactorTreeNodes nodes)
    (failure : ℕ → ℝ) (failure_pos : ∀ n, 0 < failure n)
    (failure_union : FailureUnionBound pTrial Rcurve nodes failure) :
    FailureData where
  k := k
  k_nonneg := fun n => (by linarith [B.k_large n] : (0 : ℝ) ≤ k n)
  k_large := B.k_large
  Lc := Lc
  Lc_ge_one := Lc_ge_one
  confidence_dominates := confidence_dominates
  pTrial := pTrial
  pTrial_nonneg := fun n => (B.trial_pos n).le
  pTrial_le_one := B.trial_le_one
  useful_prime_split := B.split
  Rcurve := Rcurve
  curve_trial_cap := B.cap
  nodes := nodes
  nodes_pos := nodes_pos
  factor_tree_nodes := factor_tree_nodes
  failure := failure
  failure_pos := failure_pos
  failure_union := failure_union

/-- The failure data constructed from a cluster budget still has the paper's
`2 n exp (-64 L_c)` bound, through the existing `FailureData` theorem. -/
theorem failureDataOfClusterBudget_failure_le_two_n_exp {k pTrial Lc : ℕ → ℝ}
    {Rcurve : ℕ → ℕ} (B : ClusterBudget k pTrial Lc Rcurve)
    (Lc_ge_one : ∀ n, 1 ≤ Lc n)
    (confidence_dominates : ∀ B₀ : ℝ, 0 < B₀ →
      ∀ᶠ n : ℕ in atTop,
        B₀ * scale n + Real.log (2 * (n : ℝ)) ≤ 64 * Lc n)
    (nodes : ℕ → ℕ) (nodes_pos : ∀ n, 1 ≤ n → 0 < nodes n)
    (factor_tree_nodes : FactorTreeNodes nodes)
    (failure : ℕ → ℝ) (failure_pos : ∀ n, 0 < failure n)
    (failure_union : FailureUnionBound pTrial Rcurve nodes failure)
    (n : ℕ) (hn : 1 ≤ n) :
    (failureDataOfClusterBudget B Lc_ge_one confidence_dominates nodes nodes_pos
      factor_tree_nodes failure failure_pos failure_union).failure n ≤
      2 * (n : ℝ) * Real.exp (-(64 * Lc n)) :=
  FailureData.failure_le_two_n_exp _ n hn

/-! ## A concrete numerical instance -/

/-- A fully explicit instance of the counting input at `p = 4`: the coefficient
space has `4^5 = 1024` models, and the good count is `1`.  The partner good
fraction is `0`, so the CRT split probability is `1/1024`, which is positive
and at most one. -/
def concreteP : ℕ → ℝ := fun _ => 4

/-- The concrete good count `1` at every scale. -/
def concreteGood : ℕ → ℝ := fun _ => 1

/-- The concrete total model count `4^5 = 1024`. -/
def concreteTotal : ℕ → ℝ := fun _ => (4 : ℝ) ^ 5

/-- The concrete partner good fraction `0`. -/
def concretePartnerGood : ℕ → ℝ := fun _ => 0

/-- The concrete split probability `1/1024`. -/
def concreteSplit : ℕ → ℝ := fun _ => 1 / 1024

/-- The concrete counting data satisfy `#good ≤ p^5`. -/
theorem concrete_good_le_total :
    ∀ n, concreteGood n ≤ concreteTotal n := by
  intro n
  unfold concreteGood concreteTotal
  norm_num

/-- The concrete partner fraction is sparse. -/
theorem concrete_partner_sparse : PartnerGoodSparse concretePartnerGood := by
  intro n
  unfold concretePartnerGood
  norm_num

/-- The concrete split probability is the CRT product `(1/1024) (1 - 0)`. -/
theorem concrete_split_eq (n : ℕ) :
    (concreteGood n / concreteTotal n) * (1 - concretePartnerGood n) =
      concreteSplit n := by
  unfold concreteGood concreteTotal concretePartnerGood concreteSplit
  norm_num

/-- The concrete exponent `k = 1200`, the smallest value in the paper's range. -/
def concreteK : ℕ → ℝ := fun _ => 1200

/-- The concrete useful-prime split bound holds at `k = 1200` and split
probability `1/1024`. -/
theorem concrete_useful : UsefulPrimeSplitBound concreteK concreteSplit := by
  intro n
  unfold concreteK concreteSplit
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1024 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  have hbig : Real.log 1024 ≤ ((201 : ℝ) / 200) * (Real.log 2 * 1200) := by
    rw [h1024]
    nlinarith
  have hneg : -(((201 : ℝ) / 200) * (Real.log 2 * 1200)) ≤
      -Real.log 1024 := by
    linarith
  calc
    Real.exp (-(((201 : ℝ) / 200) * (Real.log 2 * 1200)))
        ≤ Real.exp (-Real.log 1024) := Real.exp_le_exp.mpr hneg
    _ = 1 / 1024 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]

/-- The concrete confidence parameter `L_c = 1`. -/
def concreteLc : ℕ → ℝ := fun _ => 1

/-- The concrete trial cap. -/
def concreteRcurve : ℕ → ℕ := modelRcurve concreteK concreteLc

/-- The concrete trial cap satisfies `CurveTrialCap`. -/
theorem concrete_curveTrialCap :
    CurveTrialCap concreteK concreteLc concreteRcurve :=
  curveTrialCap_modelRcurve concreteK concreteLc

/-- The concrete `64 L_c` budget. -/
theorem concrete_budget (n : ℕ) :
    64 * concreteLc n ≤ concreteSplit n * (concreteRcurve n : ℝ) := by
  have h := curve_trial_budget_core (k := (1200 : ℝ)) (Lc := (1 : ℝ))
    (p := (1 / 1024 : ℝ)) (R := (concreteRcurve n : ℝ))
    (by norm_num) (by norm_num) (concrete_useful n) (concrete_curveTrialCap n)
  simpa [concreteLc, concreteSplit] using h

/-- **`ClusterBudget` is inhabited with explicit positive constants.** -/
theorem concrete_clusterBudget :
    ClusterBudget concreteK concreteSplit concreteLc concreteRcurve where
  k_large := by intro n; unfold concreteK; norm_num
  split := concrete_useful
  cap := concrete_curveTrialCap
  Lc_nonneg := by intro n; unfold concreteLc; norm_num
  trial_pos := by intro n; unfold concreteSplit; norm_num
  trial_le_one := by intro n; unfold concreteSplit; norm_num
  budget := concrete_budget

/-! ## Axiom audit -/

#print axioms goodFraction_lower
#print axioms splitProbability_lower
#print axioms usefulPrimeSplitBound_of_modelCount
#print axioms modelK_exponent
#print axioms usefulPrimeSplitBound_modelK
#print axioms curveTrialCap_modelRcurve
#print axioms splitProbability_pos
#print axioms splitProbability_le_one
#print axioms clusterBudget_model
#print axioms ClusterBudget.curve_trial_budget
#print axioms failureDataOfClusterBudget
#print axioms failureDataOfClusterBudget_failure_le_two_n_exp
#print axioms concrete_useful
#print axioms concrete_clusterBudget

end

end Cogentic.RandomizedL30SplitBound
