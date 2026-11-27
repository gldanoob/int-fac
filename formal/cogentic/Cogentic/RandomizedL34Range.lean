import Cogentic.RandomizedL34ZeroFree
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# L34: the `x = 2^(T^6)` range condition from explicit parameter bounds

`Cogentic.RandomizedL34ZeroFree` reduced the paper's Chebotarev range input to
the arithmetic budget

* `ChebotarevRangeT6 K T degree discLog` — `K d (log |Δ_E|)^2 ≤ (log 2) T^6`,
* `ChebotarevExponentBudget K (T^6) degree discLog` — the same inequality with
  the division by `log 2`,

and proved that either is equivalent to the range threshold for the paper's
cutoff `x = 2^(T^6)`.

This file performs the remaining exponent arithmetic.  The paper chooses the
polynomial parameter `T` so that it bounds both the absolute degree `d` and the
logarithm of the absolute discriminant:

`d ≤ T`, `log |Δ_E| ≤ T`.

Consequently

`d (log |Δ_E|)^2 ≤ T * T^2 = T^3`,

so the `T^6` budget is implied by the single scalar inequality

`K ≤ (log 2) T^3`.

That inequality is the *smallest* explicit exponent arithmetic left: the
original budget has the right-hand side `(log 2) T^6` and the two-variable
product `d (log |Δ_E|)^2`; after using the two paper bounds it is exactly
`K T^3 ≤ (log 2) T^6`, whose cancellation of the positive factor `T^3` is the
stated linear comparison between `K` and `(log 2) T^3`.

The main results are

* `chebotarevRangeT6_of_degree_le_T_of_discLog_le_T` — the arithmetic
  reduction;
* `ChebotarevT6RangeInput.toChebotarevRangeT6`,
  `…toChebotarevExponentBudget`, `…toChebotarevRangeThreshold` and
  `…toChebotarevRangeInput` — the packaged input and all the equivalent forms;
* `chebotarevRangeT6_of_le_one_of_two_le` — the concrete paper case
  `K ≤ 1`, `T ≥ 2`, where `K ≤ (log 2) T^3` follows from
  `Real.log_two_gt_d9`.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  No loss, count, or
error is set to zero.
-/

namespace Cogentic.RandomizedL34Range

open Filter Real
open Cogentic.RandomizedL34
open Cogentic.RandomizedL34Sub
open Cogentic.RandomizedL34Analytic
open Cogentic.RandomizedL34Dedekind
open Cogentic.RandomizedL34ZeroFree

noncomputable section

/-! ## 1. The exact `T^6` equivalences -/

/-- **The `x = 2^(T^6)` threshold is exactly the `T^6` arithmetic budget.**
This is the `T^6` instance of `chebotarevRangeThreshold_T6_of_T6` and
`chebotarevRangeT6_of_threshold`. -/
theorem chebotarevRangeThreshold_T6_iff_T6
    {K : ℝ} {T degree discLog : ℕ → ℝ} :
    ChebotarevRangeThreshold K (fun n => (2 : ℝ) ^ ((T n) ^ 6)) degree discLog ↔
      ChebotarevRangeT6 K T degree discLog :=
  ⟨chebotarevRangeT6_of_threshold, chebotarevRangeThreshold_T6_of_T6⟩

/-- **The `T^6` exponent budget is exactly the `T^6` arithmetic budget.**
The only difference is the position of the positive factor `log 2`. -/
theorem chebotarevExponentBudget_T6_iff_T6
    {K : ℝ} {T degree discLog : ℕ → ℝ} :
    ChebotarevExponentBudget K (fun n => (T n) ^ 6) degree discLog ↔
      ChebotarevRangeT6 K T degree discLog := by
  constructor
  · intro h
    have hcond : ChebotarevExponentCondition K (fun n => (T n) ^ 6) degree discLog :=
      chebotarevExponentCondition_iff_budget.mpr h
    intro n
    exact hcond n
  · intro h
    refine chebotarevExponentCondition_iff_budget.mp ?_
    intro n
    exact h n

/-- **The threshold and the exponent budget are exactly equivalent at
`x = 2^(T^6)`.**  This is the `S = T^6` instance of
`chebotarevRangeThreshold_rpow_two_iff_budget`. -/
theorem chebotarevRangeThreshold_T6_iff_budget
    {K : ℝ} {T degree discLog : ℕ → ℝ} :
    ChebotarevRangeThreshold K (fun n => (2 : ℝ) ^ ((T n) ^ 6)) degree discLog ↔
      ChebotarevExponentBudget K (fun n => (T n) ^ 6) degree discLog :=
  chebotarevRangeThreshold_rpow_two_iff_budget

/-- The cutoff `2^(T^6)` is positive. -/
theorem rpow_two_T6_pos (T : ℕ → ℝ) (n : ℕ) :
    0 < (2 : ℝ) ^ ((T n) ^ 6) :=
  Real.rpow_pos_of_pos (by norm_num) _

/-! ## 2. The exponent arithmetic `d (log |Δ_E|)^2 ≤ T^3` -/

/-- **The `T^6` budget follows from the paper's parameter bounds.**  If
`0 ≤ d ≤ T` and `0 ≤ log |Δ_E| ≤ T`, then `d (log |Δ_E|)^2 ≤ T^3`.  Together
with `K ≤ (log 2) T^3` and `K ≥ 0` this gives
`K d (log |Δ_E|)^2 ≤ (log 2) T^6`, i.e. `ChebotarevRangeT6`. -/
theorem chebotarevRangeT6_of_degree_le_T_of_discLog_le_T
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (hK : 0 ≤ K)
    (hdeg0 : ∀ n, 0 ≤ degree n)
    (hD0 : ∀ n, 0 ≤ discLog n)
    (hdegT : ∀ n, degree n ≤ T n)
    (hDT : ∀ n, discLog n ≤ T n)
    (hconst : ∀ n, K ≤ Real.log 2 * (T n) ^ 3) :
    ChebotarevRangeT6 K T degree discLog := by
  intro n
  have hT0 : 0 ≤ T n := le_trans (hdeg0 n) (hdegT n)
  have hsq : (discLog n) ^ 2 ≤ (T n) ^ 2 :=
    pow_le_pow_left₀ (hD0 n) (hDT n) 2
  have hprod : degree n * (discLog n) ^ 2 ≤ T n * (T n) ^ 2 :=
    mul_le_mul (hdegT n) hsq (sq_nonneg _) hT0
  have hprod3 : degree n * (discLog n) ^ 2 ≤ (T n) ^ 3 := by
    calc
      degree n * (discLog n) ^ 2 ≤ T n * (T n) ^ 2 := hprod
      _ = (T n) ^ 3 := by ring
  have hmul : K * (degree n * (discLog n) ^ 2) ≤ K * (T n) ^ 3 :=
    mul_le_mul_of_nonneg_left hprod3 hK
  have hconst' : K * (T n) ^ 3 ≤
      (Real.log 2 * (T n) ^ 3) * (T n) ^ 3 :=
    mul_le_mul_of_nonneg_right (hconst n) (pow_nonneg hT0 3)
  calc
    K * degree n * (discLog n) ^ 2
        = K * (degree n * (discLog n) ^ 2) := by ring
    _ ≤ K * (T n) ^ 3 := hmul
    _ ≤ (Real.log 2 * (T n) ^ 3) * (T n) ^ 3 := hconst'
    _ = Real.log 2 * (T n) ^ 6 := by ring

/-- The same arithmetic reduction in the division-free exponent-budget form
`K d (log |Δ_E|)^2 / log 2 ≤ T^6`. -/
theorem chebotarevExponentBudget_T6_of_degree_le_T_of_discLog_le_T
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (hK : 0 ≤ K)
    (hdeg0 : ∀ n, 0 ≤ degree n)
    (hD0 : ∀ n, 0 ≤ discLog n)
    (hdegT : ∀ n, degree n ≤ T n)
    (hDT : ∀ n, discLog n ≤ T n)
    (hconst : ∀ n, K ≤ Real.log 2 * (T n) ^ 3) :
    ChebotarevExponentBudget K (fun n => (T n) ^ 6) degree discLog :=
  chebotarevExponentBudget_T6_iff_T6.mpr
    (chebotarevRangeT6_of_degree_le_T_of_discLog_le_T hK hdeg0 hD0 hdegT hDT
      hconst)

/-- The same arithmetic reduction in threshold form for `x = 2^(T^6)`. -/
theorem chebotarevRangeThreshold_T6_of_degree_le_T_of_discLog_le_T
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (hK : 0 ≤ K)
    (hdeg0 : ∀ n, 0 ≤ degree n)
    (hD0 : ∀ n, 0 ≤ discLog n)
    (hdegT : ∀ n, degree n ≤ T n)
    (hDT : ∀ n, discLog n ≤ T n)
    (hconst : ∀ n, K ≤ Real.log 2 * (T n) ^ 3) :
    ChebotarevRangeThreshold K (fun n => (2 : ℝ) ^ ((T n) ^ 6)) degree discLog :=
  chebotarevRangeThreshold_T6_of_T6
    (chebotarevRangeT6_of_degree_le_T_of_discLog_le_T hK hdeg0 hD0 hdegT hDT
      hconst)

/-! ## 3. The concrete case `K ≤ 1`, `T ≥ 2` -/

/-- **The explicit scalar comparison `K ≤ (log 2) T^3` for `K ≤ 1` and
`T ≥ 2`.**  The lower bound `log 2 > 0.693` gives `(log 2) 2^3 > 1`. -/
theorem constant_le_of_le_one_of_two_le {K T : ℝ} (hK : K ≤ 1) (hT : 2 ≤ T) :
    K ≤ Real.log 2 * T ^ 3 := by
  have hlog2 : (1 : ℝ) ≤ Real.log 2 * (2 : ℝ) ^ 3 := by
    have h := Real.log_two_gt_d9
    have h8 : (2 : ℝ) ^ 3 = 8 := by norm_num
    rw [h8]
    nlinarith
  have hcube : (2 : ℝ) ^ 3 ≤ T ^ 3 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT 3
  have hlogpos : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hmono : Real.log 2 * (2 : ℝ) ^ 3 ≤ Real.log 2 * T ^ 3 :=
    mul_le_mul_of_nonneg_left hcube hlogpos
  linarith

/-- **The paper case `K ≤ 1`, `T ≥ 2`.**  Under the paper's parameter bounds
`d ≤ T` and `log |Δ_E| ≤ T`, the `T^6` arithmetic budget holds whenever the
range constant is at most `1`. -/
theorem chebotarevRangeT6_of_le_one_of_two_le
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (hK0 : 0 ≤ K) (hK1 : K ≤ 1)
    (hdeg0 : ∀ n, 0 ≤ degree n)
    (hD0 : ∀ n, 0 ≤ discLog n)
    (hdegT : ∀ n, degree n ≤ T n)
    (hDT : ∀ n, discLog n ≤ T n)
    (hT : ∀ n, 2 ≤ T n) :
    ChebotarevRangeT6 K T degree discLog :=
  chebotarevRangeT6_of_degree_le_T_of_discLog_le_T hK0 hdeg0 hD0 hdegT hDT
    (fun n => constant_le_of_le_one_of_two_le hK1 (hT n))

/-! ## 4. The packaged input -/

/-- **The explicit `T^6` range input.**  It records exactly the paper's
parameter choices: positive `K`, positive degree and discriminant logarithm, the
two bounds `d ≤ T`, `log |Δ_E| ≤ T`, and the scalar exponent comparison
`K ≤ (log 2) T^3`. -/
structure ChebotarevT6RangeInput (K : ℝ) (T degree discLog : ℕ → ℝ) : Prop where
  /-- The range constant is positive. -/
  K_pos : 0 < K
  /-- The absolute degree is positive. -/
  degree_pos : ∀ n, 0 < degree n
  /-- `log |Δ_E|` is positive. -/
  discLog_pos : ∀ n, 0 < discLog n
  /-- The polynomial parameter bounds the absolute degree. -/
  degree_le_T : ∀ n, degree n ≤ T n
  /-- The polynomial parameter bounds `log |Δ_E|`. -/
  discLog_le_T : ∀ n, discLog n ≤ T n
  /-- The smallest scalar exponent comparison. -/
  constant_le : ∀ n, K ≤ Real.log 2 * (T n) ^ 3

namespace ChebotarevT6RangeInput

/-- The packaged input gives the `T^6` arithmetic budget. -/
theorem toChebotarevRangeT6
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (A : ChebotarevT6RangeInput K T degree discLog) :
    ChebotarevRangeT6 K T degree discLog :=
  chebotarevRangeT6_of_degree_le_T_of_discLog_le_T A.K_pos.le
    (fun n => (A.degree_pos n).le) (fun n => (A.discLog_pos n).le)
    A.degree_le_T A.discLog_le_T A.constant_le

/-- The packaged input gives the exponent budget in `T^6` form. -/
theorem toChebotarevExponentBudget
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (A : ChebotarevT6RangeInput K T degree discLog) :
    ChebotarevExponentBudget K (fun n => (T n) ^ 6) degree discLog :=
  chebotarevExponentBudget_T6_iff_T6.mpr A.toChebotarevRangeT6

/-- The packaged input gives the range threshold for `x = 2^(T^6)`. -/
theorem toChebotarevRangeThreshold
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (A : ChebotarevT6RangeInput K T degree discLog) :
    ChebotarevRangeThreshold K (fun n => (2 : ℝ) ^ ((T n) ^ 6)) degree discLog :=
  chebotarevRangeThreshold_T6_of_T6 A.toChebotarevRangeT6

/-- The packaged input gives the logarithmic range inequality for
`x = 2^(T^6)`. -/
theorem toChebotarevRangeInequality
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (A : ChebotarevT6RangeInput K T degree discLog) :
    ChebotarevRangeInequality K (fun n => (2 : ℝ) ^ ((T n) ^ 6)) degree discLog :=
  chebotarevRangeInequality_rpow_two
    (chebotarevExponentCondition_iff_budget.mpr A.toChebotarevExponentBudget)

/-- The packaged input gives the smallest `ChebotarevRangeInput`. -/
theorem toChebotarevRangeInput
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (A : ChebotarevT6RangeInput K T degree discLog) :
    ChebotarevRangeInput K (fun n => (2 : ℝ) ^ ((T n) ^ 6)) degree discLog where
  K_pos := A.K_pos
  range := A.toChebotarevRangeInequality

/-- The packaged input gives the paper-level `EffectiveChebotarevRange`. -/
theorem toEffectiveChebotarevRange
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (A : ChebotarevT6RangeInput K T degree discLog) :
    EffectiveChebotarevRange K (fun n => (2 : ℝ) ^ ((T n) ^ 6)) degree discLog :=
  A.toChebotarevRangeInput.toEffectiveChebotarevRange

end ChebotarevT6RangeInput

/-- **The concrete packaged paper case.**  `K ≤ 1`, `T ≥ 2`, and the two
parameter bounds give the full `T^6` range input. -/
theorem chebotarevT6RangeInput_of_le_one_of_two_le
    {K : ℝ} {T degree discLog : ℕ → ℝ}
    (hK0 : 0 < K) (hK1 : K ≤ 1)
    (hdeg : ∀ n, 0 < degree n)
    (hD : ∀ n, 0 < discLog n)
    (hdegT : ∀ n, degree n ≤ T n)
    (hDT : ∀ n, discLog n ≤ T n)
    (hT : ∀ n, 2 ≤ T n) :
    ChebotarevT6RangeInput K T degree discLog where
  K_pos := hK0
  degree_pos := hdeg
  discLog_pos := hD
  degree_le_T := hdegT
  discLog_le_T := hDT
  constant_le := fun n => constant_le_of_le_one_of_two_le hK1 (hT n)

/-! ## Axiom audit -/

#print axioms chebotarevRangeThreshold_T6_iff_T6
#print axioms chebotarevExponentBudget_T6_iff_T6
#print axioms chebotarevRangeThreshold_T6_iff_budget
#print axioms rpow_two_T6_pos
#print axioms chebotarevRangeT6_of_degree_le_T_of_discLog_le_T
#print axioms chebotarevExponentBudget_T6_of_degree_le_T_of_discLog_le_T
#print axioms chebotarevRangeThreshold_T6_of_degree_le_T_of_discLog_le_T
#print axioms constant_le_of_le_one_of_two_le
#print axioms chebotarevRangeT6_of_le_one_of_two_le
#print axioms ChebotarevT6RangeInput.toChebotarevRangeT6
#print axioms ChebotarevT6RangeInput.toChebotarevExponentBudget
#print axioms ChebotarevT6RangeInput.toChebotarevRangeThreshold
#print axioms ChebotarevT6RangeInput.toChebotarevRangeInequality
#print axioms ChebotarevT6RangeInput.toChebotarevRangeInput
#print axioms ChebotarevT6RangeInput.toEffectiveChebotarevRange
#print axioms chebotarevT6RangeInput_of_le_one_of_two_le

end

end Cogentic.RandomizedL34Range
