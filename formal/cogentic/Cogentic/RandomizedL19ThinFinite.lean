import Cogentic.RandomizedL19Thin

/-!
# L19.6: the sharp thin-pair route without an initial-segment hypothesis

`Cogentic.RandomizedL19Thin.LatticePaperThinInputs` carries the sharp
small-determinant exponents `η = min ζ (min 1 c₀)` and `c = cMax + log 3`, but
retains one bookkeeping field

`smallDet_prefix : ∀ n, scale n < 1 → smallDet n ≤ exp (paper.c * scale n) * exp (-paper.eta * W n)`.

That field is only needed because the three-term union bound costs a factor `3`,
and `3 ≤ exp (log 3 · scale n)` is used only when `scale n ≥ 1`.

This file removes the field.  The factor `3` is absorbed on the *finite* initial
segment by enlarging the polynomial exponent `c`.  Concretely, with

`S = {n < scaleThreshold | 3 ≤ n ∧ scale n < 1}`

(an explicit `Finset`; `scaleThreshold` is a threshold beyond which
`1 ≤ scale n`), set

`C = max paper.c (paper.cMax + ∑ n ∈ S, log 3 / scale n)`.

For `n ∈ S` we have `scale n > 0` and the finite check

`3 · exp (paper.cMax · scale n) ≤ exp (C · scale n)`,

which is discharged by the single-term bound for the finite sum defining `C`.
For `n ∉ S` with `n ≥ 3`, either `scale n ≥ 1` and the paper's three-term
estimate applies directly, or the same finite absorption applies.  The indices
`n = 0, 1, 2` never enter the asymptotic statement (`scale 2 < 0`, and
`scale 0 = scale 1 = 0`); the loss is still `thin + smallDet` and is not set to
zero.

The resulting structure `LatticePaperThinFiniteInputs` is the sharp
`LatticePaperThinInputs` with `smallDet_prefix` deleted, and yields
`SubexpLoss`, `SubexpLeaf` and the C5 `B = 2` slot.

For the *literal* pointwise form of `smallDet_prefix`, increasing `c` cannot
help at `n = 0, 1, 2` because there `scale n ≤ 0`.  Section 7 therefore also
proves that pointwise form from the explicit three-element check on
`Finset.range 3`, via `smallDet_prefix_of_finite_range` and
`LatticePaperThinFinitePointwiseInputs`.  The L19.6 leaf itself uses the
no-check eventual structure.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

namespace Cogentic.RandomizedL19ThinFinite

open Filter Real
open scoped BigOperators
open Cogentic.RandomizedPaperLeafStatements
open Cogentic.RandomizedOneThirdAsymptotic
open Cogentic.RandomizedL19SecondMoment
open Cogentic.RandomizedL19Thin

/-! ## 1. Positivity of the ledger scale above the small-index region -/

/-- `scale n` is positive for `n ≥ 3`.  For `n = 2` the real-power convention
makes `scale 2 < 0`; the asymptotic argument below starts at `3`, where both
`log n` and `log log n` are positive. -/
theorem scale_pos_of_three_le {n : ℕ} (hn : 3 ≤ n) : 0 < scale n := by
  have h3log : (1 : ℝ) < Real.log 3 := by
    have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    simpa using h
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog_gt_one : (1 : ℝ) < Real.log (n : ℝ) :=
    lt_of_lt_of_le h3log (Real.log_le_log (by norm_num) hnR)
  have hlog_pos : 0 < Real.log (n : ℝ) := lt_trans zero_lt_one hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hlog_gt_one
  unfold scale
  exact mul_pos (Real.rpow_pos_of_pos hlog_pos _)
    (Real.rpow_pos_of_pos hloglog_pos _)

/-- `scale n` is nonnegative for `n ≥ 3`. -/
theorem scale_nonneg_of_three_le {n : ℕ} (hn : 3 ≤ n) : 0 ≤ scale n :=
  (scale_pos_of_three_le hn).le

/-! ## 2. An explicit finite initial segment -/

/-- A threshold beyond which the ledger scale is at least `1`. -/
private theorem exists_scale_one_threshold :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (1 : ℝ) ≤ scale n :=
  Filter.eventually_atTop.mp (scale_grows.eventually_ge_atTop (1 : ℝ))

/-- An explicit threshold `N` with `1 ≤ scale n` for `n ≥ N`. -/
noncomputable def scaleOneThreshold : ℕ := exists_scale_one_threshold.choose

theorem one_le_scale_of_scaleOneThreshold_le {n : ℕ}
    (hn : scaleOneThreshold ≤ n) : (1 : ℝ) ≤ scale n :=
  exists_scale_one_threshold.choose_spec n hn

/-- The threshold used below.  It is at least `3`, so every index in the finite
initial segment is in the region where `scale` is positive. -/
noncomputable def scaleThreshold : ℕ := max 3 scaleOneThreshold

theorem one_le_scale_of_scaleThreshold_le {n : ℕ}
    (hn : scaleThreshold ≤ n) : (1 : ℝ) ≤ scale n :=
  one_le_scale_of_scaleOneThreshold_le
    (le_trans (le_max_right 3 scaleOneThreshold) hn)

/-- The explicit finite set of indices in the initial segment at which the
factor `3` still has to be absorbed: `3 ≤ n < scaleThreshold` and
`scale n < 1`. -/
noncomputable def smallDetPrefixSlice : Finset ℕ := by
  classical
  exact (Finset.range scaleThreshold).filter (fun n => 3 ≤ n ∧ scale n < 1)

theorem mem_smallDetPrefixSlice {n : ℕ} :
    n ∈ smallDetPrefixSlice ↔ n < scaleThreshold ∧ 3 ≤ n ∧ scale n < 1 := by
  classical
  simp only [smallDetPrefixSlice, Finset.mem_filter, Finset.mem_range]

/-! ## 3. The adjusted polynomial constant -/

/-- The polynomial exponent obtained by charging the finite union-bound factor
`3` to the initial segment.  The sum is finite and explicit. -/
noncomputable def adjustedC {W smallDet : ℕ → ℝ}
    (P : SmallDetPaperInputs W smallDet) : ℝ :=
  max P.c (P.cMax + ∑ n ∈ smallDetPrefixSlice, Real.log 3 / scale n)

theorem c_le_adjustedC {W smallDet : ℕ → ℝ}
    (P : SmallDetPaperInputs W smallDet) : P.c ≤ adjustedC P := by
  unfold adjustedC
  exact le_max_left _ _

/-- For an index of the finite initial segment, the sum over the segment is at
least the single term `log 3 / scale n`. -/
theorem cMax_add_div_le_adjustedC {W smallDet : ℕ → ℝ}
    (P : SmallDetPaperInputs W smallDet) {n : ℕ}
    (hn : n ∈ smallDetPrefixSlice) :
    P.cMax + Real.log 3 / scale n ≤ adjustedC P := by
  unfold adjustedC
  refine le_trans ?_ (le_max_right _ _)
  have hterm_nonneg : ∀ m ∈ smallDetPrefixSlice, 0 ≤ Real.log 3 / scale m := by
    intro m hm
    have hm3 : 3 ≤ m := (mem_smallDetPrefixSlice.mp hm).2.1
    exact div_nonneg (Real.log_pos (by norm_num)).le
      (scale_pos_of_three_le hm3).le
  have hsingle : Real.log 3 / scale n ≤
      ∑ m ∈ smallDetPrefixSlice, Real.log 3 / scale m :=
    Finset.single_le_sum hterm_nonneg hn
  linarith

/-- **The explicit finite check.**  On the finite initial segment the factor `3`
is absorbed by the enlarged exponent `adjustedC P`. -/
theorem three_mul_exp_cMax_le_exp_adjustedC {W smallDet : ℕ → ℝ}
    (P : SmallDetPaperInputs W smallDet) {n : ℕ}
    (hn : n ∈ smallDetPrefixSlice) :
    3 * exp (P.cMax * scale n) ≤ exp (adjustedC P * scale n) := by
  have hn3 : 3 ≤ n := (mem_smallDetPrefixSlice.mp hn).2.1
  have hspos : 0 < scale n := scale_pos_of_three_le hn3
  have hC := cMax_add_div_le_adjustedC P hn
  have hdiv : Real.log 3 / scale n ≤ adjustedC P - P.cMax := by linarith
  have hmul : Real.log 3 / scale n * scale n ≤
      (adjustedC P - P.cMax) * scale n :=
    mul_le_mul_of_nonneg_right hdiv hspos.le
  have hcancel : Real.log 3 / scale n * scale n = Real.log 3 := by
    field_simp [hspos.ne']
  rw [hcancel] at hmul
  calc
    3 * exp (P.cMax * scale n) =
        exp (Real.log 3) * exp (P.cMax * scale n) := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    _ = exp (Real.log 3 + P.cMax * scale n) := by rw [← Real.exp_add]
    _ ≤ exp ((adjustedC P - P.cMax) * scale n + P.cMax * scale n) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = exp (adjustedC P * scale n) := by
      congr 1
      ring

/-! ## 4. The three-term union bound before the factor `3` is absorbed -/

/-- Monotonicity of the `exp (c · s) · exp (-η · w)` envelope. -/
private theorem exp_envelope_mono {c c' η η' s w : ℝ}
    (hcc : c ≤ c') (hη : η' ≤ η) (hs : 0 ≤ s) (hw : 0 ≤ w) :
    exp (c * s) * exp (-η * w) ≤ exp (c' * s) * exp (-η' * w) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : c * s ≤ c' * s := mul_le_mul_of_nonneg_right hcc hs
  have h2 : -η * w ≤ -η' * w := by nlinarith
  linarith

/-- The three-term union bound keeping the factor `3` visible.  This is the
proof of `SmallDetPaperInputs.smallDet_le_of_scale_ge_one` stopped before the
absorption of `3`. -/
theorem smallDet_le_three_mul {W smallDet : ℕ → ℝ}
    (P : SmallDetPaperInputs W smallDet) {n : ℕ} (hs : 0 ≤ scale n) :
    smallDet n ≤ 3 * (exp (P.cMax * scale n) * exp (-P.eta * W n)) := by
  have hW := P.W_nonneg n
  have h1 : P.distinct n ≤ exp (P.cMax * scale n) * exp (-P.eta * W n) :=
    (P.distinct_bound n).trans
      (exp_envelope_mono P.cDistinct_le_cMax P.eta_le_distinct hs hW)
  have h2 : P.sameDen n ≤ exp (P.cMax * scale n) * exp (-P.eta * W n) :=
    (P.sameDen_bound n).trans
      (exp_envelope_mono P.cSame_le_cMax P.eta_le_same hs hW)
  have h3 : P.diag n ≤ exp (P.cMax * scale n) * exp (-P.eta * W n) :=
    (P.diag_bound n).trans
      (exp_envelope_mono P.cDiag_le_cMax P.eta_le_diag hs hW)
  calc
    smallDet n = P.distinct n + P.sameDen n + P.diag n := P.pair_split n
    _ ≤ exp (P.cMax * scale n) * exp (-P.eta * W n) +
          exp (P.cMax * scale n) * exp (-P.eta * W n) +
            exp (P.cMax * scale n) * exp (-P.eta * W n) := by
      linarith [h1, h2, h3]
    _ = 3 * (exp (P.cMax * scale n) * exp (-P.eta * W n)) := by ring

/-- **The pointwise bound for `n ≥ 3`.**  The factor `3` is absorbed either by
`scale n ≥ 1` (the paper's estimate), or by the finite initial-segment constant
`adjustedC`. -/
theorem smallDet_le_adjusted_of_three_le {W smallDet : ℕ → ℝ}
    (P : SmallDetPaperInputs W smallDet) {n : ℕ} (hn : 3 ≤ n) :
    smallDet n ≤ exp (adjustedC P * scale n) * exp (-P.eta * W n) := by
  have hspos : 0 < scale n := scale_pos_of_three_le hn
  by_cases hN : n < scaleThreshold
  · by_cases hs1 : scale n < 1
    · have hmem : n ∈ smallDetPrefixSlice :=
        mem_smallDetPrefixSlice.mpr ⟨hN, hn, hs1⟩
      have hthree := smallDet_le_three_mul P hspos.le
      have habs := three_mul_exp_cMax_le_exp_adjustedC P hmem
      calc
        smallDet n ≤ 3 * (exp (P.cMax * scale n) * exp (-P.eta * W n)) :=
          hthree
        _ = (3 * exp (P.cMax * scale n)) * exp (-P.eta * W n) := by ring
        _ ≤ exp (adjustedC P * scale n) * exp (-P.eta * W n) :=
          mul_le_mul_of_nonneg_right habs (by positivity)
    · have hsge : 1 ≤ scale n := le_of_not_gt hs1
      exact (P.smallDet_le_of_scale_ge_one hsge).trans
        (exp_envelope_mono (c_le_adjustedC P) le_rfl hspos.le (P.W_nonneg n))
  · have hsge : 1 ≤ scale n :=
      one_le_scale_of_scaleThreshold_le (le_of_not_gt hN)
    exact (P.smallDet_le_of_scale_ge_one hsge).trans
      (exp_envelope_mono (c_le_adjustedC P) le_rfl
        (le_trans zero_le_one hsge) (P.W_nonneg n))

/-! ## 5. Eventual bound and the L19.6 consequences -/

/-- The sharp small-determinant bound eventually holds with the adjusted
polynomial exponent `adjustedC P`; no initial-segment hypothesis is used. -/
theorem smallDet_eventually_bound {W smallDet : ℕ → ℝ}
    (P : SmallDetPaperInputs W smallDet) :
    ∀ᶠ n : ℕ in atTop,
      smallDet n ≤ exp (adjustedC P * scale n) * exp (-P.eta * W n) := by
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
  exact smallDet_le_adjusted_of_three_le P hn

/-- **L19.6 small-determinant `SubexpLoss` without a prefix hypothesis.** -/
theorem smallDet_subexpLoss {W smallDet : ℕ → ℝ}
    (P : SmallDetPaperInputs W smallDet) (hW : DominatesScale W) :
    SubexpLoss smallDet :=
  subexpLoss_of_eventually_le (smallDet_eventually_bound P)
    (subexpLoss_exp_mul_exp_neg (W := W) hW (C := adjustedC P) P.eta_pos)

/-! ## 6. The sharp L19.6 structure with `smallDet_prefix` deleted -/

/-- The sharp L19.6 assembly with no initial-segment field.  It is exactly
`LatticePaperThinInputs` with `smallDet_prefix` removed: the thin bound remains
the L18.4 lattice count with `η = 1/4`, and the small-determinant bound is the
three paper contributions with the adjusted finite constant `adjustedC`. -/
structure LatticePaperThinFiniteInputs where
  /-- Logarithmic mark scale `W = log V`. -/
  W : ℕ → ℝ
  /-- The L19.6 thin fraction. -/
  thin : ℕ → ℝ
  /-- The L19.6 small-determinant fraction. -/
  smallDet : ℕ → ℝ
  /-- The L18.4 determinant-strip count. -/
  lattice : Cogentic.RandomizedL18_4.ThinPairInputs W thin
  /-- `log V = D^{O(1)}` dominates every fixed multiple of `scale`. -/
  W_dominates : DominatesScale W
  /-- The thin fraction is nonnegative. -/
  thin_nonneg : ∀ n, 0 ≤ thin n
  /-- The three paper contributions to `smallDet`. -/
  paper : SmallDetPaperInputs W smallDet

namespace LatticePaperThinFiniteInputs

variable (S : LatticePaperThinFiniteInputs)

/-- The L19.6 deficit: the genuine sum of the thin and small-determinant
fractions.  It is not modified by the finite-constant adjustment. -/
noncomputable def loss (n : ℕ) : ℝ := S.thin n + S.smallDet n

theorem loss_nonneg (n : ℕ) : 0 ≤ S.loss n :=
  add_nonneg (S.thin_nonneg n) (S.paper.smallDet_nonneg n)

/-- The thin-pair field, proved from the L18.4 lattice count. -/
theorem thin_bound (n : ℕ) :
    S.thin n ≤ exp ((0 : ℝ) * scale n) * exp (-(1 / 4 : ℝ) * S.W n) :=
  thin_bound_of_lattice S.lattice n

/-- The small-determinant field, eventually with the adjusted constant. -/
theorem smallDet_eventually_bound :
    ∀ᶠ n : ℕ in atTop,
      S.smallDet n ≤
        exp (adjustedC S.paper * scale n) * exp (-S.paper.eta * S.W n) :=
  Cogentic.RandomizedL19ThinFinite.smallDet_eventually_bound S.paper

/-- The small-determinant `SubexpLoss` field, with no prefix hypothesis. -/
theorem smallDet_subexpLoss : SubexpLoss S.smallDet :=
  Cogentic.RandomizedL19ThinFinite.smallDet_subexpLoss S.paper S.W_dominates

/-- **The L19.6 `SubexpLoss` for the sharp route.** -/
theorem subexpLoss : SubexpLoss S.loss := by
  apply subexpLoss_of_eventually_le
    (g := fun n =>
      exp ((0 : ℝ) * scale n) * exp (-(1 / 4 : ℝ) * S.W n) +
        exp (adjustedC S.paper * scale n) * exp (-S.paper.eta * S.W n))
  · filter_upwards [S.smallDet_eventually_bound] with n hdet
    unfold loss
    exact add_le_add (S.thin_bound n) hdet
  · exact subexpLoss_add
      (subexpLoss_exp_mul_exp_neg (W := S.W) S.W_dominates
        (C := 0) (by norm_num))
      (subexpLoss_exp_mul_exp_neg (W := S.W) S.W_dominates
        (C := adjustedC S.paper) S.paper.eta_pos)

/-- **The L19.6 `SubexpLeaf` for the sharp route.** -/
noncomputable def toSubexpLeaf : SubexpLeaf where
  loss := S.loss
  loss_nonneg := S.loss_nonneg
  paper := S.subexpLoss

/-- The C5 `B = 2` slot. -/
theorem slot_le : ∀ᶠ n : ℕ in atTop,
    S.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.subexpLoss 2 (by norm_num)

end LatticePaperThinFiniteInputs

/-! ## 7. The literal replacement: an explicit three-point `Finset` check

The no-check structure above is enough for the L19.6 leaf.  For the literal
pointwise form of `smallDet_prefix`, the only indices not covered by
`smallDet_le_adjusted_of_three_le` are `n = 0, 1, 2` (where `scale n ≤ 0` and
the factor-`3` absorption cannot be arranged by increasing `c`).  Those are
recorded as the explicit finite check on `Finset.range 3`. -/

/-- **The original `smallDet_prefix`, reduced to a three-element `Finset`
check.**  For every `n` with `scale n < 1`, either `n ≥ 3` and the adjusted
bound is proved, or `n ∈ {0,1,2}` and the explicit finite check applies. -/
theorem smallDet_prefix_of_finite_range {W smallDet : ℕ → ℝ}
    (P : SmallDetPaperInputs W smallDet)
    (hsmall : ∀ n ∈ Finset.range 3,
      smallDet n ≤ exp (adjustedC P * scale n) * exp (-P.eta * W n)) :
    ∀ n : ℕ, scale n < 1 →
      smallDet n ≤ exp (adjustedC P * scale n) * exp (-P.eta * W n) := by
  intro n _
  by_cases hn3 : 3 ≤ n
  · exact smallDet_le_adjusted_of_three_le P hn3
  · exact hsmall n (Finset.mem_range.mpr (not_le.mp hn3))

/-- The pointwise sharp L19.6 structure.  Its only initial-segment field is the
explicit finite check on `Finset.range 3`; it is not a zero-loss assertion. -/
structure LatticePaperThinFinitePointwiseInputs where
  /-- Logarithmic mark scale `W = log V`. -/
  W : ℕ → ℝ
  /-- The L19.6 thin fraction. -/
  thin : ℕ → ℝ
  /-- The L19.6 small-determinant fraction. -/
  smallDet : ℕ → ℝ
  /-- The L18.4 determinant-strip count. -/
  lattice : Cogentic.RandomizedL18_4.ThinPairInputs W thin
  /-- `log V = D^{O(1)}` dominates every fixed multiple of `scale`. -/
  W_dominates : DominatesScale W
  /-- The thin fraction is nonnegative. -/
  thin_nonneg : ∀ n, 0 ≤ thin n
  /-- The three paper contributions to `smallDet`. -/
  paper : SmallDetPaperInputs W smallDet
  /-- **The explicit finite check** at `n = 0, 1, 2`, with the adjusted
  polynomial constant. -/
  smallDet_prefixCheck : ∀ n ∈ Finset.range 3,
    smallDet n ≤ exp (adjustedC paper * scale n) * exp (-paper.eta * W n)

namespace LatticePaperThinFinitePointwiseInputs

variable (S : LatticePaperThinFinitePointwiseInputs)

/-- The pointwise small-determinant bound: `n ≥ 3` is proved, `n < 3` is the
explicit three-point check. -/
theorem smallDet_bound (n : ℕ) :
    S.smallDet n ≤
      exp (adjustedC S.paper * scale n) * exp (-S.paper.eta * S.W n) := by
  by_cases hn3 : 3 ≤ n
  · exact smallDet_le_adjusted_of_three_le S.paper hn3
  · exact S.smallDet_prefixCheck n (Finset.mem_range.mpr (not_le.mp hn3))

/-- The literal `smallDet_prefix` field of
`Cogentic.RandomizedL19Thin.LatticePaperThinInputs`, now with adjusted
constants and derived from the finite check. -/
theorem smallDet_prefix :
    ∀ n : ℕ, scale n < 1 →
      S.smallDet n ≤
        exp (adjustedC S.paper * scale n) * exp (-S.paper.eta * S.W n) :=
  smallDet_prefix_of_finite_range S.paper S.smallDet_prefixCheck

/-- **The sharp L19.6 `ThinPairInputs` with the prefix field replaced by the
finite check.** -/
noncomputable def toThinPairInputs :
    Cogentic.RandomizedL19SecondMoment.ThinPairInputs where
  W := S.W
  W_nonneg := S.lattice.W_nonneg
  W_dominates := S.W_dominates
  thin := S.thin
  smallDet := S.smallDet
  thin_nonneg := S.thin_nonneg
  smallDet_nonneg := S.paper.smallDet_nonneg
  cThin := 0
  etaThin := 1 / 4
  etaThin_pos := by norm_num
  cDet := adjustedC S.paper
  etaDet := S.paper.eta
  etaDet_pos := S.paper.eta_pos
  thin_bound := fun n => thin_bound_of_lattice S.lattice n
  smallDet_bound := S.smallDet_bound

/-- The L19.6 `SubexpLoss` from the pointwise finite-check route. -/
theorem subexpLoss : SubexpLoss S.toThinPairInputs.loss :=
  S.toThinPairInputs.subexpLoss

/-- The L19.6 `SubexpLeaf` from the pointwise finite-check route. -/
noncomputable def toSubexpLeaf : SubexpLeaf :=
  S.toThinPairInputs.toSubexpLeaf

/-- The C5 `B = 2` slot from the pointwise finite-check route. -/
theorem slot_le : ∀ᶠ n : ℕ in atTop,
    S.toThinPairInputs.loss n ≤ exp (-(2 : ℝ) * scale n) :=
  S.toThinPairInputs.slot_le

end LatticePaperThinFinitePointwiseInputs

/-! ## 8. Compatibility with the sharp `LatticePaperThinInputs` -/

/-- Every sharp `LatticePaperThinInputs` gives a `LatticePaperThinFiniteInputs`
by forgetting the now-unnecessary prefix field.  The new route therefore
subsumes the old one without using `smallDet_prefix`. -/
def ofSharp (S : Cogentic.RandomizedL19Thin.LatticePaperThinInputs) :
    LatticePaperThinFiniteInputs where
  W := S.W
  thin := S.thin
  smallDet := S.smallDet
  lattice := S.lattice
  W_dominates := S.W_dominates
  thin_nonneg := S.thin_nonneg
  paper := S.paper

theorem ofSharp_subexpLoss (S : Cogentic.RandomizedL19Thin.LatticePaperThinInputs) :
    SubexpLoss (ofSharp S).loss :=
  (ofSharp S).subexpLoss

/-! ## Axiom audit -/

#print axioms scale_pos_of_three_le
#print axioms one_le_scale_of_scaleThreshold_le
#print axioms mem_smallDetPrefixSlice
#print axioms c_le_adjustedC
#print axioms cMax_add_div_le_adjustedC
#print axioms three_mul_exp_cMax_le_exp_adjustedC
#print axioms smallDet_le_three_mul
#print axioms smallDet_le_adjusted_of_three_le
#print axioms smallDet_eventually_bound
#print axioms smallDet_subexpLoss
#print axioms LatticePaperThinFiniteInputs.loss_nonneg
#print axioms LatticePaperThinFiniteInputs.thin_bound
#print axioms LatticePaperThinFiniteInputs.smallDet_eventually_bound
#print axioms LatticePaperThinFiniteInputs.smallDet_subexpLoss
#print axioms LatticePaperThinFiniteInputs.subexpLoss
#print axioms LatticePaperThinFiniteInputs.toSubexpLeaf
#print axioms LatticePaperThinFiniteInputs.slot_le
#print axioms smallDet_prefix_of_finite_range
#print axioms LatticePaperThinFinitePointwiseInputs.smallDet_bound
#print axioms LatticePaperThinFinitePointwiseInputs.smallDet_prefix
#print axioms LatticePaperThinFinitePointwiseInputs.toThinPairInputs
#print axioms LatticePaperThinFinitePointwiseInputs.subexpLoss
#print axioms LatticePaperThinFinitePointwiseInputs.toSubexpLeaf
#print axioms LatticePaperThinFinitePointwiseInputs.slot_le
#print axioms ofSharp
#print axioms ofSharp_subexpLoss

end Cogentic.RandomizedL19ThinFinite
