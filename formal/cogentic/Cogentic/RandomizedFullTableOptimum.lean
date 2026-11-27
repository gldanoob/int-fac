import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized

noncomputable def fullTableRatio : ℝ := (Real.sqrt 13 - 1) / 3

noncomputable def fullTableOptimalCube : ℝ := (92 + 26 * Real.sqrt 13) / 27

noncomputable def fullTableOptimum : ℝ := fullTableOptimalCube ^ (1 / 3 : ℝ)

/-- The shared scan and sparse solve budgets with only radix height charged.
The supply constraint uses the smallest incoming algebraic scale `a`. -/
def HeightFreeFullTableBudget (C : ℝ) : Prop :=
  ∃ a r δ v : ℝ, 0 < a ∧ 0 < r ∧ 0 < δ ∧ 0 ≤ v ∧ 2 * v ≤ C ∧
    2 * max r a ≤ C ∧ a + 1 / (3 * δ * r) + (1 / δ + δ * v) / (3 * a) ≤ 2 * v

/-- The full flexible population charges each field's base and the separate algebraic tests. -/
def PooledHeightFreeFullTableBudget (C : ℝ) : Prop :=
  ∃ a r δ v f : ℝ, 0 < a ∧ 0 < r ∧ 0 < δ ∧ 0 ≤ v ∧ 0 ≤ f ∧ 2 * v ≤ C ∧
    2 * v - 1 / (3 * δ * r) + f ≤ C ∧ 2 * max r (a + f) ≤ C ∧
    max r (a + f) + 1 / (3 * δ * r) + (1 / δ + δ * v) / (3 * a) ≤ 2 * v + f

private theorem fullTableOptimalCube_pos : 0 < fullTableOptimalCube := by
  unfold fullTableOptimalCube
  positivity

theorem fullTableOptimum_pos : 0 < fullTableOptimum :=
  Real.rpow_pos_of_pos fullTableOptimalCube_pos _

theorem fullTableOptimum_cube : fullTableOptimum ^ (3 : ℕ) = fullTableOptimalCube := by
  unfold fullTableOptimum
  rw [← Real.rpow_natCast, ← Real.rpow_mul fullTableOptimalCube_pos.le]
  norm_num

theorem fullTableRatio_bounds : 0 < fullTableRatio ∧ fullTableRatio < 1 := by
  have hlo : (1 : ℝ) < Real.sqrt 13 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hhi : Real.sqrt 13 < (4 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  unfold fullTableRatio
  constructor <;> linarith only [hlo, hhi]

/-- The polynomial ratio bound includes both endpoints, and equality occurs only
at the interior optimal ratio. -/
theorem fullTable_ratio_minimum {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    fullTableOptimalCube * (9 * t ^ 2 * (1 - t / 2) ^ 2) ≤ 8 * (1 + t) ∧
      (fullTableOptimalCube * (9 * t ^ 2 * (1 - t / 2) ^ 2) = 8 * (1 + t) ↔
        t = fullTableRatio) := by
  let q : ℝ := Real.sqrt 13
  let B : ℝ := q + 7 + (56 + 17 * q) / 6 * t + (46 + 13 * q) / 6 * (t * (1 - t))
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hgap : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hq_sq : q ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hfactor : 8 * (1 + t) - fullTableOptimalCube * (9 * t ^ 2 * (1 - t / 2) ^ 2) =
      (t - fullTableRatio) ^ 2 * B := by
    change 8 * (1 + t) - (92 + 26 * q) / 27 * (9 * t ^ 2 * (1 - t / 2) ^ 2) =
      (t - (q - 1) / 3) ^ 2 * B
    dsimp only [B]
    linear_combination
      (q * (13 * t ^ 2 / 54 - 5 * t / 9 - 1 / 9) -
        13 * t ^ 3 / 9 + 100 * t ^ 2 / 27 - t / 9 - 5 / 9) * hq_sq
  refine ⟨sub_nonneg.mp (hfactor.symm ▸ mul_nonneg (sq_nonneg _) hB.le), ?_⟩
  calc
    _ ↔ 8 * (1 + t) - fullTableOptimalCube * (9 * t ^ 2 * (1 - t / 2) ^ 2) = 0 := by
      rw [sub_eq_zero, eq_comm]
    _ ↔ _ := by rw [hfactor]; simp [hB.ne', sub_eq_zero]

private theorem normalized_full_table_supply {C t δ : ℝ}
    (hC : 0 < C) (ht : 0 < t) (hδ : 0 < δ) :
    t * C / 2 + 1 / (3 * δ * (C / 2)) + (1 / δ + δ * (C / 2)) / (3 * (t * C / 2)) ≤ C ↔
      (1 + t) / δ + C * δ / 2 ≤ 3 * C ^ 2 * t * (1 - t / 2) / 2 := by
  have factor : 0 < 3 * (t * C / 2) := by positivity
  have he : (C - (t * C / 2 +
        1 / (3 * δ * (C / 2)) + (1 / δ + δ * (C / 2)) / (3 * (t * C / 2)))) *
        (3 * (t * C / 2)) =
      3 * C ^ 2 * t * (1 - t / 2) / 2 - ((1 + t) / δ + C * δ / 2) := by
    field_simp
    ring
  constructor
  · intro h
    have hh := mul_nonneg (sub_nonneg.mpr h) factor.le
    rw [he] at hh
    exact sub_nonneg.mp hh
  · intro h
    have hh := sub_nonneg.mpr h
    rw [← he] at hh
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right factor).mp hh)

private theorem normalized_full_table_cube {C t δ : ℝ} (hC : 0 < C) (ht : 0 < t)
    (hδ : 0 < δ) (h : (1 + t) / δ + C * δ / 2 ≤ 3 * C ^ 2 * t * (1 - t / 2) / 2) :
    8 * (1 + t) ≤ 9 * C ^ 3 * t ^ 2 * (1 - t / 2) ^ 2 := by
  have hprod : ((1 + t) / δ) * (C * δ / 2) = C * (1 + t) / 2 := by field_simp
  have hroot : Real.sqrt (2 * C * (1 + t)) ≤ (1 + t) / δ + C * δ / 2 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith only [hprod, sq_nonneg ((1 + t) / δ - C * δ / 2)]⟩
  have hsq := (Real.sqrt_le_iff.mp (hroot.trans h)).2
  apply le_of_mul_le_mul_left (a := C) _ hC
  nlinarith only [hsq]

private theorem normalized_full_table_witness {C t : ℝ} (hC : 0 < C) (ht : 0 < t) (ht₁ : t ≤ 1)
    (h : 8 * (1 + t) ≤ 9 * C ^ 3 * t ^ 2 * (1 - t / 2) ^ 2) :
    let δ := Real.sqrt (2 * (1 + t) / C)
    0 < δ ∧ (1 + t) / δ + C * δ / 2 ≤ 3 * C ^ 2 * t * (1 - t / 2) / 2 := by
  let L := 3 * C ^ 2 * t * (1 - t / 2) / 2
  have hgap : 0 ≤ 1 - t / 2 := by linarith only [ht₁]
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hrad : 0 ≤ 2 * C * (1 + t) := by positivity
  have hs := mul_le_mul_of_nonneg_left h hC.le
  have hroot : Real.sqrt (2 * C * (1 + t)) ≤ L := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hL, by dsimp [L]; nlinarith only [hs]⟩
  let δ := Real.sqrt (2 * (1 + t) / C)
  have hδ : 0 < δ := Real.sqrt_pos.2 (by positivity)
  have hδsq : δ ^ 2 = 2 * (1 + t) / C := Real.sq_sqrt (by positivity)
  have he : (1 + t) / δ = C * δ / 2 := by
    apply (div_eq_iff hδ.ne').2
    calc
      _ = C / 2 * (2 * (1 + t) / C) := by field_simp
      _ = _ := by rw [← hδsq]; ring
  have hroot_eq : Real.sqrt (2 * C * (1 + t)) = C * δ := by
    apply (Real.sqrt_eq_iff_eq_sq hrad (by positivity)).2
    calc
      _ = C ^ 2 * (2 * (1 + t) / C) := by field_simp
      _ = _ := by rw [← hδsq]; ring
  change 0 < δ ∧ (1 + t) / δ + C * δ / 2 ≤ L
  refine ⟨hδ, ?_⟩
  rw [he]
  linarith only [hroot, hroot_eq]

private theorem heightFreeFullTableBudget_lower {C : ℝ} (h : HeightFreeFullTableBudget C) :
    fullTableOptimum ≤ C := by
  rcases h with ⟨a, r, δ, v, ha, hr, hδ, hv, hscan, hsolve, hsupply⟩
  have haC : a ≤ C / 2 := by linarith only [le_max_right r a, hsolve]
  have hrC : r ≤ C / 2 := by linarith only [le_max_left r a, hsolve]
  have hC : 0 < C := by linarith only [ha, haC]
  have hsplit : δ * v / (3 * a) = (δ / (3 * a)) * v := by ring
  rw [add_div, hsplit] at hsupply
  have hmargin : a + 1 / (3 * δ * r) + (1 / δ) / (3 * a) ≤ (2 - δ / (3 * a)) * v := by
    linarith only [hsupply]
  have hleft : 0 < a + 1 / (3 * δ * r) + (1 / δ) / (3 * a) := by positivity
  have hcoef := pos_of_mul_pos_left (hleft.trans_le hmargin) hv
  have hsweep := mul_le_mul_of_nonneg_left (show v ≤ C / 2 by linarith only [hscan]) hcoef.le
  have hrat : 1 / (3 * δ * (C / 2)) ≤ 1 / (3 * δ * r) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hrC (by positivity))
  have hnew : a + 1 / (3 * δ * (C / 2)) + (1 / δ + δ * (C / 2)) / (3 * a) ≤ C := by
    rw [add_div, show δ * (C / 2) / (3 * a) = (δ / (3 * a)) * (C / 2) by ring]
    linarith only [hmargin, hsweep, hrat]
  let t := 2 * a / C
  have ht : 0 < t := by dsimp [t]; positivity
  have ht₁ : t ≤ 1 := (div_le_iff₀ hC).2 (by linarith only [haC])
  have hat : t * C / 2 = a := by dsimp [t]; field_simp
  have hnormalized := (normalized_full_table_supply hC ht hδ).1 (by rwa [hat])
  have hpoly := normalized_full_table_cube hC ht hδ hnormalized
  have htgap : 0 < 1 - t / 2 := by linarith only [ht₁]
  have hden : 0 < 9 * t ^ 2 * (1 - t / 2) ^ 2 := by positivity
  have hopt := (fullTable_ratio_minimum ht.le ht₁).1.trans hpoly
  have hcube : fullTableOptimalCube ≤ C ^ (3 : ℕ) := by
    apply le_of_mul_le_mul_right _ hden
    convert hopt using 1
    ring
  apply (pow_le_pow_iff_left₀ fullTableOptimum_pos.le hC.le (by decide : (3 : ℕ) ≠ 0)).1
  simpa only [fullTableOptimum_cube] using hcube

private theorem optimal_full_table_supply :
    let B := fullTableOptimum
    let t := fullTableRatio
    let δ := Real.sqrt (2 * (1 + t) / B)
    0 < δ ∧ t * B / 2 + 1 / (3 * δ * (B / 2)) +
      (1 / δ + δ * (B / 2)) / (3 * (t * B / 2)) ≤ B := by
  let B := fullTableOptimum
  have hB : 0 < B := fullTableOptimum_pos
  let t := fullTableRatio
  have ht : 0 < t := fullTableRatio_bounds.1
  have ht₁ : t ≤ 1 := fullTableRatio_bounds.2.le
  have hpoly : 8 * (1 + t) ≤ 9 * B ^ 3 * t ^ 2 * (1 - t / 2) ^ 2 := by
    have he := (fullTable_ratio_minimum ht.le ht₁).2.mpr (rfl : t = fullTableRatio)
    change 8 * (1 + t) ≤ 9 * fullTableOptimum ^ 3 * t ^ 2 * (1 - t / 2) ^ 2
    rw [fullTableOptimum_cube, ← he]
    ring_nf
    exact le_rfl
  have ⟨hδ, hδ_supply⟩ := normalized_full_table_witness hB ht ht₁ hpoly
  exact ⟨hδ, (normalized_full_table_supply hB ht hδ).2 hδ_supply⟩

/-- The minimum is attained in the relaxed ledger, and every larger budget is feasible. -/
theorem heightFreeFullTableBudget_iff {C : ℝ} :
    HeightFreeFullTableBudget C ↔ fullTableOptimum ≤ C := by
  refine ⟨heightFreeFullTableBudget_lower, ?_⟩
  intro hC
  let B := fullTableOptimum
  let t := fullTableRatio
  let δ := Real.sqrt (2 * (1 + t) / B)
  have hB : 0 < B := fullTableOptimum_pos
  have ht : 0 < t := fullTableRatio_bounds.1
  have ht₁ : t ≤ 1 := fullTableRatio_bounds.2.le
  obtain ⟨hδ, hδ_supply⟩ := optimal_full_table_supply
  have ha : 0 < t * B / 2 := by positivity
  have hr : 0 < B / 2 := by positivity
  have har : t * B / 2 ≤ B / 2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr ht₁) hB.le]
  refine ⟨t * B / 2, B / 2, δ, B / 2, ha, hr, hδ, hr.le, ?_, ?_, ?_⟩
  · linarith only [hC]
  · rw [max_eq_left har]
    linarith only [hC]
  · rw [show 2 * (B / 2) = B by ring]
    exact hδ_supply

theorem fullTable_zero_ratio_infeasible (C : ℝ) :
    ¬ (8 * (1 + (0 : ℝ)) ≤ 9 * C ^ 3 * 0 ^ 2 * (1 - 0 / 2) ^ 2) := by norm_num

theorem fullTable_unit_ratio_iff (C : ℝ) :
    8 * (1 + (1 : ℝ)) ≤ 9 * C ^ 3 * 1 ^ 2 * (1 - 1 / 2) ^ 2 ↔ 64 / 9 ≤ C ^ 3 := by
  constructor <;> intro h <;> nlinarith only [h]

theorem fullTableOptimum_bounds : 1.90188361 < fullTableOptimum ∧ fullTableOptimum < 1.90188362 := by
  have hlo : (3.6055512754 : ℝ) < Real.sqrt 13 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hhi : Real.sqrt 13 < (3.6055512755 : ℝ) :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  constructor
  · apply (pow_lt_pow_iff_left₀ (by norm_num) fullTableOptimum_pos.le (by decide : (3 : ℕ) ≠ 0)).mp
    rw [fullTableOptimum_cube, fullTableOptimalCube]
    linarith only [hlo]
  · apply (pow_lt_pow_iff_left₀ fullTableOptimum_pos.le (by norm_num) (by decide : (3 : ℕ) ≠ 0)).mp
    rw [fullTableOptimum_cube, fullTableOptimalCube]
    linarith only [hhi]

/-- The pooled flexible ledger has the same minimum, attained with `f = r - a`. -/
theorem pooledHeightFreeFullTableBudget_iff {C : ℝ} :
    PooledHeightFreeFullTableBudget C ↔ fullTableOptimum ≤ C := by
  constructor
  · rintro ⟨a, r, δ, v, f, ha, hr, hδ, hv, hf, hscan, _, hsolve, hrows⟩
    have hbase : max r a ≤ max r (a + f) :=
      max_le (le_max_left _ _) ((le_add_of_nonneg_right hf).trans (le_max_right _ _))
    apply heightFreeFullTableBudget_lower
    exact ⟨a, r, δ, v, ha, hr, hδ, hv, hscan, by linarith only [hsolve, hbase],
      by linarith only [hrows, le_max_right r (a + f)]⟩
  · intro hC
    let B := fullTableOptimum
    let t := fullTableRatio
    let δ := Real.sqrt (2 * (1 + t) / B)
    let a := t * B / 2
    let r := B / 2
    let f := r - a
    have hB : 0 < B := fullTableOptimum_pos
    have ht : 0 < t := fullTableRatio_bounds.1
    have ht₁ : t ≤ 1 := fullTableRatio_bounds.2.le
    have htlo : (0.85 : ℝ) ≤ t := by
      have hq : (3.55 : ℝ) < Real.sqrt 13 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
      dsimp [t, fullTableRatio]
      linarith only [hq]
    have hBlo : (1.9 : ℝ) ≤ B := by linarith only [fullTableOptimum_bounds.1]
    have hBhi : B ≤ 2 := by linarith only [fullTableOptimum_bounds.2]
    obtain ⟨hδ, hsupply⟩ := optimal_full_table_supply
    have hδhi : δ ≤ 3 / 2 := by
      apply (Real.sqrt_le_left (by norm_num)).2
      apply (div_le_iff₀ hB).2
      linarith only [ht₁, hBlo]
    have ha : 0 < a := by dsimp [a]; positivity
    have hr : 0 < r := by dsimp [r]; positivity
    have hrhi : r ≤ 1 := by dsimp [r]; linarith only [hBhi]
    have hfeq : f = (1 - t) * r := by dsimp [f, a, r]; ring
    have hf : 0 ≤ f := hfeq ▸ mul_nonneg (sub_nonneg.mpr ht₁) hr.le
    have hfhi : f ≤ 0.15 := by
      rw [hfeq]
      calc
        _ ≤ (0.15 : ℝ) * 1 :=
          mul_le_mul (by linarith only [htlo]) hrhi hr.le (by norm_num)
        _ = _ := by ring
    have hrational : f ≤ 1 / (3 * δ * r) := by
      apply (le_div_iff₀ (show 0 < 3 * δ * r by positivity)).2
      rw [mul_comm f]
      calc
        _ ≤ (3 * (3 / 2) * 1 : ℝ) * 0.15 := by
          gcongr
        _ ≤ _ := by norm_num
    have hmax : max r (a + f) = r := by
      rw [show a + f = r by dsimp [f]; ring, max_self]
    change a + 1 / (3 * δ * r) + (1 / δ + δ * r) / (3 * a) ≤ B at hsupply
    change B ≤ C at hC
    have hscan : 2 * r ≤ C := by dsimp [r]; linarith only [hC]
    refine ⟨a, r, δ, r, f, ha, hr, hδ, hr.le, hf, hscan,
      by linarith only [hscan, hrational], by simpa only [hmax] using hscan, ?_⟩
    rw [hmax]
    dsimp only [f, r]
    linarith only [hsupply]

/-- The optimal coefficient is the unique nonnegative root of its integer polynomial. -/
theorem fullTableOptimum_polynomial_iff {C : ℝ} (hC : 0 ≤ C) :
    27 * C ^ 6 - 184 * C ^ 3 - 12 = 0 ↔ C = fullTableOptimum := by
  have hq : 0 ≤ 26 * Real.sqrt 13 := by positivity
  have hq_sq : (Real.sqrt 13) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have hsign : 0 ≤ 27 * C ^ 3 - 92 := by
      by_contra! hneg
      have hprod := mul_nonneg (pow_nonneg hC 3) (show 0 ≤ 184 - 27 * C ^ 3 by linarith only [hneg])
      nlinarith only [hprod, h]
    have hs : (27 * C ^ 3 - 92) ^ 2 = (26 * Real.sqrt 13) ^ 2 := by
      nlinarith only [h, hq_sq]
    have he := (pow_left_inj₀ hsign hq two_ne_zero).1 hs
    apply (pow_left_inj₀ hC fullTableOptimum_pos.le (by decide : (3 : ℕ) ≠ 0)).1
    rw [fullTableOptimum_cube, fullTableOptimalCube]
    linarith only [he]
  · rintro rfl
    rw [show fullTableOptimum ^ 6 = (fullTableOptimum ^ 3) ^ 2 by ring, fullTableOptimum_cube]
    unfold fullTableOptimalCube
    nlinarith only [hq_sq]

end Cogentic.Randomized

#print axioms Cogentic.Randomized.fullTableOptimum_cube
#print axioms Cogentic.Randomized.fullTable_ratio_minimum
#print axioms Cogentic.Randomized.heightFreeFullTableBudget_iff
#print axioms Cogentic.Randomized.pooledHeightFreeFullTableBudget_iff
#print axioms Cogentic.Randomized.fullTableOptimum_bounds
#print axioms Cogentic.Randomized.fullTableOptimum_polynomial_iff
