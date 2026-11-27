import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized

/-- A stage with parent cutoff at least `r` and child cutoff at most `r`
forces the same lower cost whether the stage uses a table or raw search.
The mean constraint supplies the positive slope needed in both cases. -/
theorem cutoff_crossing_tradeoff {r δ A y child sR sA v C : ℝ}
    (hr : 0 < r) (hd : 0 < δ) (hA : 0 ≤ A) (hy : r ≤ y)
    (hc : 0 < child) (hcr : child ≤ r) (hv : 0 ≤ v)
    (hsR : 1/(3*δ*r) ≤ sR) (hsA : (A+δ*v)/(3*child) ≤ sA)
    (hmean : y+sR+sA ≤ 2*v)
    (hbudget : 2*v ≤ C ∨ r+sR+sA ≤ C) :
    δ < 6*r ∧ 2*A+2/δ+δ*C ≤ 6*r*(C-r) := by
  have hsA' : (A+δ*v)/(3*r) ≤ sA :=
    (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hcr (by norm_num))).trans hsA
  have hR := mul_le_mul_of_nonneg_right hsR (show 0 ≤ 3*r by positivity)
  have heR : (1/(3*δ*r))*(3*r) = 1/δ := by field_simp
  rw [heR] at hR
  have hAl := (div_le_iff₀ (show 0 < 3*r by positivity)).mp hsA'
  let D := 3*r^2+1/δ+A
  have hD : 0 < D := by dsimp [D]; positivity
  have hmass : D+δ*v ≤ 3*r*(r+sR+sA) := by
    dsimp [D]
    nlinarith only [hR, hAl]
  have hmean' : D ≤ (6*r-δ)*v := by
    have hmul := mul_le_mul_of_nonneg_left
      (show r+sR+sA ≤ 2*v by linarith only [hy, hmean]) (show 0 ≤ 3*r by positivity)
    nlinarith only [hmass, hmul]
  have hslope : 0 < 6*r-δ := by
    by_contra! hnon
    exact (not_le_of_gt hD) (hmean'.trans (mul_nonpos_of_nonpos_of_nonneg hnon hv))
  let v₀ := D/(6*r-δ)
  have he : (6*r-δ)*v₀ = D := by dsimp [v₀]; field_simp [hslope.ne']
  have hv₀ : v₀ ≤ v := by
    rw [← he] at hmean'
    exact le_of_mul_le_mul_left hmean' hslope
  have hC : 2*v₀ ≤ C := by
    rcases hbudget with htable | hsearch
    · linarith only [hv₀, htable]
    · have hmul := mul_le_mul_of_nonneg_left hsearch (show 0 ≤ 3*r by positivity)
      have hδv := mul_le_mul_of_nonneg_left hv₀ hd.le
      apply le_of_mul_le_mul_left (a := 3*r) _ (by positivity)
      nlinarith only [hmul, hδv, he, hmass]
  have hlast := mul_le_mul_of_nonneg_left hC hslope.le
  have he' : (6*r-δ)*(2*v₀) = 2*D := by rw [← he]; ring
  rw [he'] at hlast
  dsimp [D] at hlast
  refine ⟨by linarith only [hslope], ?_⟩
  simp only [div_eq_mul_inv] at hlast ⊢
  nlinarith only [hlast]

/-- The physical height at the crossing stage implies the symmetric
terminal obstruction. -/
theorem cutoff_crossing_cost_floor {r δ A y child sR sA v C u : ℝ}
    (hr : 0 < r) (hd : 0 < δ) (hA : 1/δ+3*u^2/4 ≤ A) (hy : r ≤ y)
    (hc : 0 < child) (hcr : child ≤ r) (hv : 0 ≤ v)
    (hsR : 1/(3*δ*r) ≤ sR) (hsA : (A+δ*v)/(3*child) ≤ sA)
    (hmean : y+sR+sA ≤ 2*v)
    (hbudget : 2*v ≤ C ∨ r+sR+sA ≤ C) :
    δ < 6*r ∧ 3*u^2/2+4/δ+δ*C ≤ 6*r*(C-r) := by
  obtain ⟨hpositive, hcost⟩ := cutoff_crossing_tradeoff hr hd
    ((show 0 ≤ 1/δ+3*u^2/4 by positivity).trans hA) hy hc hcr hv hsR hsA hmean hbudget
  refine ⟨hpositive, ?_⟩
  simp only [div_eq_mul_inv] at hcost hA ⊢
  linarith only [hcost, hA]

end Cogentic.Randomized
