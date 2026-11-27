import Mathlib.Data.Int.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Cogentic.RandomizedSectorNormBound

/-- A representative at or below the midpoint bounds the absolute value of
every representative from below. -/
theorem abs_ge_of_modEq_half {q r y : ℤ} (hhalf : 2 * r ≤ q)
    (h : y ≡ r [ZMOD q]) : r ≤ |y| := by
  by_contra! hy
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hy
  have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (m := r - y) (n := q)
    (by omega) (by omega) (Int.modEq_iff_dvd.mp h)
  omega

theorem abs_ge_of_modEq_signed_half {q y : ℤ}
    (h : (y ≡ (q - 1) / 2 [ZMOD q]) ∨ (y ≡ -((q - 1) / 2) [ZMOD q])) :
    (q - 1) / 2 ≤ |y| := by
  have hhalf : 2 * ((q - 1) / 2) ≤ q := by omega
  rcases h with h | h
  · exact abs_ge_of_modEq_half hhalf h
  · simpa only [abs_neg] using abs_ge_of_modEq_half hhalf
      (show -y ≡ (q - 1) / 2 [ZMOD q] from by simpa only [neg_neg] using h.neg)

/-- The sector width bounds the squared radius from below for either
of the two specified residues of the imaginary coefficient. -/
theorem sector_norm_lower_bound {q y : ℤ} (hq : 3 ≤ q) (hodd : Odd q)
    (hmod : (y ≡ (q - 1) / 2 [ZMOD q]) ∨ (y ≡ -((q - 1) / 2) [ZMOD q]))
    {V J R N : ℝ} (hV : 0 ≤ V) (hJ : 0 < J)
    (hsector : |(y : ℝ)| * V ≤ 2 * R / J) (hN : R ^ 2 = N) :
    V ^ 2 * ((q : ℝ) - 1) ^ 2 * J ^ 2 / 16 ≤ N := by
  have hint := abs_ge_of_modEq_signed_half hmod
  have hdist : (q : ℝ) - 1 ≤ 2 * |(y : ℝ)| := by
    have hz : q - 1 ≤ 2 * |y| := by
      rcases hodd with ⟨k, hk⟩
      omega
    exact_mod_cast hz
  have hscale := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist hV) hJ.le
  have hsector' := (le_div_iff₀ hJ).mp hsector
  have hlin : V * ((q : ℝ) - 1) * J ≤ 4 * R := by nlinarith only [hscale, hsector']
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast (show (1 : ℤ) ≤ q by omega)
  have hnonneg := mul_nonneg (mul_nonneg hV (sub_nonneg.mpr hq')) hJ.le
  have hsq := pow_le_pow_left₀ hnonneg hlin 2
  rw [← hN]
  nlinarith only [hsq]

#print axioms abs_ge_of_modEq_half
#print axioms abs_ge_of_modEq_signed_half
#print axioms sector_norm_lower_bound

end Cogentic.RandomizedSectorNormBound
