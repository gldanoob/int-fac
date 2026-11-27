import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedLatticePrimitive

theorem gcd_lift {t h z j N : ℤ} (hlift : h = z * t + j * N) (hprimitive : t.gcd j = 1) :
    t.gcd h = t.gcd N := by
  rw [hlift, Int.gcd_mul_right_add_right]
  exact Int.gcd_mul_right_right_of_gcd_eq_one hprimitive

theorem reduced_square_congruence {t h z j N u : ℤ} (hN : N ≠ 0)
    (hlift : h = z * t + j * N) (hprimitive : t.gcd j = 1)
    (hsquare : z ^ 2 ≡ u [ZMOD N]) :
    let g : ℤ := t.gcd N
    (t / g).gcd (h / g) = 1 ∧ (t / g).gcd (N / g) = 1 ∧
      (h / g) ^ 2 ≡ (t / g) ^ 2 * u [ZMOD N / g] := by
  let g : ℤ := t.gcd N
  change (t / g).gcd (h / g) = 1 ∧ (t / g).gcd (N / g) = 1 ∧
    (h / g) ^ 2 ≡ (t / g) ^ 2 * u [ZMOD N / g]
  have hgpos := Int.gcd_pos_of_ne_zero_right t hN
  have hg : g ≠ 0 := by
    simpa [g] using hgpos.ne'
  have hgt : g ∣ t := Int.gcd_dvd_left t N
  have hgN : g ∣ N := Int.gcd_dvd_right t N
  have hgcd := gcd_lift hlift hprimitive
  have hgh : g ∣ h := by
    simpa [g, hgcd] using Int.gcd_dvd_right t h
  have hlift' : h / g = z * (t / g) + j * (N / g) := by
    apply mul_right_cancel₀ hg
    calc
      h / g * g = h := Int.ediv_mul_cancel hgh
      _ = z * t + j * N := hlift
      _ = z * (t / g * g) + j * (N / g * g) := by
        rw [Int.ediv_mul_cancel hgt, Int.ediv_mul_cancel hgN]
      _ = (z * (t / g) + j * (N / g)) * g := by ring
  refine ⟨?_, Int.gcd_ediv_gcd_ediv_gcd hgpos, ?_⟩
  · simpa [g, hgcd] using
      (Int.gcd_ediv_gcd_ediv_gcd (i := t) (j := h) (by rwa [hgcd]))
  · have hline : h / g ≡ z * (t / g) [ZMOD N / g] := by
      simp [hlift']
    have hmod : N / g ∣ N := ⟨g, (Int.ediv_mul_cancel hgN).symm⟩
    calc
      (h / g) ^ 2 ≡ (z * (t / g)) ^ 2 [ZMOD N / g] := hline.pow 2
      _ = (t / g) ^ 2 * z ^ 2 := by ring
      _ ≡ (t / g) ^ 2 * u [ZMOD N / g] := (hsquare.of_dvd hmod).mul_left _

end Cogentic.RandomizedLatticePrimitive
