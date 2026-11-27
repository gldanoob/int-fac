import Cogentic.RandomizedPrimitiveQuadraticRoot
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.RingTheory.Coprime.Lemmas

namespace Cogentic.RandomizedQuadraticCoefficientCongruence

open RandomizedPrimitiveQuadraticRoot (formValue)

/-- A divisor of both the second coordinate and the represented value
must divide the leading coefficient at a primitive vector. -/
theorem dvd_lead_of_dvd_value {m b c j k s : ℤ}
    (hjk : j.gcd k = 1) (hsk : s ∣ k) (hQ : s ∣ formValue m b c j k) :
    s ∣ m := by
  have hcop : IsCoprime s j :=
    (Int.isCoprime_iff_gcd_eq_one.mpr hjk).symm.of_isCoprime_of_dvd_left hsk
  apply (show IsCoprime s (j ^ 2) from hcop.pow_right).dvd_of_dvd_mul_right
  have hcross : s ∣ (b * j) * k := dvd_mul_of_dvd_right hsk _
  have htail : s ∣ (c * k) * k := dvd_mul_of_dvd_right hsk _
  have h := dvd_sub hQ (dvd_add hcross htail)
  convert h using 1
  unfold formValue
  ring

/-- At fixed first two coefficients, divisibility by a modulus coprime
to the second coordinate determines at most one trailing residue. -/
theorem trailing_modEq_of_dvd_values {m b c c' j k t : ℤ}
    (htk : t.gcd k = 1) (hQ : t ∣ formValue m b c j k) (hQ' : t ∣ formValue m b c' j k) :
    c ≡ c' [ZMOD t] := by
  apply Int.modEq_iff_dvd.mpr
  have hcop : IsCoprime t (k ^ 2) := (Int.isCoprime_iff_gcd_eq_one.mpr htk).pow_right
  apply hcop.dvd_of_dvd_mul_right
  convert dvd_sub hQ' hQ using 1
  unfold formValue
  ring

theorem coefficient_congruences_of_product_dvd {m b c c' j k s t : ℤ}
    (hjk : j.gcd k = 1) (hsk : s ∣ k) (htk : t.gcd k = 1)
    (hQ : s * t ∣ formValue m b c j k) (hQ' : s * t ∣ formValue m b c' j k) :
    s ∣ m ∧ c ≡ c' [ZMOD t] := by
  have hs : s ∣ s * t := dvd_mul_right s t
  have ht : t ∣ s * t := dvd_mul_left t s
  exact ⟨dvd_lead_of_dvd_value hjk hsk (hs.trans hQ),
    trailing_modEq_of_dvd_values htk (ht.trans hQ) (ht.trans hQ')⟩

/-- In a half-open interval of length `hi - lo`, the trailing coefficient
has at most `(hi - lo) / t + 1` admissible values. -/
theorem trailing_coefficient_card_le {m b j k t lo hi : ℤ}
    (htk : t.gcd k = 1) (ht : 0 < t) (hinterval : lo ≤ hi) :
    (((Finset.Ico lo hi).filter (fun c => t ∣ formValue m b c j k)).card : ℚ) ≤
      ((hi : ℚ) - lo) / t + 1 := by
  let admissible := (Finset.Ico lo hi).filter (fun c => t ∣ formValue m b c j k)
  change (admissible.card : ℚ) ≤ _
  have hlength : 0 ≤ ((hi : ℚ) - lo) / t :=
    div_nonneg (sub_nonneg.mpr (by exact_mod_cast hinterval)) (by exact_mod_cast ht.le)
  rcases admissible.eq_empty_or_nonempty with hempty | ⟨c₀, hc₀⟩
  · simp only [hempty, Finset.card_empty, Nat.cast_zero]
    linarith only [hlength]
  have hsubset : admissible ⊆ (Finset.Ico lo hi).filter (fun c => c ≡ c₀ [ZMOD t]) := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1,
      trailing_modEq_of_dvd_values htk (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hc₀).2⟩
  let x : ℚ := ((lo : ℚ) - c₀) / t
  let y : ℚ := ((hi : ℚ) - c₀) / t
  have hxy : x ≤ y := div_le_div_of_nonneg_right
    (sub_le_sub_right (by exact_mod_cast hinterval) _) (by exact_mod_cast ht.le)
  have heq := Int.Ico_filter_modEq_card lo hi ht c₀
  change (_ : ℤ) = max (⌈y⌉ - ⌈x⌉) 0 at heq
  rw [max_eq_left (sub_nonneg.mpr (Int.ceil_le_ceil hxy))] at heq
  have heq' : (((Finset.Ico lo hi).filter (fun c => c ≡ c₀ [ZMOD t])).card : ℚ) =
      (⌈y⌉ : ℚ) - ⌈x⌉ := by exact_mod_cast heq
  have hcard : (admissible.card : ℚ) ≤ (⌈y⌉ : ℚ) - ⌈x⌉ := by
    rw [← heq']
    exact_mod_cast Finset.card_le_card hsubset
  have hdiff : y - x = ((hi : ℚ) - lo) / t := by dsimp [x, y]; rw [← sub_div]; ring
  linarith only [hcard, hdiff, Int.le_ceil x, Int.ceil_lt_add_one y]

#print axioms dvd_lead_of_dvd_value
#print axioms trailing_modEq_of_dvd_values
#print axioms coefficient_congruences_of_product_dvd
#print axioms trailing_coefficient_card_le

end Cogentic.RandomizedQuadraticCoefficientCongruence
