import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedUnitCircleMoment

open scoped BigOperators ComplexConjugate

private theorem norm_pow_sub_one_le {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) :
    ‖z ^ m - 1‖ ≤ (m : ℝ) * ‖z - 1‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      ‖z ^ (m + 1) - 1‖ = ‖z ^ m * (z - 1) + (z ^ m - 1)‖ := by
        congr 1
        rw [pow_succ]
        ring
      _ ≤ ‖z ^ m * (z - 1)‖ + ‖z ^ m - 1‖ := norm_add_le _ _
      _ ≤ ((m + 1 : ℕ) : ℝ) * ‖z - 1‖ := by
        rw [Complex.norm_mul, Complex.norm_pow, hz, one_pow, one_mul,
          Nat.cast_succ, add_mul, one_mul, add_comm]
        exact add_le_add_left ih _

private theorem norm_sub_one_sq {z : ℂ} (hz : ‖z‖ = 1) :
    ‖z - 1‖ ^ 2 = 2 * (1 - z.re) := by
  have hsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz, one_pow]
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, sub_zero] at hsq ⊢
  nlinarith only [hsq]

theorem one_sub_pow_re_le {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) :
    1 - (z ^ m).re ≤ (m : ℝ) ^ 2 * (1 - z.re) := by
  have hp : ‖z ^ m‖ = 1 := by rw [Complex.norm_pow, hz, one_pow]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_pow_sub_one_le hz m) 2
  rw [mul_pow, norm_sub_one_sq hp, norm_sub_one_sq hz] at h
  nlinarith only [h]

private theorem exists_unit_rotation (z : ℂ) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ u * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · exact ⟨1, by simpa only [Complex.ofReal_one] using
      Complex.norm_of_nonneg (show (0 : ℝ) ≤ 1 from zero_le_one), by simp [hz]⟩
  have hn := norm_ne_zero_iff.mpr hz
  refine ⟨conj z / (‖z‖ : ℂ), ?_, ?_⟩
  · rw [Complex.norm_div, Complex.norm_conj, Complex.norm_of_nonneg (norm_nonneg _),
      div_self hn]
  · rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    field_simp [Complex.ofReal_ne_zero.mpr hn]

noncomputable def weightedMean {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (f : ι → ℂ) : ℂ :=
  ∑ i ∈ s, (w i : ℂ) * f i

private theorem weightedMean_mul {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (u : ℂ) (f : ι → ℂ) :
    weightedMean s w (fun i => u * f i) = u * weightedMean s w f := by
  simp only [weightedMean, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem sum_one_sub_re {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) (f : ι → ℂ) :
    ∑ i ∈ s, w i * (1 - (f i).re) = 1 - (weightedMean s w f).re := by
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, hw]
  congr 1
  unfold weightedMean
  change _ = Complex.reAddGroupHom (∑ i ∈ s, (w i : ℂ) * f i)
  rw [map_sum]
  simp [Complex.mul_re]

/-- For a finite probability law on the unit circle, the deficit of the norm
of its power moment grows by a factor of at most the squared exponent. -/
theorem weightedMean_power_deficit_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (z : ι → ℂ) (hw : ∑ i ∈ s, w i = 1)
    (hw₀ : ∀ i ∈ s, 0 ≤ w i) (hz : ∀ i ∈ s, ‖z i‖ = 1) (m : ℕ) :
    1 - ‖weightedMean s w (fun i => z i ^ m)‖ ≤
      (m : ℝ) ^ 2 * (1 - ‖weightedMean s w z‖) := by
  obtain ⟨u, hu, hrot⟩ := exists_unit_rotation (weightedMean s w z)
  let f := fun i => u * z i
  have hf (i : ι) (hi : i ∈ s) : ‖f i‖ = 1 := by simp [f, Complex.norm_mul, hu, hz i hi]
  have hre : (weightedMean s w f).re = ‖weightedMean s w z‖ := by
    rw [weightedMean_mul, hrot, Complex.ofReal_re]
  have hnorm : ‖weightedMean s w (fun i => f i ^ m)‖ =
      ‖weightedMean s w (fun i => z i ^ m)‖ := by
    simp only [f, mul_pow, weightedMean_mul, Complex.norm_mul, Complex.norm_pow,
      hu, one_pow, one_mul]
  calc
    _ ≤ 1 - (weightedMean s w (fun i => f i ^ m)).re := by
      rw [← hnorm]
      exact sub_le_sub_left (Complex.re_le_norm _) 1
    _ = ∑ i ∈ s, w i * (1 - (f i ^ m).re) := (sum_one_sub_re s w hw _).symm
    _ ≤ (m : ℝ) ^ 2 * (∑ i ∈ s, w i * (1 - (f i).re)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (one_sub_pow_re_le (hf i hi) m) (hw₀ i hi)
    _ = _ := by rw [sum_one_sub_re s w hw f, hre]

theorem uniformMean_power_deficit_le {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (z : ι → ℂ) (hz : ∀ i ∈ s, ‖z i‖ = 1) (m : ℕ) :
    1 - ‖(∑ i ∈ s, z i ^ m) / (s.card : ℂ)‖ ≤
      (m : ℝ) ^ 2 * (1 - ‖(∑ i ∈ s, z i) / (s.card : ℂ)‖) := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  have hw : ∑ _ ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hc]
  have h := weightedMean_power_deficit_le s (fun _ => (s.card : ℝ)⁻¹) z hw
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hz m
  have hmean (f : ι → ℂ) : weightedMean s (fun _ => (s.card : ℝ)⁻¹) f =
      (∑ i ∈ s, f i) / (s.card : ℂ) := by
    simp only [weightedMean, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [← Finset.mul_sum, ← div_eq_inv_mul]
  simpa only [hmean] using h

#print axioms one_sub_pow_re_le
#print axioms weightedMean_power_deficit_le
#print axioms uniformMean_power_deficit_le

end Cogentic.RandomizedUnitCircleMoment
