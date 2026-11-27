import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedTwoFactorFourier

open scoped BigOperators ComplexConjugate

/-- A bounded spectral multiplier acting on two square-summable factors. -/
theorem spectral_sum_norm_le {ι : Type*} (s : Finset ι) (w a b : ι → ℂ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hw : ∀ i ∈ s, ‖w i‖ ≤ ρ) :
    ‖∑ i ∈ s, w i * a i * b i‖ ≤
      ρ * (Real.sqrt (∑ i ∈ s, ‖a i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2)) := by
  calc
    _ ≤ ∑ i ∈ s, ‖w i * a i * b i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ρ * (‖a i‖ * ‖b i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Complex.norm_mul, Complex.norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_right (hw i hi) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ρ * ∑ i ∈ s, ‖a i‖ * ‖b i‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt s _ _) hρ

section FiniteGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Unnormalized Fourier transform with the character itself in the forward transform. -/
noncomputable def transform (f : G → ℂ) (χ : AddChar G ℂ) : ℂ :=
  ∑ x, f x * χ x

theorem inversion_sum (f : G → ℂ) (x : G) :
    ∑ χ : AddChar G ℂ, transform f χ * χ (-x) = (Fintype.card G : ℂ) * f x := by
  classical
  calc
    _ = ∑ χ : AddChar G ℂ, ∑ y, f y * χ (y - x) := by
      apply Finset.sum_congr rfl
      intro χ _
      simp only [transform, Finset.sum_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, mul_assoc]
    _ = ∑ y, f y * (∑ χ : AddChar G ℂ, χ (y - x)) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by simp [AddChar.sum_apply_eq_ite, sub_eq_zero, mul_ite, mul_comm]

private theorem conj_transform (f : G → ℂ) (χ : AddChar G ℂ) :
    conj (transform f χ) = ∑ x, conj (f x) * χ (-x) := by
  simp only [transform, map_sum, map_mul, AddChar.map_neg_eq_conj]

/-- Parseval's identity for the unnormalized transform. -/
theorem sum_norm_transform_sq (f : G → ℂ) :
    ∑ χ : AddChar G ℂ, ‖transform f χ‖ ^ 2 = (Fintype.card G : ℝ) * ∑ x, ‖f x‖ ^ 2 := by
  have h : ∑ χ : AddChar G ℂ, conj (transform f χ) * transform f χ =
      (Fintype.card G : ℂ) * ∑ x, conj (f x) * f x := calc
    _ = ∑ χ : AddChar G ℂ, ∑ x, conj (f x) * (transform f χ * χ (-x)) := by
      simp only [conj_transform, Finset.sum_mul, mul_assoc, mul_comm (transform f _) _]
    _ = ∑ x, conj (f x) * (∑ χ : AddChar G ℂ, transform f χ * χ (-x)) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp only [inversion_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

/-- The inverse transform restricted to a chosen finite set of frequencies. -/
noncomputable def inverseOn (s : Finset (AddChar G ℂ))
    (F : AddChar G ℂ → ℂ) (x : G) : ℂ :=
  (∑ χ ∈ s, F χ * χ (-x)) / (Fintype.card G : ℂ)

/-- The pointwise error of retaining the exceptional frequencies only.
The bound is in the two physical-space counting-measure L² norms. -/
theorem inverseOn_two_factor_error_le [DecidableEq (AddChar G ℂ)]
    (exceptional : Finset (AddChar G ℂ)) (guard : AddChar G ℂ → ℂ)
    (a b : G → ℂ) (x : G) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hguard : ∀ χ ∉ exceptional, ‖guard χ‖ ≤ ρ) :
    ‖inverseOn Finset.univ (fun χ => guard χ * transform a χ * transform b χ) x -
      inverseOn exceptional (fun χ => guard χ * transform a χ * transform b χ) x‖ ≤
      ρ * (Real.sqrt (∑ y, ‖a y‖ ^ 2) * Real.sqrt (∑ y, ‖b y‖ ^ 2)) := by
  let s := Finset.univ \ exceptional
  have hsplit (F : AddChar G ℂ → ℂ) :
      inverseOn Finset.univ F x - inverseOn exceptional F x = inverseOn s F x := by
    unfold inverseOn
    rw [← sub_div]
    congr 1
    exact (eq_sub_of_add_eq (Finset.sum_sdiff (Finset.subset_univ exceptional))).symm
  rw [hsplit]
  have hw χ (hχ : χ ∈ s) : ‖guard χ * χ (-x)‖ ≤ ρ := by
    rw [Complex.norm_mul, χ.norm_apply, mul_one]
    exact hguard χ (Finset.mem_sdiff.mp hχ).2
  have h := spectral_sum_norm_le s (fun χ => guard χ * χ (-x))
    (transform a) (transform b) ρ hρ hw
  have hsq (f : G → ℂ) :
      ∑ χ ∈ s, ‖transform f χ‖ ^ 2 ≤ (Fintype.card G : ℝ) * ∑ y, ‖f y‖ ^ 2 := by
    rw [← sum_norm_transform_sq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hn : 0 < (Fintype.card G : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hnorm : ‖(Fintype.card G : ℂ)‖ = (Fintype.card G : ℝ) := Complex.norm_natCast _
  simp only [inverseOn, Complex.norm_div, hnorm]
  apply (div_le_iff₀ hn).2
  calc
    ‖∑ χ ∈ s, (guard χ * transform a χ * transform b χ) * χ (-x)‖ =
        ‖∑ χ ∈ s, (guard χ * χ (-x)) * transform a χ * transform b χ‖ := by
      congr 1
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ρ * (Real.sqrt (∑ χ ∈ s, ‖transform a χ‖ ^ 2) *
        Real.sqrt (∑ χ ∈ s, ‖transform b χ‖ ^ 2)) := h
    _ ≤ ρ * (Real.sqrt ((Fintype.card G : ℝ) * ∑ y, ‖a y‖ ^ 2) *
        Real.sqrt ((Fintype.card G : ℝ) * ∑ y, ‖b y‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt (hsq a)) (Real.sqrt_le_sqrt (hsq b))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hρ
    _ = _ := by
      rw [Real.sqrt_mul hn.le, Real.sqrt_mul hn.le]
      ring_nf
      rw [Real.sq_sqrt hn.le]
      ring

/-- Counting-measure convolution on an additive finite abelian group. -/
noncomputable def convolution (a b : G → ℂ) (x : G) : ℂ :=
  ∑ y, a y * b (x - y)

theorem transform_convolution (a b : G → ℂ) (χ : AddChar G ℂ) :
    transform (convolution a b) χ = transform a χ * transform b χ := by
  symm
  calc
    _ = ∑ y, ∑ z, (a y * χ y) * (b z * χ z) := by
      simp only [transform]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = ∑ y, ∑ t, a y * b (t - y) * χ t := by
      refine Finset.sum_congr rfl fun y _ => Fintype.sum_equiv (Equiv.addLeft y) _ _ ?_
      intro z
      change (a y * χ y) * (b z * χ z) = a y * b (y + z - y) * χ (y + z)
      rw [add_sub_cancel_left, AddChar.map_add_eq_mul]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [transform, convolution, Finset.sum_mul]

theorem inverseOn_univ_transform (a : G → ℂ) (x : G) :
    inverseOn Finset.univ (transform a) x = a x := by
  rw [inverseOn, inversion_sum, mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- The exceptional-frequency approximation to the convolution of a guard and two
factors has pointwise error at most the off-exception guard bound times their L² norms. -/
theorem convolution_two_factor_error_le [DecidableEq (AddChar G ℂ)]
    (exceptional : Finset (AddChar G ℂ)) (guard a b : G → ℂ)
    (x : G) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hguard : ∀ χ ∉ exceptional, ‖transform guard χ‖ ≤ ρ) :
    ‖convolution (convolution guard a) b x -
      inverseOn exceptional (fun χ => transform guard χ * transform a χ * transform b χ) x‖ ≤
      ρ * (Real.sqrt (∑ y, ‖a y‖ ^ 2) * Real.sqrt (∑ y, ‖b y‖ ^ 2)) := by
  have hform : transform (convolution (convolution guard a) b) =
      fun χ => transform guard χ * transform a χ * transform b χ := by
    funext χ
    rw [transform_convolution, transform_convolution]
  rw [← hform, ← inverseOn_univ_transform (convolution (convolution guard a) b) x, hform]
  exact inverseOn_two_factor_error_le exceptional (transform guard) a b x ρ hρ hguard

end FiniteGroup

#print axioms spectral_sum_norm_le
#print axioms inversion_sum
#print axioms sum_norm_transform_sq
#print axioms inverseOn_two_factor_error_le
#print axioms convolution_two_factor_error_le

end Cogentic.RandomizedTwoFactorFourier
