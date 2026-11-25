import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-! Finite estimates for the root grid, discarded marks and factor-base covariance,
and exact incidence and unit-span descent from a positive Gram. -/

namespace Cogentic

open scoped BigOperators Matrix
open Matrix

variable {ι κ : Type*} [Fintype κ]

/-- Integer valuation equations with an integer target descend from real to rational
coefficients. One rational-linear functional on the reals preserves every equation. -/
theorem rational_incidence_solution (A : Matrix ι κ ℤ) (b : ι → ℤ)
    (x : κ → ℝ) (hx : ∀ i, ∑ j, (A i j : ℝ) * x j = b i) :
    ∃ c : κ → ℚ, ∀ i, ∑ j, (A i j : ℚ) * c j = b i := by
  have hn : (1 : ℝ) ∉ (⊥ : Submodule ℚ ℝ) := by simp
  obtain ⟨f, _, hf⟩ := LinearMap.exists_extend_of_notMem
    (0 : (⊥ : Submodule ℚ ℝ) →ₗ[ℚ] ℚ) hn (1 : ℚ)
  refine ⟨fun j => f (x j), fun i => ?_⟩
  have commuting (k : ℤ) (r : ℝ) : f ((k : ℝ) * r) = (k : ℚ) * f r := by
    simpa only [zsmul_eq_mul] using map_zsmul f k r
  have integers (k : ℤ) : f (k : ℝ) = (k : ℚ) := by
    simpa [hf] using commuting k 1
  simpa only [map_sum, commuting, integers] using congrArg f (hx i)

/-- A positive weighted Gram on the joint rows spans every target. The weights can
be arbitrary here because the strict positivity hypothesis already certifies the rank. -/
theorem weighted_gram_surjective [Fintype ι] (M : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (h : (M * W * M.transpose).PosDef) : Function.Surjective M.mulVec := by
  classical
  intro b
  obtain ⟨t, ht⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr h.isUnit) b
  refine ⟨W *ᵥ (M.transpose *ᵥ t), ?_⟩
  simpa only [mulVec_mulVec, Matrix.mul_assoc] using ht

/-- Clearing one common denominator produces integer incidence coefficients. -/
private theorem clear_denominators (q : κ → ℚ) :
    ∃ (d : ℤ) (z : κ → ℤ), d ≠ 0 ∧ ∀ j, (z j : ℚ) = d * q j := by
  obtain ⟨d, h⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  choose z hz using h
  exact ⟨d, z, mem_nonZeroDivisors_iff_ne_zero.mp d.property,
    fun j => by simpa only [eq_intCast, zsmul_eq_mul] using hz j⟩

/-- Every real homogeneous incidence solution is a real combination of integer
homogeneous solutions. A basis for the finite rational span of its coordinates
reduces this to finitely many rational systems, each with a common denominator. -/
theorem real_kernel_spanned_by_integer (A : Matrix ι κ ℤ) (x : κ → ℝ)
    (hx : ∀ i, ∑ j, (A i j : ℝ) * x j = 0) :
    x ∈ Submodule.span ℝ {v : κ → ℝ | ∃ z : κ → ℤ,
        (∀ i, ∑ j, A i j * z j = 0) ∧ v = fun j => (z j : ℝ)} := by
  classical
  let W := Submodule.span ℚ (Set.range x)
  let : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range x)
  let basis := Module.finBasis ℚ W
  let v (j : κ) : W := ⟨x j, Submodule.subset_span ⟨j, rfl⟩⟩
  let q (k : Fin (Module.finrank ℚ W)) (j : κ) : ℚ := basis.coord k (v j)
  have hW (i : ι) : ∑ j, (A i j) • v j = (0 : W) := by
    apply Subtype.ext
    simpa [v, zsmul_eq_mul] using hx i
  have hq (k) (i : ι) : ∑ j, (A i j : ℚ) * q k j = 0 := by
    have eq := congrArg (basis.coord k) (hW i)
    simpa [q, map_sum, map_zsmul, zsmul_eq_mul] using eq
  let S := Submodule.span ℝ {v : κ → ℝ | ∃ z : κ → ℤ,
        (∀ i, ∑ j, A i j * z j = 0) ∧ v = fun j => (z j : ℝ)}
  have hS (k) : (fun j => (q k j : ℝ)) ∈ S := by
    obtain ⟨d, z, hd, hz⟩ := clear_denominators (q k)
    have hzk (i : ι) : ∑ j, A i j * z j = 0 := by
      have e : ∑ j, (A i j : ℚ) * (z j : ℚ) = 0 := by
        simp only [hz, mul_left_comm (A i _ : ℚ) (d : ℚ), ← Finset.mul_sum,
          hq k i, mul_zero]
      exact_mod_cast e
    have hzS : (fun j => (z j : ℝ)) ∈ S := Submodule.subset_span ⟨z, hzk, rfl⟩
    have hdz := S.smul_mem (d : ℝ)⁻¹ hzS
    have eq : (d : ℝ)⁻¹ • (fun j => (z j : ℝ)) = fun j => (q k j : ℝ) := by
      funext j
      have hj : (z j : ℝ) = (d : ℝ) * (q k j : ℝ) := by exact_mod_cast hz j
      simp [Pi.smul_apply, smul_eq_mul, hj, hd]
    rwa [eq] at hdz
  have reconstruct : ∑ k, (basis k : ℝ) • (fun j => (q k j : ℝ)) = x := by
    funext j
    have e := congrArg W.subtype (basis.sum_repr (v j))
    simpa only [map_sum, map_smul, Submodule.subtype_apply, q, v,
      Finset.sum_apply, Pi.smul_apply, Module.Basis.coord_apply,
      Rat.smul_def, smul_eq_mul, mul_comm] using e
  change x ∈ S
  rw [← reconstruct]
  exact S.sum_mem fun k _ => S.smul_mem _ (hS k)

/-- Joint rows on the surviving marks. The integer block includes the intercept
and is rescaled by nonzero factors, just as in the extractor's Gram. -/
def jointRows {ν : Type*} (A : Matrix ι κ ℤ) (scale : ι → ℝ)
    (U : Matrix ν κ ℝ) : Matrix (ι ⊕ ν) κ ℝ :=
  fun row j => match row with
    | .inl i => scale i * (A i j : ℝ)
    | .inr k => U k j

/-- Positivity of the actual joint Gram yields both exact incidence descent and
real spanning by archimedean images of integer valuation relations, on the surviving rows. -/
theorem positive_gram_descent {ν : Type*} [Fintype ι] [Fintype ν]
    (A : Matrix ι κ ℤ) (scale : ι → ℝ) (hnz : ∀ i, scale i ≠ 0)
    (U : Matrix ν κ ℝ) (W : Matrix κ κ ℝ)
    (h : (jointRows A scale U * W * (jointRows A scale U).transpose).PosDef) :
    (∀ b : ι → ℤ, ∃ c : κ → ℚ, ∀ i, ∑ j, (A i j : ℚ) * c j = b i) ∧
    Submodule.span ℝ {y : ν → ℝ | ∃ z : κ → ℤ, (∀ i, ∑ j, A i j * z j = 0) ∧
        y = U *ᵥ (fun j => (z j : ℝ))} = ⊤ := by
  classical
  let M := jointRows A scale U
  have surj := weighted_gram_surjective M W h
  have block (x : κ → ℝ) (i : ι) :
      (M *ᵥ x) (.inl i) = scale i * ∑ j, (A i j : ℝ) * x j := by
    simp only [M, Matrix.mulVec, dotProduct, jointRows, Finset.mul_sum, mul_assoc]
  constructor
  · intro b
    obtain ⟨x, eq⟩ := surj (Sum.elim (fun i => scale i * (b i : ℝ)) (fun _ => 0))
    apply rational_incidence_solution A b x
    intro i
    apply mul_left_cancel₀ (hnz i)
    simpa only [← block, Sum.elim_inl] using congrFun eq (.inl i)
  · let S := Submodule.span ℝ {y : ν → ℝ | ∃ z : κ → ℤ,
          (∀ i, ∑ j, A i j * z j = 0) ∧ y = U *ᵥ (fun j => (z j : ℝ))}
    apply top_unique
    intro y _
    obtain ⟨x, eq⟩ := surj (Sum.elim (fun _ => 0) y)
    have neutral (i : ι) : ∑ j, (A i j : ℝ) * x j = 0 := by
      have hi := congrFun eq (.inl i)
      rw [block] at hi
      exact (mul_eq_zero.mp hi).resolve_left (hnz i)
    have image : U *ᵥ x = y := funext fun k => congrFun eq (.inr k)
    have lifted := real_kernel_spanned_by_integer A x neutral
    have span_le : Submodule.span ℝ {v : κ → ℝ | ∃ z : κ → ℤ,
        (∀ i, ∑ j, A i j * z j = 0) ∧ v = fun j => (z j : ℝ)} ≤ S.comap U.mulVecLin := by
      apply Submodule.span_le.mpr
      rintro _ ⟨z, hz, rfl⟩
      exact Submodule.subset_span ⟨z, hz, rfl⟩
    rw [← image]
    exact span_le lifted

/-- Restoring all clean rows and marks preserves the extractor conclusions. Extra
valuation rows vanish on retained marks, and the prescribed target is supported on
retained rows. No condition is imposed on either matrix at an extra mark. -/
theorem positive_gram_full_descent {ν ι' κ' : Type*} [Fintype ι] [Fintype ν] [Fintype κ']
    (A : Matrix ι κ ℤ) (scale : ι → ℝ) (hnz : ∀ i, scale i ≠ 0)
    (U : Matrix ν κ ℝ) (W : Matrix κ κ ℝ)
    (h : (jointRows A scale U * W * (jointRows A scale U).transpose).PosDef)
    (A' : Matrix (ι ⊕ ι') (κ ⊕ κ') ℤ) (U' : Matrix ν (κ ⊕ κ') ℝ)
    (keepA : ∀ i j, A' (.inl i) (.inl j) = A i j)
    (deleted : ∀ i j, A' (.inr i) (.inl j) = 0)
    (keepU : ∀ k j, U' k (.inl j) = U k j) :
    (∀ b : ι → ℤ, ∃ c : κ ⊕ κ' → ℚ, ∀ i, ∑ j, (A' i j : ℚ) * c j = (Sum.elim b 0 i : ℤ)) ∧
    Submodule.span ℝ {y : ν → ℝ | ∃ z : κ ⊕ κ' → ℤ, (∀ i, ∑ j, A' i j * z j = 0) ∧
        y = U' *ᵥ (fun j => (z j : ℝ))} = ⊤ := by
  obtain ⟨target, span⟩ := positive_gram_descent A scale hnz U W h
  constructor
  · intro b
    obtain ⟨c, hc⟩ := target b
    refine ⟨Sum.elim c 0, ?_⟩
    rintro (i | i) <;> simp [Fintype.sum_sum_type, keepA, deleted, hc]
  · rw [← top_le_iff, ← span]
    apply Submodule.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    apply Submodule.subset_span
    refine ⟨Sum.elim z 0, ?_, ?_⟩
    · rintro (i | i) <;> simp [Fintype.sum_sum_type, keepA, deleted, hz]
    · funext k
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, keepU]

/-- The mean logarithmic distance over a normalized positive grid inherits a
pointwise distance interval, including its lower endpoint. -/
private theorem mean_log_range {β : Type*} [Fintype β] (mass dist : β → ℝ)
    (l h : ℝ) (hl : 0 < l) (hm : ∀ a, 0 ≤ mass a) (hs : ∑ a, mass a = 1)
    (hb : ∀ a, l ≤ dist a ∧ dist a ≤ h) :
    Real.log l ≤ ∑ a, mass a * Real.log (dist a) ∧
    ∑ a, mass a * Real.log (dist a) ≤ Real.log h := by
  constructor
  · calc
      Real.log l = ∑ a, mass a * Real.log l := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (Real.log_le_log hl (hb a).1) (hm a)
  · calc
      _ ≤ ∑ a, mass a * Real.log h := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (Real.log_le_log (hl.trans_le (hb a).1) (hb a).2) (hm a)
      _ = _ := by rw [← Finset.sum_mul, hs, one_mul]

/-- Entry bounds on the actual mean-log differences. The root marks lie a distance
between w and 2w to the right of their own target; other targets are gap-separated. -/
theorem root_grid_log_entries {α : Type*} {β : Option α → Type*} [∀ k, Fintype (β k)]
    (root : α → ℝ) (point mass : (k : Option α) → β k → ℝ) (w gap : ℝ)
    (hw : 0 < w) (hnarrow : 2*w ≤ gap/2) (hgap : gap ≤ 1/2)
    (hroot : ∀ i, 0 ≤ root i ∧ root i ≤ 1/2)
    (hsep : ∀ i j, i ≠ j → gap ≤ |root i - root j|)
    (hbaseline : ∀ a, 3/4 ≤ point none a ∧ point none a ≤ 1)
    (hmark : ∀ i a, root i+w ≤ point (some i) a ∧ point (some i) a ≤ root i+2*w)
    (hmass : ∀ k a, 0 ≤ mass k a) (hnorm : ∀ k, ∑ a, mass k a = 1) :
    let mean := fun k j => ∑ a, mass k a * Real.log |point k a - root j|
    (∀ i, Real.log (1/4) - Real.log (2*w) ≤ mean none i - mean (some i) i) ∧
    (∀ i j, i ≠ j → |mean none j - mean (some i) j| ≤ -Real.log (gap/2)) := by
  dsimp only
  have base (a : β none) (j : α) : 1/4 ≤ |point none a - root j| ∧ |point none a - root j| ≤ 1 := by
    obtain ⟨lo, hi⟩ := hbaseline a
    obtain ⟨rl, rh⟩ := hroot j
    rw [abs_of_nonneg (by linarith : 0 ≤ point none a - root j)]
    constructor <;> linarith
  constructor
  · intro i
    have b := (mean_log_range _ _ _ _ (by norm_num : (0:ℝ)<1/4)
      (hmass none) (hnorm none) (fun a => base a i)).1
    have own (a : β (some i)) : w ≤ |point (some i) a - root i| ∧ |point (some i) a - root i| ≤ 2*w := by
      obtain ⟨lo, hi⟩ := hmark i a
      rw [abs_of_nonneg (by linarith : 0 ≤ point (some i) a - root i)]
      constructor <;> linarith
    exact sub_le_sub b ((mean_log_range _ _ _ _ hw (hmass (some i)) (hnorm (some i)) own).2)
  · intro i j hij
    have hg : 0 < gap/2 := by linarith
    have base' (a : β none) : gap/2 ≤ |point none a - root j| ∧ |point none a - root j| ≤ 1 :=
      ⟨le_trans (by linarith) (base a j).1, (base a j).2⟩
    have other (a : β (some i)) : gap/2 ≤ |point (some i) a - root j| ∧ |point (some i) a - root j| ≤ 1 := by
      obtain ⟨lo, hi⟩ := hmark i a
      have ri := hroot i
      have rj := hroot j
      have sep := hsep i j hij
      have tri := abs_sub_le (root i) (point (some i) a) (root j)
      rw [abs_of_nonpos (by linarith : root i - point (some i) a ≤ 0)] at tri
      exact ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    have b := mean_log_range _ _ _ _ hg (hmass none) (hnorm none) base'
    have t := mean_log_range _ _ _ _ hg (hmass (some i)) (hnorm (some i)) other
    rw [Real.log_one] at b t
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Sparse lost marks have a controlled finite-prime Gram perturbation. Only the
support bound per mark and weighted diagonal losses per surviving coordinate enter. -/
theorem sparse_discard_energy {α β : Type*} [Fintype α] [Fintype β]
    (weight : α → ℝ) (Z : α → β → ℝ) (support : α → Finset β) (v : β → ℝ)
    (k : ℕ) (δ : ℝ) (hw : ∀ a, 0 ≤ weight a)
    (hk : ∀ a, (support a).card ≤ k) (hz : ∀ a i, i ∉ support a → Z a i = 0)
    (hdiag : ∀ i, ∑ a, weight a * (Z a i)^2 ≤ δ) :
    ∑ a, weight a * (∑ i, Z a i * v i)^2 ≤ k * δ * ∑ i, (v i)^2 := by
  classical
  have one (a : α) : (∑ i, Z a i * v i)^2 ≤ k * ∑ i, (Z a i)^2 * (v i)^2 := by
    have sm : ∑ i ∈ support a, Z a i * v i = ∑ i, Z a i * v i := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp [hz a i hi]
    have ss : ∑ i ∈ support a, (Z a i * v i)^2 = ∑ i, (Z a i)^2 * (v i)^2 := by
      simp_rw [mul_pow]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp [hz a i hi]
    have cs := Finset.sum_mul_sq_le_sq_mul_sq (support a) (fun _ => (1 : ℝ)) (fun i => Z a i * v i)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sm, ss] at cs
    exact cs.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk a)
      (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  calc
    _ ≤ ∑ a, weight a * (k * ∑ i, (Z a i)^2 * (v i)^2) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (one a) (hw a)
    _ = k * ∑ i, (∑ a, weight a * (Z a i)^2) * (v i)^2 := by
      simp_rw [Finset.mul_sum, Finset.sum_mul, mul_left_comm (weight _) (k : ℝ), mul_assoc]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ k * ∑ i, δ * (v i)^2 := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hdiag i) (sq_nonneg _)) (by positivity)
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

/-- Projecting away the exact norm direction removes the leading rank-one
covariance correction. Only the squared error in its direction survives. -/
theorem perpendicular_covariance {α : Type*} [Fintype α]
    (v c w : α → ℝ) (k δ : ℝ) (perp : ∑ i, w i * v i = 0)
    (approx : ∑ i, (c i - k * w i)^2 ≤ δ) :
    (∑ i, c i * v i)^2 ≤ δ * ∑ i, (v i)^2 := by
  have eq : ∑ i, (c i - k * w i) * v i = ∑ i, c i * v i := by
    simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, perp, mul_zero, sub_zero]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => c i - k*w i) v
  rw [eq] at cs
  exact cs.trans (mul_le_mul_of_nonneg_right approx (Finset.sum_nonneg fun i _ => sq_nonneg _))

/-- A weighted entrywise remainder affects only the energy on the indexed block.
With weights p^(-α/2), the coefficient is the sum of p^(-α) times the entry tolerance. -/
theorem covariance_remainder {α : Type*} [Fintype α]
    (E : Matrix α α ℝ) (v w : α → ℝ) (ε : ℝ) (he : 0 ≤ ε)
    (entry : ∀ i j, |E i j| ≤ ε * w i * w j) :
    |∑ i, ∑ j, v i * E i j * v j| ≤ ε * (∑ i, (w i)^2) * ∑ i, (v i)^2 := by
  have one (i j) : |v i * E i j * v j| ≤ ε * (w i * |v i|) * (w j * |v j|) := by
    calc
      _ = |v i| * |E i j| * |v j| := by simp only [abs_mul]
      _ ≤ |v i| * (ε * w i * w j) * |v j| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (entry i j) (abs_nonneg _)) (abs_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∑ i, |∑ j, v i * E i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |v i * E i j * v j| := Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, ε * (w i * |v i|) * (w j * |v j|) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => one i j
    _ = ε * (∑ i, w i * |v i|)^2 := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    _ ≤ _ := by
      have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w (fun i => |v i|)
      simp only [sq_abs] at cs
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left cs he

/-- Separate the finite diagonal energy from cancellation between the archimedean
score and the finite mean. This gives the 1/(128u) coefficient without dividing. -/
theorem covariance_energy {α : Type*} [Fintype α]
    (p g m : α → ℝ) (F u Q : ℝ) (hw : ∀ a, 0 ≤ p a) (hF : 0 ≤ F) (hu : 1 ≤ u)
    (mean_energy : ∑ a, p a * (m a)^2 ≤ 12*u*F)
    (finite_block : 4 * (∑ a, p a * (g a + m a)^2) + 3*F ≤ 4*Q) :
    64*u*F + ∑ a, p a * (g a)^2 ≤ 128*u*Q := by
  let T := ∑ a, p a * (g a + m a)^2
  have score : ∑ a, p a * (g a)^2 ≤ 2*T + 2*∑ a, p a * (m a)^2 := by
    simp only [T, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    have point : (g a)^2 ≤ 2*(g a + m a)^2 + 2*(m a)^2 := by
      nlinarith [sq_nonneg (g a + 2*m a)]
    nlinarith [mul_le_mul_of_nonneg_left point (hw a)]
  have tpos : 0 ≤ T := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  change 4*T+3*F ≤ 4*Q at finite_block
  nlinarith [mul_le_mul_of_nonneg_left finite_block (by linarith : 0 ≤ 32*u),
    mul_nonneg (sub_nonneg.mpr hu) tpos, mul_nonneg (by linarith : 0 ≤ u) hF]

/-- The cumulative peeling inequality uses the error at each removed row's first
deletion. It bounds the entire newly deleted mass, even across several rounds. -/
theorem peeling_mass_bound {α : Type*} (S D : Finset α) (w : α → ℝ) (E : α → α → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hw : ∀ i, 0 ≤ w i)
    (lost : ∀ i ∈ S, δ * (w i)^2 ≤ 2 * ∑ j ∈ D, w i * w j * |E i j|) :
    δ^2 * (∑ i ∈ S, (w i)^2) ≤
      4 * (∑ j ∈ D, (w j)^2) * ∑ i ∈ S, ∑ j ∈ D, (E i j)^2 := by
  classical
  let u := ∑ i ∈ S, (w i)^2
  let v := ∑ i ∈ D, (w i)^2
  let t := ∑ i ∈ S, ∑ j ∈ D, w i * w j * |E i j|
  let e := ∑ i ∈ S, ∑ j ∈ D, (E i j)^2
  have hu : 0 ≤ u := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hv : 0 ≤ v := Finset.sum_nonneg fun i _ => sq_nonneg _
  have he : 0 ≤ e := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have ht : 0 ≤ t := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hw i) (hw j)) (abs_nonneg _)
  have loss : δ*u ≤ 2*t := by simpa only [u, t, Finset.mul_sum] using Finset.sum_le_sum lost
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (S ×ˢ D)
    (fun p => w p.1 * w p.2) (fun p => |E p.1 p.2|)
  have sumProduct : ∑ i ∈ S, ∑ j ∈ D, (w i * w j)^2 = u*v := by
    simp only [u, v, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  simp only [Finset.sum_product, sq_abs, sumProduct] at cs
  change t^2 ≤ u*v*e at cs
  change δ^2*u ≤ 4*v*e
  rcases hu.eq_or_lt with hu | hu
  · rw [← hu, mul_zero]
    positivity
  · have sq := mul_self_le_mul_self (mul_nonneg hδ hu.le) loss
    apply le_of_mul_le_mul_left (a := u) _ hu
    nlinarith only [sq, cs]

end Cogentic
