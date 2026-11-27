import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Coordinatewise cutoff maxima and the finite Euclidean integral bound. -/

namespace Cogentic.Randomized

open MeasureTheory

private theorem euclidean_norm_le_of_nonneg_le {ι : Type*} [Fintype ι]
    {u v : EuclideanSpace ℝ ι} (hu : ∀ i, 0 ≤ u i) (huv : ∀ i, u i ≤ v i) :
    ‖u‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum fun i _ ↦ by
    rw [Real.norm_of_nonneg (hu i), Real.norm_of_nonneg ((hu i).trans (huv i))]
    exact pow_le_pow_left₀ (hu i) (huv i) 2

private theorem euclidean_integral_apply {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {g : Ω → EuclideanSpace ℝ ι} (hg : Integrable g μ) (i : ι) :
    (∫ t, g t ∂μ) i = ∫ t, g t i ∂μ :=
  (PiLp.proj 2 (fun _ : ι ↦ ℝ) i : EuclideanSpace ℝ ι →L[ℝ] ℝ).integral_comp_comm hg |>.symm

/-- Each coordinate may take its maximum at a different cutoff. The common
integrand envelope and the cutoff-independent error are both charged in ℓ². -/
theorem l2_cutoff_sup_le {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} (C : Finset κ) (hC : C.Nonempty) (A : κ → ι → ℂ)
    (f : κ → ι → Ω → ℂ) (g : Ω → EuclideanSpace ℝ ι) (err : EuclideanSpace ℝ ι)
    (hg : Integrable g μ)
    (hdom : ∀ k ∈ C, ∀ i, ∀ᵐ t ∂μ, ‖f k i t‖ ≤ g t i)
    (herr : ∀ k ∈ C, ∀ i, ‖A k i - ∫ t, f k i t ∂μ‖ ≤ err i) :
    ‖(WithLp.toLp 2 (fun i ↦ C.sup' hC (fun k ↦ ‖A k i‖)) : EuclideanSpace ℝ ι)‖ ≤
      (∫ t, ‖g t‖ ∂μ) + ‖err‖ := by
  classical
  let u : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i ↦ C.sup' hC fun k ↦ ‖A k i‖
  let v : EuclideanSpace ℝ ι := ∫ t, g t ∂μ
  have hcoord (i : ι) : Integrable (fun t ↦ g t i) μ :=
    (PiLp.proj 2 (fun _ : ι ↦ ℝ) i : EuclideanSpace ℝ ι →L[ℝ] ℝ).integrable_comp hg
  have hu (i : ι) : 0 ≤ u i := by
    change 0 ≤ C.sup' hC (fun k ↦ ‖A k i‖)
    obtain ⟨k, hk⟩ := hC
    exact (norm_nonneg (A k i)).trans (Finset.le_sup' (fun j ↦ ‖A j i‖) hk)
  have huv (i : ι) : u i ≤ (v + err) i := by
    change C.sup' hC (fun k ↦ ‖A k i‖) ≤ v i + err i
    apply Finset.sup'_le
    intro k hk
    rw [show v i = ∫ t, g t i ∂μ from euclidean_integral_apply hg i]
    calc
      ‖A k i‖ = ‖(∫ t, f k i t ∂μ) + (A k i - ∫ t, f k i t ∂μ)‖ :=
        congrArg norm (by abel)
      _ ≤ ‖∫ t, f k i t ∂μ‖ + ‖A k i - ∫ t, f k i t ∂μ‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (norm_integral_le_of_norm_le (hcoord i) (hdom k hk i)) (herr k hk i)
  change ‖u‖ ≤ _
  calc
    ‖u‖ ≤ ‖v + err‖ := euclidean_norm_le_of_nonneg_le hu huv
    _ ≤ ‖v‖ + ‖err‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_integral_le_integral_norm (μ := μ) g) le_rfl

/-- Use the pointwise coordinatewise maximum inside the integral. The only
integrability assumption is on this finite real vector. -/
theorem l2_cutoff_sup_integral_sup_le {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} (C : Finset κ) (hC : C.Nonempty) (A : κ → ι → ℂ)
    (f : κ → ι → Ω → ℂ) (err : EuclideanSpace ℝ ι)
    (hg : Integrable (fun t ↦ (WithLp.toLp 2
      (fun i ↦ C.sup' hC (fun k ↦ ‖f k i t‖)) : EuclideanSpace ℝ ι)) μ)
    (herr : ∀ k ∈ C, ∀ i, ‖A k i - ∫ t, f k i t ∂μ‖ ≤ err i) :
    ‖(WithLp.toLp 2 (fun i ↦ C.sup' hC (fun k ↦ ‖A k i‖)) : EuclideanSpace ℝ ι)‖ ≤
      (∫ t, ‖(WithLp.toLp 2 (fun i ↦ C.sup' hC (fun k ↦ ‖f k i t‖)) :
        EuclideanSpace ℝ ι)‖ ∂μ) + ‖err‖ :=
  l2_cutoff_sup_le C hC A f _ err hg
    (fun _k hk i ↦ Filter.Eventually.of_forall fun t ↦ Finset.le_sup' (fun k ↦ ‖f k i t‖) hk) herr

/-- Perron cutoffs multiply the same Mellin vector by scalar factors. A single
integrable envelope for those factors controls the coordinatewise cutoff maxima. -/
theorem l2_perron_sup_le {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} (C : Finset κ) (hC : C.Nonempty) (A : κ → ι → ℂ)
    (D : Ω → EuclideanSpace ℂ ι) (factor : κ → Ω → ℂ) (weight : Ω → ℝ)
    (err : EuclideanSpace ℝ ι) (hw : ∀ t, 0 ≤ weight t)
    (hg : Integrable (fun t ↦ weight t • (WithLp.toLp 2
      (fun i ↦ ‖D t i‖) : EuclideanSpace ℝ ι)) μ)
    (hfactor : ∀ k ∈ C, ∀ᵐ t ∂μ, ‖factor k t‖ ≤ weight t)
    (herr : ∀ k ∈ C, ∀ i, ‖A k i - ∫ t, factor k t * D t i ∂μ‖ ≤ err i) :
    ‖(WithLp.toLp 2 (fun i ↦ C.sup' hC (fun k ↦ ‖A k i‖)) : EuclideanSpace ℝ ι)‖ ≤
      (∫ t, weight t * ‖D t‖ ∂μ) + ‖err‖ := by
  let U (t : Ω) : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i ↦ ‖D t i‖
  have hU (t : Ω) : ‖U t‖ = ‖D t‖ := by
    simp only [U, EuclideanSpace.norm_eq, norm_norm]
  have hnorm (t : Ω) : ‖weight t • U t‖ = weight t * ‖D t‖ := by
    rw [norm_smul, Real.norm_of_nonneg (hw t), hU]
  have hdom (k : κ) (hk : k ∈ C) (i : ι) :
      ∀ᵐ t ∂μ, ‖factor k t * D t i‖ ≤ (weight t • U t) i := by
    filter_upwards [hfactor k hk] with t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)
  simpa only [hnorm] using l2_cutoff_sup_le C hC A
    (fun k i t ↦ factor k t * D t i) (fun t ↦ weight t • U t) err hg hdom herr

/-- Half-integer cutoffs on a vertical line share the same kernel. Supply the
uniform scalar Perron truncation error after the progression transform. -/
theorem l2_halfInteger_perron_sup_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} (C : Finset ℕ) (hC : C.Nonempty) (A : ℕ → ι → ℂ)
    (D : Ω → EuclideanSpace ℂ ι) (s kernel : Ω → ℂ) (err : EuclideanSpace ℝ ι)
    {c H : ℝ} (hH : 0 ≤ H) (hs : ∀ t, (s t).re = c)
    (hcut : ∀ m ∈ C, ((m : ℝ) + 1 / 2) ^ c ≤ H)
    (hg : Integrable (fun t ↦ (H * ‖kernel t‖) • (WithLp.toLp 2
      (fun i ↦ ‖D t i‖) : EuclideanSpace ℝ ι)) μ)
    (herr : ∀ m ∈ C, ∀ i,
      ‖A m i - ∫ t, ((((m : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s t * kernel t) * D t i ∂μ‖ ≤ err i) :
    ‖(WithLp.toLp 2 (fun i ↦ C.sup' hC (fun m ↦ ‖A m i‖)) : EuclideanSpace ℝ ι)‖ ≤
      (∫ t, (H * ‖kernel t‖) * ‖D t‖ ∂μ) + ‖err‖ := by
  apply l2_perron_sup_le C hC A D (fun m t ↦ (((m : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s t * kernel t)
    (fun t ↦ H * ‖kernel t‖) err (fun t ↦ mul_nonneg hH (norm_nonneg _)) hg _ herr
  intro m hm
  filter_upwards with t
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hs t]
  exact mul_le_mul_of_nonneg_right (hcut m hm) (norm_nonneg _)

end Cogentic.Randomized
