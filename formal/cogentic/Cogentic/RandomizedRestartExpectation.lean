import Cogentic.RandomizedRestartBudget
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace Cogentic.Randomized

open MeasureTheory
open scoped ENNReal

/-- The charge for phases reached on one sample path. Infinite charge is allowed
before taking the expectation. -/
noncomputable def dyadicRestartCharge {Ω : Type*} (T : ℝ) (reach : ℕ → Set Ω) (ω : Ω) :
    ℝ≥0∞ :=
  ∑' j : ℕ, (reach j).indicator (fun _ ↦ ENNReal.ofReal (T * (2 : ℝ)^j)) ω

private theorem dyadicRestartCharge_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 ≤ T)
    (reach : ℕ → Set Ω) (hmeas : ∀ j, MeasurableSet (reach j)) :
    (∫⁻ ω, dyadicRestartCharge T reach ω ∂μ) =
      ∑' j : ℕ, ENNReal.ofReal (T * (2 : ℝ)^j * (μ (reach j)).toReal) := by
  unfold dyadicRestartCharge
  rw [lintegral_tsum (fun j ↦ (measurable_const.indicator (hmeas j)).aemeasurable)]
  congr 1
  funext j
  have hbudget : 0 ≤ T * (2 : ℝ)^j := by positivity
  rw [lintegral_indicator_const (hmeas j), ENNReal.ofReal_mul hbudget,
    ENNReal.ofReal_toReal (measure_ne_top μ _)]

/-- A local conditional failure rate of at most one quarter bounds the expected
charge of doubling phase budgets by twice the first budget. The local assumption
is expressed in joint-mass form, so it also covers zero-probability reach events. -/
theorem dyadicRestartCharge_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ) (hT : 0 ≤ T)
    (reach : ℕ → Set Ω) (hmeas : ∀ j, MeasurableSet (reach j))
    (hnested : ∀ j, reach (j + 1) ⊆ reach j)
    (hrate : ∀ j, μ (reach (j + 1) ∩ reach j) ≤ ENNReal.ofReal (1/4) * μ (reach j)) :
    (∫⁻ ω, dyadicRestartCharge T reach ω ∂μ) ≤ ENNReal.ofReal (2*T) := by
  let p (j : ℕ) := (μ (reach j)).toReal
  have hp0 : p 0 ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := reach 0))
    simpa [p] using h
  have hpstep (j : ℕ) : p (j + 1) ≤ (1/4 : ℝ) * p j := by
    have hr := hrate j
    rw [Set.inter_eq_left.mpr (hnested j)] at hr
    have hf : ENNReal.ofReal (1/4) * μ (reach j) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)
    have := ENNReal.toReal_mono hf hr
    simpa [p, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1/4 : ℝ))]
      using this
  have hnonneg (j : ℕ) : 0 ≤ p j := ENNReal.toReal_nonneg
  obtain ⟨hsum, hle⟩ := dyadic_restart_tail_tsum_le T hT p hnonneg
    (quarter_survival_le p hp0 hpstep)
  rw [dyadicRestartCharge_integral μ T hT reach hmeas,
    ← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ by positivity) hsum]
  exact ENNReal.ofReal_le_ofReal hle

/-- A deterministic prefix through the phases before the threshold, followed by
the same local restart guarantee, costs at most three threshold budgets in expectation. -/
theorem dyadicRestartCharge_with_prefix_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : ℝ) (ha : 0 ≤ a) (m : ℕ)
    (reach : ℕ → Set Ω) (hmeas : ∀ j, MeasurableSet (reach j))
    (hnested : ∀ j, reach (j + 1) ⊆ reach j)
    (hrate : ∀ j, μ (reach (j + 1) ∩ reach j) ≤ ENNReal.ofReal (1/4) * μ (reach j)) :
    ENNReal.ofReal (∑ j ∈ Finset.range m, a * (2 : ℝ)^j) +
      (∫⁻ ω, dyadicRestartCharge (a * (2 : ℝ)^m) reach ω ∂μ) ≤
      ENNReal.ofReal (3 * (a * (2 : ℝ)^m)) := by
  apply (add_le_add le_rfl
    (dyadicRestartCharge_integral_le μ _ (by positivity) reach hmeas hnested hrate)).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), dyadic_restart_prefix_sum]
  exact ENNReal.ofReal_le_ofReal (by linarith only [ha])

end Cogentic.Randomized
