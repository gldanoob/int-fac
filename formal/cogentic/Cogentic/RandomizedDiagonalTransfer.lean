import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized

open Filter Real Asymptotics
open scoped BigOperators Topology

/-- A centered first absolute moment bound controls the sum of proxy means
under the same conditional probability law. -/
theorem proxy_firstMoment_le_of_centered {ι Ω : Type*}
    (points : Finset ι) (outcomes : Finset Ω) (weight : Ω → ℝ) (proxy : ι → Ω → ℝ)
    {ε μ : ℝ} (hw : ∀ ω ∈ outcomes, 0 ≤ weight ω)
    (hprob : (∑ ω ∈ outcomes, weight ω) = 1)
    (hcenter : (∑ ω ∈ outcomes, weight ω * |(∑ i ∈ points, proxy i ω) - μ|) ≤ ε * μ) :
    (∑ i ∈ points, ∑ ω ∈ outcomes, weight ω * proxy i ω) ≤ (1 + ε) * μ := by
  calc
    _ = ∑ ω ∈ outcomes, weight ω * (∑ i ∈ points, proxy i ω) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ ω ∈ outcomes, weight ω * (μ + |(∑ i ∈ points, proxy i ω) - μ|) :=
      Finset.sum_le_sum fun ω hω ↦ mul_le_mul_of_nonneg_left
        (by linarith only [le_abs_self ((∑ i ∈ points, proxy i ω) - μ)]) (hw ω hω)
    _ = μ + ∑ ω ∈ outcomes, weight ω * |(∑ i ∈ points, proxy i ω) - μ| := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hprob, one_mul]
    _ ≤ _ := by linarith only [hcenter]

/-- For nonnegative scores and proxies, their squared residual has diagonal
bounded by the two first moments times their respective caps. The outcome
weights can be those of the probability law after conditioning. -/
theorem diagonal_residual_le {ι Ω : Type*} (points : Finset ι) (outcomes : Finset Ω)
    (weight : Ω → ℝ) (f proxy : ι → Ω → ℝ) {F P C μ : ℝ}
    (hw : ∀ ω ∈ outcomes, 0 ≤ weight ω)
    (hf : ∀ i ∈ points, ∀ ω ∈ outcomes, 0 ≤ f i ω ∧ f i ω ≤ F)
    (hp : ∀ i ∈ points, ∀ ω ∈ outcomes, 0 ≤ proxy i ω ∧ proxy i ω ≤ P)
    (hP : 0 ≤ P) (hμ : 0 < μ)
    (hfirst : (∑ i ∈ points, ∑ ω ∈ outcomes, weight ω * f i ω) = μ)
    (hproxy : (∑ i ∈ points, ∑ ω ∈ outcomes, weight ω * proxy i ω) ≤ C * μ) :
    (∑ i ∈ points, ∑ ω ∈ outcomes, weight ω * (f i ω - proxy i ω)^2) / μ^2 ≤
      (F + C*P) / μ := by
  have hpoint (i) (hi : i ∈ points) (ω) (hω : ω ∈ outcomes) :
      (f i ω - proxy i ω)^2 ≤ F * f i ω + P * proxy i ω := by
    obtain ⟨hfn, hfc⟩ := hf i hi ω hω
    obtain ⟨hpn, hpc⟩ := hp i hi ω hω
    nlinarith only [mul_nonneg hfn hpn, mul_le_mul_of_nonneg_right hfc hfn,
      mul_le_mul_of_nonneg_right hpc hpn]
  have hsum :
      (∑ i ∈ points, ∑ ω ∈ outcomes, weight ω * (f i ω - proxy i ω)^2) ≤
        F * μ + P * (C * μ) := by
    calc
      _ ≤ ∑ i ∈ points, ∑ ω ∈ outcomes, (F * (weight ω * f i ω) + P * (weight ω * proxy i ω)) :=
        Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun ω hω ↦
          (mul_le_mul_of_nonneg_left (hpoint i hi ω hω) (hw ω hω)).trans_eq (by ring)
      _ = F * (∑ i ∈ points, ∑ ω ∈ outcomes, weight ω * f i ω) +
          P * (∑ i ∈ points, ∑ ω ∈ outcomes, weight ω * proxy i ω) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by
        rw [hfirst]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hproxy hP)
  apply (div_le_iff₀ (sq_pos_of_pos hμ)).mpr
  calc
    _ ≤ F * μ + P * (C * μ) := hsum
    _ = _ := by field_simp

/-- A positive fixed exponential mean margin absorbs both the proxy envelope
and the desired (D^{-4A}) relative error. All parameters are fixed before
taking the limit in (D). -/
theorem diagonal_exp_margin_tendsto_zero {A Λ μ diag : ℝ → ℝ}
    {η c C K C₀ : ℝ} (hη : 0 < η) (hc : 0 < c) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hC₀ : 0 ≤ C₀)
    (hA : ∀ᶠ D in atTop, 0 ≤ A D ∧ A D ≤ C * (log D)^3)
    (hΛ : ∀ᶠ D in atTop, c * D * log D ≤ Λ D)
    (hμ : ∀ᶠ D in atTop, exp (η * Λ D) ≤ μ D)
    (hdiag : ∀ᶠ D in atTop,
      0 ≤ diag D ∧ diag D ≤ C₀ * exp (K * A D * (log D)^2) / μ D) :
    Tendsto (fun D ↦ diag D * exp (4 * A D * log D)) atTop (𝓝 0) := by
  let δ := η*c/2
  have hδ : 0 < δ := by positivity
  let B := (K+4)*C
  have hB : 0 ≤ B := by positivity
  have hlog := (isLittleO_iff.mp (isLittleO_log_rpow_rpow_atTop 5
    (show (0:ℝ) < 1 by norm_num))) (show 0 < δ/(B+1) by positivity)
  have hupper : ∀ᶠ D in atTop,
      diag D * exp (4 * A D * log D) ≤ C₀ * exp (-δ*D) := by
    filter_upwards [hA, hΛ, hμ, hdiag, hlog, tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_ge_atTop (0:ℝ)] with D hAD hΛD hμD hdD hl hlo hD
    have hl' : (log D)^5 ≤ (δ/(B+1)) * D := by
      simpa [Real.rpow_natCast, Real.norm_of_nonneg hD, Real.norm_of_nonneg (by positivity : 0 ≤ (log D)^5)]
        using hl
    have hKbound : K * A D * (log D)^2 ≤ (K*C) * (log D)^5 := by
      calc
        _ ≤ K * (C * (log D)^3) * (log D)^2 := by gcongr; exact hAD.2
        _ = _ := by ring
    have hAbound : 4 * A D * log D ≤ (4*C) * (log D)^5 := by
      calc
        _ ≤ 4 * (C * (log D)^3) * log D := by gcongr; exact hAD.2
        _ = (4*C) * (log D)^4 := by ring
        _ ≤ (4*C) * (log D)^5 := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hlo (show (4 : ℕ) ≤ 5 by decide)) (by positivity)
    have hpoly : B * (log D)^5 ≤ δ * D := by
      calc
        _ ≤ (B+1) * (log D)^5 := by gcongr; linarith
        _ ≤ (B+1) * ((δ/(B+1)) * D) := mul_le_mul_of_nonneg_left hl' (by positivity)
        _ = _ := by field_simp
    have hExp : K * A D * (log D)^2 + 4*A D*log D - η*Λ D ≤ -δ*D := by
      have hcD : c * D ≤ c * D * log D := le_mul_of_one_le_right (by positivity) hlo
      have hηD := mul_le_mul_of_nonneg_left (hcD.trans hΛD) hη.le
      dsimp [B, δ] at hpoly ⊢
      linarith only [hKbound, hAbound, hpoly, hηD]
    calc
      _ ≤ (C₀ * exp (K * A D * (log D)^2) / μ D) * exp (4 * A D * log D) :=
        mul_le_mul_of_nonneg_right hdD.2 (by positivity)
      _ ≤ (C₀ * exp (K * A D * (log D)^2) / exp (η*Λ D)) * exp (4 * A D * log D) := by
        gcongr
      _ = C₀ * exp (K * A D * (log D)^2 + 4*A D*log D - η*Λ D) := by
        rw [exp_sub, exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hExp) hC₀
  have hlimit : Tendsto (fun D : ℝ ↦ C₀ * exp (-δ*D)) atTop (𝓝 0) := by
    simpa using (tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hδ))).const_mul C₀
  exact squeeze_zero' (hdiag.mono fun D hd ↦ mul_nonneg hd.1 (by positivity)) hupper hlimit

end Cogentic.Randomized
