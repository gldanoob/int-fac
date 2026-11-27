import Cogentic.RandomizedBalancedFiniteSchedule

namespace Cogentic.Randomized.BalancedPerturbation

/-- At the small common perturbations used in the finite schedule, all of the
other leading scalar charges and nonactive descent margins remain strict. -/
theorem other_scalar_checks {p : BalancedPerturbation}
    (huₗ : 0.58514027 < p.u) (huᵤ : p.u < 0.58514029)
    (hbₗ : 0.9448547 < p.b) (hbᵤ : p.b < 0.944855)
    (hdₗ : 1.4199108 < p.δ) (hdᵤ : p.δ < 1.4199110)
    (hq : 0 < p.q) (hq' : p.q ≤ 1 / 10 ^ 6) :
    0 < p.y₂ ∧ p.y₂ < p.v₁ ∧ p.v₁ < p.y₁ ∧ p.y₁ < p.v₀ ∧
    p.v₀ < p.y₀ ∧ p.y₀ < 1 ∧ 0 < 2 * p.β - 1 / 3 ∧
    1 < p.lowBox ∧ 1.636 < p.lowRatio ∧
    p.Aplus < (p.lowRatio - 1) * p.lowBox * p.β ∧
    1.01 * p.R < 0.49 * (p.A₀ + p.lowBox * p.β) ∧
    (33 / 32) * p.R < (15 / 32) * (p.A₀ + p.lowBox * p.β) ∧
    p.b + p.δ * 1.43 / 3 + 1 / (3 * p.δ * p.b) + 2 * p.q < 1.871 ∧
    p.b + p.δ * 1.636 / 3 + (1 + p.v₁) / (3 * p.δ * p.b) + 2 * p.q < 1.9835 ∧
    p.b + p.δ * 1.43 / 3 + p.h * Real.sqrt (p.y₁ / p.y₀) + 2 * p.q < 1.969 ∧
    p.b + p.δ * 1.636 / 3 + p.h * Real.sqrt (p.y₂ / p.y₀) + 2 * p.q < 1.912 ∧
    p.b + p.δ * p.lowRatio / 3 + 2 * p.q < 1.736 ∧
    p.b + 2 * p.δ / 3 < 1.892 ∧ 2 * p.b < 1.890 := by
  have hu : 0 < p.u := by linarith only [huₗ]
  have hb : 0 < p.b := by linarith only [hbₗ]
  have hd : 0 < p.δ := by linarith only [hdₗ]
  have hαₗ : 0.5 ≤ p.α := by unfold α; linarith only [hq]
  have hαᵤ : p.α ≤ 0.500001 := by unfold α; linarith only [hq']
  have hα : 0 < p.α := by linarith only [hαₗ]
  have hχₗ : 1 ≤ p.χ := by unfold χ; linarith only [hq]
  have hχᵤ : p.χ ≤ 1.000001 := by unfold χ; linarith only [hq']
  have hh : 0 < p.h := by unfold h; positivity
  have hh' : p.h ≤ 0.58514129 := by unfold h; linarith only [huᵤ,hq']
  have hy₀ : 0 < p.y₀ := by unfold y₀; positivity
  have hv₀ : 0 < p.v₀ := by unfold v₀; positivity
  have hy₁ : 0 < p.y₁ := by unfold y₁; positivity
  have hv₁ : 0 < p.v₁ := by unfold v₁; positivity
  have hy₂ : 0 < p.y₂ := by unfold y₂; positivity
  have hy₀l : 0.3646215 ≤ p.y₀ := by
    unfold y₀
    calc
      _ ≤ 3 * (0.58514027 : ℝ) ^ 2 * 1.4199108 / 4 := by norm_num
      _ ≤ _ := by gcongr
  have hy₀u : p.y₀ ≤ 0.3646216 := by
    unfold y₀
    calc
      _ ≤ 3 * (0.58514029 : ℝ) ^ 2 * 1.4199110 / 4 := by gcongr
      _ ≤ _ := by norm_num
  have hv₀l : 0.18231075 ≤ p.v₀ := by
    unfold v₀
    calc
      _ = (0.5 : ℝ) * 0.3646215 := by norm_num
      _ ≤ _ := by gcongr
  have hv₀u : p.v₀ ≤ 0.18231117 := by
    unfold v₀
    calc
      _ ≤ (0.500001 : ℝ) * 0.3646216 := by gcongr
      _ ≤ _ := by norm_num
  have hv₁u : p.v₁ ≤ 0.06375 := by
    unfold v₁ y₁
    calc
      _ ≤ (0.500001 : ℝ) * (0.18231117 / 1.43) := by gcongr
      _ ≤ _ := by norm_num
  have hβₗ : 0.6654323 ≤ p.β := by
    unfold β
    calc
      _ ≤ (0.9448547 : ℝ) / 1.4199110 := by norm_num
      _ ≤ _ := by gcongr
  have hβᵤ : p.β ≤ 0.6654327 := by
    unfold β
    calc
      _ ≤ (0.944855 : ℝ) / 1.4199108 := by gcongr
      _ ≤ _ := by norm_num
  have hβ : 0 < p.β := by linarith only [hβₗ]
  have hden : 0 < 2 * p.β - 1 / 3 := by linarith only [hβₗ]
  have hRₗ : 0.3493145 ≤ p.R := by
    unfold R
    calc
      _ ≤ 1 / (1.4199110 : ℝ) ^ 3 := by norm_num
      _ ≤ _ := by gcongr
  have hRᵤ : p.R ≤ 0.3493147 := by
    unfold R
    calc
      _ ≤ 1 / (1.4199108 : ℝ) ^ 3 := by gcongr
      _ ≤ _ := by norm_num
  have hR : 0 < p.R := by linarith only [hRₗ]
  have hAₗ : 0.4129982 ≤ p.A₀ := by
    unfold A₀
    calc
      _ ≤ (0.3493145 : ℝ) * (1 + 1 * 0.18231075) := by norm_num
      _ ≤ _ := by gcongr
  have hAᵤ : p.A₀ ≤ 0.4129988 := by
    unfold A₀
    calc
      _ ≤ (0.3493147 : ℝ) * (1 + 1.000001 * 0.18231117) := by gcongr
      _ ≤ _ := by norm_num
  have hApₗ : 0.4129982 ≤ p.Aplus := by unfold Aplus; linarith only [hAₗ,hq]
  have hApᵤ : p.Aplus ≤ 0.4129998 := by unfold Aplus; linarith only [hAᵤ,hq']
  have hAp : 0 < p.Aplus := by linarith only [hApₗ]
  have hRatioLower : 1.67052 ≤ p.lowRatio := by
    unfold lowRatio
    calc
      _ ≤ ((0.6654323 : ℝ) + 2 * 0.4129982 + 0.3493145 / (3 * 0.6654327) + 4 * 0) /
          (2 * 0.6654327 - 1 / 3) := by norm_num
      _ ≤ _ := by gcongr
  have hRatioUpper : p.lowRatio ≤ 1.67056 := by
    unfold lowRatio
    calc
      _ ≤ ((0.6654327 : ℝ) + 2 * 0.4129998 + 0.3493147 / (3 * 0.6654323) + 4 * (1 / 10 ^ 6)) /
          (2 * 0.6654323 - 1 / 3) := by gcongr
      _ ≤ _ := by norm_num
  have hL : 1.0498 ≤ p.lowBox := by
    unfold lowBox
    calc
      _ ≤ (1.67052 : ℝ) - (0.4129998 + 1 / 10 ^ 6) / 0.6654323 := by norm_num
      _ ≤ _ := by gcongr
  have hLpos : 0 < p.lowBox := by linarith only [hL]
  have hcut : p.Aplus < (p.lowRatio - 1) * p.lowBox * p.β := by
    have hfactor : 0 ≤ p.lowRatio - 1 := by linarith only [hRatioLower]
    have hprod : 0 ≤ (p.lowRatio - 1) * p.lowBox := mul_nonneg hfactor hLpos.le
    calc
      _ ≤ 0.4129998 := hApᵤ
      _ < (1.67052 - 1 : ℝ) * 1.0498 * 0.6654323 := by norm_num
      _ ≤ _ := by gcongr
  have hbottom : 0.4129982 + 1.0498 * 0.6654323 ≤ p.A₀ + p.lowBox * p.β := by gcongr
  have hsa : Real.sqrt (p.y₁ / p.y₀) ≤ 0.592 := by
    have he : p.y₁ / p.y₀ = p.α / 1.43 := by
      unfold y₁ v₀
      field_simp
    rw [he, Real.sqrt_le_iff]
    constructor
    · norm_num
    · exact (div_le_iff₀ (by norm_num)).2 (hαᵤ.trans (by norm_num))
  have hsb : Real.sqrt (p.y₂ / p.y₀) ≤ 0.328 := by
    have he : p.y₂ / p.y₀ = p.α ^ 2 / (1.43 * 1.636) := by
      unfold y₂ v₁ y₁ v₀
      field_simp
    rw [he, Real.sqrt_le_iff]
    constructor
    · norm_num
    · have hsq := pow_le_pow_left₀ hα.le hαᵤ 2
      exact (div_le_iff₀ (by norm_num)).2 (hsq.trans (by norm_num))
  refine ⟨hy₂, ?_, ?_, ?_, ?_, ?_, hden, ?_, ?_, hcut, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_lt_self hv₁ (by norm_num)
  · unfold v₁
    exact mul_lt_of_lt_one_left hy₁ (hαᵤ.trans_lt (by norm_num))
  · exact div_lt_self hv₀ (by norm_num)
  · unfold v₀
    exact mul_lt_of_lt_one_left hy₀ (hαᵤ.trans_lt (by norm_num))
  · linarith only [hy₀u]
  · linarith only [hL]
  · linarith only [hRatioLower]
  · linarith only [hbottom,hRᵤ]
  · linarith only [hbottom,hRᵤ]
  · calc
      _ ≤ (0.944855 : ℝ) + 1.4199110 * 1.43 / 3 +
          1 / (3 * 1.4199108 * 0.9448547) + 2 * (1 / 10 ^ 6) := by gcongr
      _ < _ := by norm_num
  · calc
      _ ≤ (0.944855 : ℝ) + 1.4199110 * 1.636 / 3 +
          (1 + 0.06375) / (3 * 1.4199108 * 0.9448547) + 2 * (1 / 10 ^ 6) := by gcongr
      _ < _ := by norm_num
  · calc
      _ ≤ (0.944855 : ℝ) + 1.4199110 * 1.43 / 3 + 0.58514129 * 0.592 + 2 * (1 / 10 ^ 6) := by gcongr
      _ < _ := by norm_num
  · calc
      _ ≤ (0.944855 : ℝ) + 1.4199110 * 1.636 / 3 + 0.58514129 * 0.328 + 2 * (1 / 10 ^ 6) := by gcongr
      _ < _ := by norm_num
  · calc
      _ ≤ (0.944855 : ℝ) + 1.4199110 * 1.67056 / 3 + 2 * (1 / 10 ^ 6) := by gcongr
      _ < _ := by norm_num
  · linarith only [hbᵤ,hdᵤ]
  · linarith only [hbᵤ]

#print axioms other_scalar_checks

end Cogentic.Randomized.BalancedPerturbation
