import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Cogentic.Randomized

def rootPolynomial (v : ℝ) : ℝ :=
  455625*v^18 + 1181952*v^12 - 1092096*v^9 - 663552*v^6 + 294912*v^3 + 65536

def rootLower : ℝ := 0.78485210451994876996

def rootUpper : ℝ := 0.78485210451994876997

theorem exists_algebraicRoot : ∃ v, rootLower < v ∧ v < rootUpper ∧ rootPolynomial v = 0 := by
  have hab : rootLower ≤ rootUpper := by norm_num [rootLower, rootUpper]
  have hf : Continuous rootPolynomial := by unfold rootPolynomial; fun_prop
  have hlow : 0 < rootPolynomial rootLower := by norm_num [rootPolynomial, rootLower]
  have hupp : rootPolynomial rootUpper < 0 := by norm_num [rootPolynomial, rootUpper]
  obtain ⟨v, hv, hzero⟩ := intermediate_value_Icc' hab hf.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (rootPolynomial rootUpper) (rootPolynomial rootLower) from
      ⟨hupp.le, hlow.le⟩)
  refine ⟨v, lt_of_le_of_ne hv.1 ?_, lt_of_le_of_ne hv.2 ?_, hzero⟩
  · intro h
    rw [← h] at hzero
    exact hlow.ne' hzero
  · intro h
    rw [h] at hzero
    exact hupp.ne hzero

noncomputable def algebraicCost (v : ℝ) : ℝ :=
  (225*v^6-96*v^3-128)/(36*v^2*(3*v^3-4))

noncomputable def algebraicPrivate (v : ℝ) : ℝ :=
  4/(9*v^2) + 2*v/3

noncomputable def algebraicSqrtCost (v : ℝ) : ℝ :=
  (6*algebraicPrivate v*(algebraicCost v-algebraicPrivate v)-3*v^2/2)/4

theorem algebraicSqrtCost_sq {v : ℝ} (hv : v ≠ 0) (hd : 3*v^3-4 ≠ 0)
    (hp : rootPolynomial v = 0) : algebraicSqrtCost v ^ 2 = algebraicCost v := by
  have h :
      algebraicSqrtCost v ^ 2 - algebraicCost v =
        rootPolynomial v / (46656*v^8*(3*v^3-4)^2) := by
    unfold algebraicSqrtCost algebraicCost algebraicPrivate rootPolynomial
    generalize hden : 3*v^3-4 = a at hd ⊢
    field_simp [hv, hd]
    subst a
    ring
  rw [hp, zero_div] at h
  exact sub_eq_zero.mp h

private def cubePolynomial (w : ℝ) : ℝ :=
  455625*w^6 + 1181952*w^4 - 1092096*w^3 - 663552*w^2 + 294912*w + 65536

private theorem rootPolynomial_eq_cube (v : ℝ) : rootPolynomial v = cubePolynomial (v^3) := by
  unfold rootPolynomial cubePolynomial
  ring

private theorem cubePolynomial_strictAnti :
    StrictAntiOn cubePolynomial (Set.Icc (47/100 : ℝ) (1/2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · unfold cubePolynomial
    fun_prop
  · intro w hw
    have hw' : w ∈ Set.Icc (47/100 : ℝ) (1/2) := interior_subset hw
    have hpos : 0 ≤ w := (by norm_num : (0 : ℝ) ≤ 47/100).trans hw'.1
    have hd : deriv cubePolynomial w =
        2733750*w^5 + 4727808*w^3 - 3276288*w^2 - 1327104*w + 294912 := by
      have h : HasDerivAt (fun z : ℝ => z) 1 w := hasDerivAt_id w
      have h' := ((((((h.pow 6).const_mul 455625).add ((h.pow 4).const_mul 1181952)).sub
        ((h.pow 3).const_mul 1092096)).sub ((h.pow 2).const_mul 663552)).add
        (h.const_mul 294912)).add_const 65536 |>.deriv
      convert h' using 1
      · congr 1
      · ring
    rw [hd]
    have h5 : w^5 ≤ (1/2 : ℝ)^5 := pow_le_pow_left₀ hpos hw'.2 _
    have h3 : w^3 ≤ (1/2 : ℝ)^3 := pow_le_pow_left₀ hpos hw'.2 _
    have h2 : (47/100 : ℝ)^2 ≤ w^2 := pow_le_pow_left₀ (by norm_num) hw'.1 _
    linarith only [h5, h3, h2, hw'.1]

private theorem cube_mem_of_rootBounds {v : ℝ} (hlo : rootLower < v) (hhi : v < rootUpper) :
    v^3 ∈ Set.Icc (47/100 : ℝ) (1/2) := by
  have h₀ : (78/100 : ℝ) ≤ v := (by norm_num [rootLower] : (78/100 : ℝ) ≤ rootLower).trans hlo.le
  have h₁ : v ≤ (79/100 : ℝ) := hhi.le.trans (by norm_num [rootUpper])
  have hp₀ : (78/100 : ℝ)^3 ≤ v^3 := pow_le_pow_left₀ (by norm_num) h₀ _
  have hp₁ : v^3 ≤ (79/100 : ℝ)^3 := pow_le_pow_left₀ ((by norm_num : (0 : ℝ) ≤ 78/100).trans h₀) h₁ _
  exact ⟨(by norm_num : (47/100 : ℝ) ≤ (78/100 : ℝ)^3).trans hp₀,
    hp₁.trans (by norm_num)⟩

/-- Exactly one real root lies between the two specified rational bounds. -/
theorem existsUnique_algebraicRoot :
    ∃! v, rootLower < v ∧ v < rootUpper ∧ rootPolynomial v = 0 := by
  obtain ⟨v, hvl, hvu, hv⟩ := exists_algebraicRoot
  refine ⟨v, ⟨hvl, hvu, hv⟩, ?_⟩
  rintro w ⟨hwl, hwu, hw⟩
  have hc := cubePolynomial_strictAnti.injOn (cube_mem_of_rootBounds hwl hwu)
    (cube_mem_of_rootBounds hvl hvu) (by rw [← rootPolynomial_eq_cube, ← rootPolynomial_eq_cube, hw, hv])
  exact (show Odd (3 : ℕ) from ⟨1, by decide⟩).pow_injective hc

end Cogentic.Randomized
