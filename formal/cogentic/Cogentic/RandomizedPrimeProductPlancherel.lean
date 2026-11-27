import Cogentic.Window
import Cogentic.RandomizedProductPerron

namespace Cogentic.Randomized

open scoped BigOperators Classical ComplexConjugate
open Finset

variable {q : ℕ} [NeZero q]

private noncomputable def unitTransform (f : (ZMod q)ˣ → ℂ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ r, f r * χ (r : ZMod q)

private theorem unitTransform_inversion (f : (ZMod q)ˣ → ℂ) (r : (ZMod q)ˣ) :
    ∑ χ : DirichletCharacter ℂ q, χ (r : ZMod q)⁻¹ * unitTransform f χ =
      (q.totient : ℂ) * f r := by
  classical
  calc
    _ = ∑ a : (ZMod q)ˣ, f a * (∑ χ : DirichletCharacter ℂ q, χ (r : ZMod q)⁻¹ * χ a) := by
      simp only [unitTransform, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => by ring))
    _ = _ := by
      simp only [DirichletCharacter.sum_char_inv_mul_char_eq ℂ r.isUnit]
      rw [sum_eq_single r]
      · simp [mul_comm]
      · intro a _ ha
        have h : (r : ZMod q) ≠ a := fun he => ha (Units.ext he.symm)
        simp [h]
      · simp

omit [NeZero q] in
private theorem conj_char_unit (χ : DirichletCharacter ℂ q) (r : (ZMod q)ˣ) :
    conj (χ (r : ZMod q)) = χ (r : ZMod q)⁻¹ := by
  calc
    _ = χ⁻¹ (r : ZMod q) := MulChar.star_apply' χ r
    _ = _ := by rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]

private theorem unitTransform_plancherel (f : (ZMod q)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖unitTransform f χ‖^2 =
      (q.totient : ℝ) * ∑ r, ‖f r‖^2 := by
  have hconj (χ : DirichletCharacter ℂ q) :
      conj (unitTransform f χ) = ∑ r, conj (f r) * χ (r : ZMod q)⁻¹ := by
    simp only [unitTransform, map_sum, map_mul, conj_char_unit]
  have h : ∑ χ : DirichletCharacter ℂ q, conj (unitTransform f χ) * unitTransform f χ =
      (q.totient : ℂ) * ∑ r, conj (f r) * f r := calc
    _ = ∑ χ : DirichletCharacter ℂ q, ∑ r,
        conj (f r) * (χ (r : ZMod q)⁻¹ * unitTransform f χ) := by
      simp only [hconj, sum_mul, mul_assoc]
    _ = ∑ r, conj (f r) * (∑ χ : DirichletCharacter ℂ q,
        χ (r : ZMod q)⁻¹ * unitTransform f χ) := by
      rw [sum_comm]
      simp only [mul_sum]
    _ = _ := by
      simp only [unitTransform_inversion, mul_sum]
      exact sum_congr rfl (fun _ _ => by ring)
  simp only [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

private theorem sum_units_character (χ : DirichletCharacter ℂ q) :
    ∑ r : (ZMod q)ˣ, χ (r : ZMod q) = if χ = 1 then (q.totient : ℂ) else 0 := by
  by_cases hχ : χ = 1
  · subst χ
    simp [ZMod.card_units_eq_totient, nsmul_eq_mul]
  · rw [if_neg hχ]
    obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hχ
    refine eq_zero_of_mul_eq_self_left hu ?_
    simpa only [mul_sum, ← map_mul, Units.val_mul, Function.comp_apply] using
      (Group.mulLeft_bijective u).sum_comp (fun r : (ZMod q)ˣ => χ (r : ZMod q))

private theorem unitTransform_classMass (P : Finset ℕ) (w : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) :
    unitTransform (Window.classMass (q := q) P w) χ = Window.twist P w χ := by
  unfold unitTransform Window.classMass Window.twist
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  by_cases hn : IsUnit (n : ZMod q)
  · obtain ⟨u, hu⟩ := hn
    rw [sum_eq_single u]
    · simp [hu, mul_comm]
    · intro r _ hr
      have h : (r : ZMod q) ≠ n := fun e => hr (Units.ext (e.trans hu.symm))
      simp [h]
    · simp
  · rw [χ.map_nonunit hn, zero_mul]
    apply sum_eq_zero
    intro r _
    have h : (r : ZMod q) ≠ n := fun e => hn (e ▸ r.isUnit)
    simp [h]

/-- The variance across reduced residues is the nonprincipal character energy
divided by the number of reduced residues. Nonunits vanish in both sums. -/
theorem classMass_centered_plancherel (P : Finset ℕ) (w : ℕ → ℂ) :
    ∑ r : (ZMod q)ˣ, ‖Window.classMass P w r -
        Window.twist P w (1 : DirichletCharacter ℂ q) / q.totient‖^2 =
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖Window.twist P w χ‖^2) / (q.totient : ℝ) := by
  let c := Window.twist P w (1 : DirichletCharacter ℂ q) / q.totient
  let e (r : (ZMod q)ˣ) := Window.classMass P w r - c
  have hφ : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
  have hφC : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
  have hφR : (q.totient : ℝ) ≠ 0 := by exact_mod_cast hφ.ne'
  have hfreq (χ : DirichletCharacter ℂ q) :
      unitTransform e χ = if χ = 1 then 0 else Window.twist P w χ := by
    have he : unitTransform e χ =
        unitTransform (Window.classMass P w) χ - c * ∑ r : (ZMod q)ˣ, χ (r : ZMod q) := by
      simp only [unitTransform, e, sub_mul, sum_sub_distrib, mul_sum]
    rw [he, unitTransform_classMass, sum_units_character]
    by_cases hχ : χ = 1
    · simp [hχ, c, hφC]
    · simp [hχ]
  change ∑ r, ‖e r‖^2 = _
  apply (eq_div_iff hφR).2
  rw [mul_comm, ← unitTransform_plancherel]
  calc
    _ = ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖unitTransform e χ‖^2 := by
      simpa [hfreq] using (sum_erase_add univ (fun χ => ‖unitTransform e χ‖^2)
        (mem_univ (1 : DirichletCharacter ℂ q))).symm
    _ = _ := sum_congr rfl (fun χ hχ => by simp [hfreq, (mem_erase.mp hχ).1])

#print axioms classMass_centered_plancherel


/-- A uniform bound on the nonprincipal coefficients bounds the entire squared
residue discrepancy, with no extra factor for the number of residues. -/
theorem classMass_centered_sq_le (P : Finset ℕ) (w : ℕ → ℂ) {M : ℝ}
    (hχ : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖Window.twist P w χ‖ ≤ M) :
    ∑ r : (ZMod q)ˣ, ‖Window.classMass P w r -
        Window.twist P w (1 : DirichletCharacter ℂ q) / q.totient‖^2 ≤ M^2 := by
  rw [classMass_centered_plancherel]
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  apply (div_le_iff₀ hφ).2
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  calc
    _ ≤ ∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, M^2 := by
      exact sum_le_sum fun χ h => pow_le_pow_left₀ (norm_nonneg _)
        (hχ χ (mem_erase.mp h).1) 2
    _ ≤ ∑ _χ : DirichletCharacter ℂ q, M^2 := by
      exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => sq_nonneg M)
    _ = _ := by simp [hcard, nsmul_eq_mul, mul_comm]

/-- The complex centered residue vector with the Mellin weight `n^{-s}`. -/
noncomputable def mellinClassError (P : Finset ℕ) (s : ℂ) (r : (ZMod q)ˣ) : ℂ :=
  Window.classMass P (fun n => ((n : ℂ)^s)⁻¹) r -
    Window.twist P (fun n => ((n : ℂ)^s)⁻¹) (1 : DirichletCharacter ℂ q) / q.totient

omit [NeZero q] in
private theorem mellin_twist_eq_polynomial (P : Finset ℕ) (s : ℂ)
    (χ : DirichletCharacter ℂ q) :
    Window.twist P (fun n => ((n : ℂ)^s)⁻¹) χ =
      productDirichletPolynomial P (fun n => χ n) s := by
  simp only [Window.twist, productDirichletPolynomial, div_eq_mul_inv]

/-- Exact Plancherel for the Mellin residue vector at every complex argument,
including the full support of any prime-bin product pattern. -/
theorem mellinClassError_plancherel (P : Finset ℕ) (s : ℂ) :
    ∑ r : (ZMod q)ˣ, ‖mellinClassError P s r‖^2 =
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ‖productDirichletPolynomial P (fun n => χ n) s‖^2) / (q.totient : ℝ) := by
  simpa only [mellinClassError, mellin_twist_eq_polynomial] using
    (classMass_centered_plancherel (q := q) P (fun n => ((n : ℂ)^s)⁻¹))

/-- The prime-bin Mellin estimate bounds the squared residue discrepancy at
every real height, uniformly over the modulus. -/
theorem primeBinProducts_mellin_energy_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] [DecidableEq ι]
      (A B : ι → ℕ), (∀ i, 2 ≤ B i) → (∀ i, A i ≤ B i) →
      (Pairwise fun i j ↦ Disjoint (primeBin (A i) (B i)) (primeBin (A j) (B j))) →
      ∀ σ t : ℝ, 0 ≤ σ →
        ∑ r : (ZMod q)ˣ, ‖mellinClassError (primeBinProducts A B)
          ((σ : ℂ) + t * Complex.I) r‖^2 ≤
          (∏ i, K * Real.sqrt (B i) *
            (1 + Real.log (q * ((B i : ℝ) + |t| + 2)))^3)^2 := by
  obtain ⟨K, hK, hb⟩ := primeBin_mellin_from_critical_line line
  refine ⟨K, hK, ?_⟩
  intro q _ ι _ _ A B hB hAB hdisj σ t hσ
  let s := (σ : ℂ) + t * Complex.I
  let H (i : ι) := K * Real.sqrt (B i) *
    (1 + Real.log (q * ((B i : ℝ) + |t| + 2)))^3
  change ∑ r : (ZMod q)ˣ, ‖mellinClassError (primeBinProducts A B) s r‖^2 ≤ (∏ i, H i)^2
  unfold mellinClassError
  refine classMass_centered_sq_le _ _ (M := ∏ i, H i) ?_
  intro χ hχ
  rw [mellin_twist_eq_polynomial, primeBinProducts_dirichletPolynomial χ A B _ hdisj,
    norm_prod]
  exact prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hb q χ hχ (A i) (B i) σ t
    (hB i) (hAB i) hσ)

open Lean Elab Command in
run_cmd
  for ax in ← collectAxioms ``primeBinProducts_mellin_energy_from_critical_line do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "The Mellin variance theorem depends on unexpected axiom {ax}"

#print axioms mellinClassError_plancherel
#print axioms primeBinProducts_mellin_energy_from_critical_line

end Cogentic.Randomized
