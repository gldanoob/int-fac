import Cogentic.RandomizedPrimeProductPlancherel
import Cogentic.RandomizedTwoFactorFourier

namespace Cogentic.Randomized

open scoped BigOperators Classical
open Finset

/-- The unit-group coordinates of the Chinese remainder isomorphism. -/
noncomputable def gridUnitCRT {m B : ℕ} (cop : m.Coprime B) :
    (ZMod (m * B))ˣ ≃* (ZMod m)ˣ × (ZMod B)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder cop).toMulEquiv).trans MulEquiv.prodUnits

/-- The affine permutation of the second residue coordinate along the
progression of the chosen row representative. -/
noncomputable def gridPhaseEquiv {m B : ℕ} (cop : m.Coprime B) (r : (ZMod m)ˣ) :
    ZMod B ≃ ZMod B :=
  (Equiv.ofBijective (fun v : ZMod B => (m : ZMod B) * v)
    (by
      have hu := (ZMod.isUnit_iff_coprime m B).mpr cop
      simpa only [IsUnit.unit_spec] using hu.unit.mulLeft_bijective)).trans
      (Equiv.addLeft ((r : ZMod m).val : ZMod B))

@[simp] theorem gridPhaseEquiv_apply {m B : ℕ} (cop : m.Coprime B) (r : (ZMod m)ˣ)
    (v : ZMod B) : gridPhaseEquiv cop r v = ((r : ZMod m).val : ZMod B) + (m : ZMod B) * v :=
  rfl

private noncomputable def unitExtension {B : ℕ} (f : (ZMod B)ˣ → ℂ) (a : ZMod B) : ℂ :=
  if ha : IsUnit a then f ha.unit else 0

private theorem unitExtension_sum {B : ℕ} [NeZero B] {E : Type*} [AddCommMonoid E]
    (f : (ZMod B)ˣ → ℂ) (g : ℂ → E) (hg : g 0 = 0) :
    ∑ a : ZMod B, g (unitExtension f a) = ∑ a : (ZMod B)ˣ, g (f a) := by
  let e : (ZMod B)ˣ ↪ ZMod B := ⟨Units.val, Units.val_injective⟩
  have hmem (a : ZMod B) : a ∈ univ.map e ↔ IsUnit a := by
    rw [mem_map]
    constructor
    · rintro ⟨u, _, hu⟩
      exact ⟨u, hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, mem_univ _, hu⟩
  calc
    _ = ∑ a ∈ univ.map e, g (unitExtension f a) := by
      symm
      apply sum_subset (subset_univ _)
      intro a _ ha
      have h : ¬ IsUnit a := fun h => ha ((hmem a).2 h)
      simp [unitExtension, h, hg]
    _ = _ := by
      rw [sum_map]
      apply sum_congr rfl
      intro a _
      simp [e, unitExtension]

private noncomputable def rowMean {α : Type*} [Fintype α] (f : α → ℂ) : ℂ :=
  (∑ a, f a) / Fintype.card α

private theorem row_center_sum_zero {α : Type*} [Fintype α] [Nonempty α] (f : α → ℂ) :
    ∑ a, (f a - rowMean f) = 0 := by
  have hcard : (Fintype.card α : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [rowMean, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  rw [mul_comm (Fintype.card α : ℂ), div_mul_cancel₀ _ hcard, sub_self]

private theorem row_center_energy_le {α : Type*} [Fintype α] [Nonempty α] (f : α → ℂ) (c : ℂ) :
    ∑ a, ‖f a - rowMean f‖^2 ≤ ∑ a, ‖f a - c‖^2 := by
  let d := rowMean f - c
  let g (a : α) := f a - rowMean f
  have hz : ∑ a, g a = 0 := row_center_sum_zero f
  have hre : ∑ a, (g a).re = 0 := by rw [← Complex.re_sum, hz, Complex.zero_re]
  have him : ∑ a, (g a).im = 0 := by rw [← Complex.im_sum, hz, Complex.zero_im]
  have hsum : (∑ a, 2 * ((g a).re * d.re + (g a).im * d.im)) = 0 := by
    simp only [← mul_sum, sum_add_distrib, ← sum_mul, hre, him, zero_mul, add_zero, mul_zero]
  have hterm (a : α) : ‖f a - c‖^2 =
      ‖g a‖^2 + ‖d‖^2 + 2 * ((g a).re * d.re + (g a).im * d.im) := by
    have ha : f a - c = g a + d := by dsimp [g, d]; ring
    rw [ha]
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im]
    ring
  change ∑ a, ‖g a‖^2 ≤ _
  simp_rw [hterm]
  rw [sum_add_distrib, hsum, add_zero, sum_add_distrib]
  exact le_add_of_nonneg_right (sum_nonneg fun _ _ => sq_nonneg _)

/-- A grid row with its mean on the unit columns subtracted, extended by zero
to the other columns and parametrized by the progression index. -/
noncomputable def gridCenteredRow {m B : ℕ} [NeZero B]
    (cop : m.Coprime B) (f : (ZMod (m * B))ˣ → ℂ) (r : (ZMod m)ˣ) (v : ZMod B) : ℂ :=
  let row (a : (ZMod B)ˣ) := f ((gridUnitCRT cop).symm (r, a))
  unitExtension (fun a => row a - rowMean row) (gridPhaseEquiv cop r v)

/-- The unnormalized additive Fourier coefficients of a centered grid row. -/
noncomputable def gridFourier {m B : ℕ} [NeZero B]
    (cop : m.Coprime B) (f : (ZMod (m * B))ˣ → ℂ) (r : (ZMod m)ˣ) (χ : AddChar (ZMod B) ℂ) : ℂ :=
  RandomizedTwoFactorFourier.transform (gridCenteredRow cop f r) χ

/-- Row centering removes the zero additive frequency. -/
theorem gridFourier_zero {m B : ℕ} [NeZero B]
    (cop : m.Coprime B) (f : (ZMod (m * B))ˣ → ℂ) (r : (ZMod m)ˣ) :
    gridFourier cop f r 0 = 0 := by
  let row (a : (ZMod B)ˣ) := f ((gridUnitCRT cop).symm (r, a))
  let g (a : (ZMod B)ˣ) := row a - rowMean row
  simp only [gridFourier, RandomizedTwoFactorFourier.transform, AddChar.zero_apply, mul_one]
  change ∑ v, unitExtension g (gridPhaseEquiv cop r v) = 0
  rw [(gridPhaseEquiv cop r).bijective.sum_comp (unitExtension g)]
  have h := unitExtension_sum g id rfl
  rw [show (∑ v, unitExtension g v) = ∑ a, g a by simpa only [id_eq] using h]
  exact row_center_sum_zero row

/-- Within-row centering followed by the additive Fourier transform has total
squared norm at most the grid modulus times the full energy about any constant. -/
theorem gridFourier_energy_le {m B : ℕ} [NeZero m] [NeZero B] [NeZero (m * B)]
    (cop : m.Coprime B) (f : (ZMod (m * B))ˣ → ℂ) (c : ℂ) :
    ∑ r : (ZMod m)ˣ, ∑ χ : AddChar (ZMod B) ℂ, ‖gridFourier cop f r χ‖^2 ≤
      (B : ℝ) * ∑ a : (ZMod (m * B))ˣ, ‖f a - c‖^2 := by
  have hrow (r : (ZMod m)ˣ) :
      ∑ v : ZMod B, ‖gridCenteredRow cop f r v‖^2 ≤
        ∑ a : (ZMod B)ˣ, ‖f ((gridUnitCRT cop).symm (r, a)) - c‖^2 := by
    let row (a : (ZMod B)ˣ) := f ((gridUnitCRT cop).symm (r, a))
    let g (a : (ZMod B)ˣ) := row a - rowMean row
    change ∑ v, ‖unitExtension g (gridPhaseEquiv cop r v)‖^2 ≤ _
    have heq := (gridPhaseEquiv cop r).bijective.sum_comp (fun v => ‖unitExtension g v‖^2)
    rw [heq, unitExtension_sum g (fun z => ‖z‖^2) (by simp)]
    exact row_center_energy_le row c
  have hcrt : (∑ r : (ZMod m)ˣ, ∑ a : (ZMod B)ˣ,
      ‖f ((gridUnitCRT cop).symm (r, a)) - c‖^2) = ∑ a : (ZMod (m * B))ˣ, ‖f a - c‖^2 := by
    calc
      _ = ∑ x : (ZMod m)ˣ × (ZMod B)ˣ, ‖f ((gridUnitCRT cop).symm x) - c‖^2 :=
        (Fintype.sum_prod_type' (fun r a => ‖f ((gridUnitCRT cop).symm (r, a)) - c‖^2)).symm
      _ = _ := (gridUnitCRT cop).symm.toEquiv.bijective.sum_comp (fun a => ‖f a - c‖^2)
  simp only [gridFourier, RandomizedTwoFactorFourier.sum_norm_transform_sq, ZMod.card,
    ← mul_sum, ← hcrt]
  exact mul_le_mul_of_nonneg_left (sum_le_sum fun r _ => hrow r) (Nat.cast_nonneg _)

/-- The grid Fourier energy of the actual Mellin-weighted residue counts is
controlled by the nonprincipal Dirichlet energy of the same finite support. -/
theorem gridFourier_mellin_energy_le {m B : ℕ} [NeZero m] [NeZero B] [NeZero (m * B)]
    (cop : m.Coprime B) (P : Finset ℕ) (s : ℂ) :
    ∑ r : (ZMod m)ˣ, ∑ χ : AddChar (ZMod B) ℂ,
      ‖gridFourier cop (Window.classMass P (fun n => ((n : ℂ)^s)⁻¹)) r χ‖^2 ≤
      (B : ℝ) * ∑ a : (ZMod (m * B))ˣ, ‖mellinClassError P s a‖^2 :=
  gridFourier_energy_le cop _ _

/-- The GRH bound survives the CRT reshuffle, row projection, and grid
Fourier transform, with exactly the additive Parseval factor. -/
theorem primeBinProducts_gridFourier_energy_from_critical_line (line : DirichletLZerosOnLine) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m B : ℕ) [NeZero m] [NeZero B] [NeZero (m * B)]
      (cop : m.Coprime B) {ι : Type} [Fintype ι] [DecidableEq ι]
      (A U : ι → ℕ), (∀ i, 2 ≤ U i) → (∀ i, A i ≤ U i) →
      (Pairwise fun i j ↦ Disjoint (primeBin (A i) (U i)) (primeBin (A j) (U j))) →
      ∀ σ t : ℝ, 0 ≤ σ →
        ∑ r : (ZMod m)ˣ, ∑ χ : AddChar (ZMod B) ℂ,
          ‖gridFourier cop (Window.classMass (primeBinProducts A U)
            (fun n => ((n : ℂ)^((σ : ℂ) + t * Complex.I))⁻¹)) r χ‖^2 ≤
          (B : ℝ) * (∏ i, K * Real.sqrt (U i) *
            (1 + Real.log ((m * B : ℕ) * ((U i : ℝ) + |t| + 2)))^3)^2 := by
  obtain ⟨K, hK, h⟩ := primeBinProducts_mellin_energy_from_critical_line line
  refine ⟨K, hK, ?_⟩
  intro m B _ _ _ cop ι _ _ A U hU hAU hdisj σ t hσ
  exact (gridFourier_mellin_energy_le cop _ _).trans
    (mul_le_mul_of_nonneg_left (h (m * B) A U hU hAU hdisj σ t hσ) (Nat.cast_nonneg _))

open Lean Elab Command in
run_cmd
  for ax in ← collectAxioms ``primeBinProducts_gridFourier_energy_from_critical_line do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "The grid Fourier theorem depends on unexpected axiom {ax}"

#print axioms gridFourier_mellin_energy_le
#print axioms primeBinProducts_gridFourier_energy_from_critical_line

end Cogentic.Randomized
