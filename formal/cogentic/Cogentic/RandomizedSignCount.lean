import Cogentic.RandomizedHiddenLabels
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Defs

namespace Cogentic.RandomizedSignCount

open RandomizedHiddenLabels

abbrev SignCube (k : ℕ) := Fin k → Bool

noncomputable def usefulSigns (k : ℕ) : Finset (SignCube k) := by
  classical
  exact (Finset.univ.erase (fun _ => false)).erase (fun _ => true)

theorem mem_usefulSigns {k : ℕ} (signs : SignCube k) :
    signs ∈ usefulSigns k ↔ (∃ i, signs i = true) ∧ ∃ i, signs i = false := by
  classical
  simp [usefulSigns, funext_iff, not_forall, and_comm]

theorem usefulSigns_card {k : ℕ} (hk : 0 < k) : (usefulSigns k).card = 2 ^ k - 2 := by
  classical
  have different : (fun _ : Fin k => true) ≠ fun _ => false := by
    intro h
    cases congrFun h ⟨0, hk⟩
  have member : (fun _ : Fin k => true) ∈ (Finset.univ.erase (fun _ => false)) := by
    simp [different]
  unfold usefulSigns
  rw [Finset.card_erase_of_mem member, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [Nat.sub_sub]

variable {Label G : Type*} [DecidableEq Label] [CommGroup G]

abbrev SquareFiber (a : G) := {x : G // x ^ 2 = a ^ 2}

/-- Compare any output root to a fixed public root of the same square. -/
def compareRoot {a : G} (publicRoot : SquareFiber a) : SquareFiber a ≃ SquareFiber (1 : G) where
  toFun x := ⟨x.val * publicRoot.val⁻¹, by rw [mul_pow, inv_pow, x.property, publicRoot.property,
    mul_inv_cancel, one_pow]⟩
  invFun s := ⟨s.val * publicRoot.val, by rw [mul_pow, s.property, one_pow, one_mul, publicRoot.property]⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])

def replacementOutput (labels : Finset Label) (multiplicity : Label → ℕ)
    (roots : Label → G) (i : Label) (hi : i ∈ labels) (x : SquareFiber (roots i)) :
    SquareFiber (labelProduct labels multiplicity roots) := by
  refine ⟨labelProduct labels multiplicity (Function.update roots i x.val), ?_⟩
  let t := x.val * (roots i)⁻¹
  have ht : t ^ 2 = 1 := by
    dsimp [t]
    rw [mul_pow, inv_pow, x.property, mul_inv_cancel]
  have hx : t * roots i = x.val := by simp [t, mul_assoc]
  simpa only [hx] using labelProduct_update_square labels multiplicity roots hi ht

/-- Varying one odd hidden label is a bijection onto the output square fiber. -/
noncomputable def replacementEquiv (labels : Finset Label) (multiplicity : Label → ℕ)
    (roots : Label → G) {i : Label} (hi : i ∈ labels) (hodd : Odd (multiplicity i)) :
    SquareFiber (roots i) ≃ SquareFiber (labelProduct labels multiplicity roots) := by
  apply Equiv.ofBijective (replacementOutput labels multiplicity roots i hi)
  constructor
  · intro x y h
    let output := replacementOutput labels multiplicity roots i hi y
    obtain ⟨z, _, same⟩ :=
      existsUnique_replacement labels multiplicity roots hi hodd output.val output.property
    exact Subtype.ext ((same x.val ⟨x.property, congrArg Subtype.val h⟩).trans
      (same y.val ⟨y.property, rfl⟩).symm)
  · intro output
    obtain ⟨x, hx, _⟩ :=
      existsUnique_replacement labels multiplicity roots hi hodd output.val output.property
    exact ⟨⟨x, hx.1⟩, Subtype.ext hx.2⟩

/-- A supplied CRT equivalence gives the signs of the output divided by the
fixed public root, as the chosen hidden root varies over its own square fiber. -/
noncomputable def comparisonSigns (labels : Finset Label) (multiplicity : Label → ℕ)
    (roots : Label → G) {i : Label} (hi : i ∈ labels) (hodd : Odd (multiplicity i))
    {k : ℕ} (publicRoot : SquareFiber (labelProduct labels multiplicity roots))
    (crt : SquareFiber (1 : G) ≃ SignCube k) : SquareFiber (roots i) ≃ SignCube k :=
  (replacementEquiv labels multiplicity roots hi hodd).trans ((compareRoot publicRoot).trans crt)

theorem comparisonSigns_apply (labels : Finset Label) (multiplicity : Label → ℕ)
    (roots : Label → G) {i : Label} (hi : i ∈ labels) (hodd : Odd (multiplicity i))
    {k : ℕ} (publicRoot : SquareFiber (labelProduct labels multiplicity roots))
    (crt : SquareFiber (1 : G) ≃ SignCube k) (x : SquareFiber (roots i)) :
    comparisonSigns labels multiplicity roots hi hodd publicRoot crt x =
      crt (compareRoot publicRoot (replacementOutput labels multiplicity roots i hi x)) := rfl

theorem mem_mixed_comparison {X : Type*} {k : ℕ} (comparison : X ≃ SignCube k) (x : X) :
    x ∈ (usefulSigns k).map comparison.symm.toEmbedding ↔
      (∃ i, comparison x i = true) ∧ ∃ i, comparison x i = false := by
  rw [Finset.mem_map_equiv, Equiv.symm_symm, mem_usefulSigns]

/-- The numerator and denominator for uniform sampling in one hidden square
fiber, with all other roots and the public comparison fixed. -/
theorem proper_sign_count (labels : Finset Label) (multiplicity : Label → ℕ)
    (roots : Label → G) {i : Label} (hi : i ∈ labels) (hodd : Odd (multiplicity i))
    {k : ℕ} (hk : 2 ≤ k) (publicRoot : SquareFiber (labelProduct labels multiplicity roots))
    (crt : SquareFiber (1 : G) ≃ SignCube k) :
    let comparison := comparisonSigns labels multiplicity roots hi hodd publicRoot crt
    let useful := (usefulSigns k).map comparison.symm.toEmbedding
    let all := Finset.univ.map comparison.symm.toEmbedding
    useful.card = 2 ^ k - 2 ∧ all.card = 2 ^ k ∧
      (useful.card : ℚ) / all.card = ((2 ^ k - 2 : ℕ) : ℚ) / (2 ^ k : ℕ) := by
  have positive : 0 < k := lt_of_lt_of_le (by decide) hk
  simp [usefulSigns_card positive]

end Cogentic.RandomizedSignCount
