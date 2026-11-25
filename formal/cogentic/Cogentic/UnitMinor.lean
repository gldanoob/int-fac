import Cogentic.EliminationUnits
import Cogentic.UnitGap

/-! The determinant margin for the actual archimedean columns selected from
the executable integer elimination. -/

open NumberField
open scoped BigOperators Matrix NumberField Polynomial

namespace Cogentic

noncomputable def orderedUnitRank {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (p : Fin d ≃ InfinitePlace K) : Fin (NumberField.Units.rank K) ≃ Fin (d-1) :=
  finCongr (by rw [NumberField.Units.rank, ← Fintype.card_congr p,Fintype.card_fin])

/-- Conditional on the integer-kernel observations spanning, a successful
marking and elimination run supplies a selected set of actual field units
whose true numerical minor and integer class determinant obey explicit
bounds. The only size parameter is the largest absolute log-column entry. -/
theorem computed_helmert_unit_minor {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [IsTotallyReal K₁] [IsTotallyReal K₂]
    {s : Marking.Input} {rel : Marking.Relations} {out : Elimination.IntegerFamily rel.marks.length}
    (marked : Marking.stageOne s = some rel) (solved : Elimination.stageTwo rel = some out)
    (places₁ : Fin s.degree ≃ InfinitePlace K₁) (places₂ : Fin s.degree ≃ InfinitePlace K₂)
    (θ₁ : K₁) (θ₂ : K₂)
    (root₁ : (Marking.polynomial s.first).eval₂ (Int.castRingHom K₁) θ₁ = 0)
    (root₂ : (Marking.polynomial s.second).eval₂ (Int.castRingHom K₂) θ₂ = 0)
    (A : ℝ) (hA : 0 < A) :
    let code := (orderedUnitRank places₁).sumCongr (orderedUnitRank places₂)
    let H := pairedHelmertMatrix code
    let σ₁ := orderedRealEmbeddings places₁
    let σ₂ := orderedRealEmbeddings places₂
    let M := H * markLogs σ₁ σ₂ (fun j : Fin rel.marks.length => (rel.marks.get j : K₁)-θ₁)
      (fun j => (rel.marks.get j : K₂)-θ₂) A
    let gap := Real.log 2 / (4*s.degree*(s.degree+1))
    let n := Fintype.card (UnitRankRows K₁ K₂)
    Submodule.span ℝ {y : UnitRankRows K₁ K₂ → ℝ | ∃ z : Fin rel.marks.length → ℤ,
      (∀ i, ∑ j, rel.matrix i j * z j = 0) ∧ y = M *ᵥ (fun j => (z j : ℝ))} = ⊤ →
    ∃ (select : UnitRankRows K₁ K₂ → Fin out.free) (u₁ : UnitRankRows K₁ K₂ → (𝓞 K₁)ˣ)
        (u₂ : UnitRankRows K₁ K₂ → (𝓞 K₂)ˣ),
      (∀ k, (u₁ k : K₁) = ∏ j, ((rel.marks.get j : K₁)-θ₁)^((out.directions.get (select k)).get j)) ∧
      (∀ k, (u₂ k : K₂) = ∏ j, ((rel.marks.get j : K₂)-θ₂)^((out.directions.get (select k)).get j)) ∧
      let v := fun k => (unitClass (u₁ k),unitClass (u₂ k))
      let B := (pairedUnitBasis K₁ K₂).toMatrix v
      let U := Matrix.of (fun i k => observeUnitPair σ₁ σ₂ H (v k) i)
      B.det ≠ 0 ∧ gap^n ≤ |U.det| ∧ ∀ T : ℝ, (∀ i j, |U i j| ≤ T) →
        |(B.det : ℝ)| ≤ n.factorial*T^n/gap^n := by
  intro code H σ₁ σ₂ M gap n span
  obtain ⟨select,u₁,u₂,h₁,h₂,nz⟩ := computed_field_unit_minor marked solved σ₁ σ₂ θ₁ θ₂
    root₁ root₂ A hA H span
  refine ⟨select,u₁,u₂,h₁,h₂,?_⟩
  intro v B U
  have both := paired_helmert_minor_bounds places₁ places₂ code (pairedUnitBasis K₁ K₂) v nz
  have existsT : ∃ T : ℝ, ∀ i j, |U i j| ≤ T := by
    refine ⟨∑ i, ∑ j, |U i j|,fun i j => ?_⟩
    exact (Finset.single_le_sum (f := fun k => |U i k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k => ∑ l, |U k l|) (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i))
  obtain ⟨T,hT⟩ := existsT
  exact ⟨nz,(both T hT).1,fun t ht => (both t ht).2⟩

end Cogentic
