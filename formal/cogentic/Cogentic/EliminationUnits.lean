import Cogentic.Pivot
import Cogentic.Elimination

/-! Finite-place and unit-rank consequences of the executable marking and elimination stages. -/

open NumberField Polynomial Matrix
open scoped BigOperators NumberField Polynomial Matrix

namespace Cogentic
open Marking

private theorem value_eq (cs : List ℤ) (a : ℕ) :
    value cs a = ((polynomial cs).eval (a : ℤ)).natAbs := by
  simp only [value, horner_correct]
  rfl

private theorem eval_mod (f : ℤ[X]) (a p : ℕ) :
    f.eval₂ (Int.castRingHom (ZMod p)) ((a%p : ℕ) : ZMod p) =
      ((f.eval (a : ℤ) : ℤ) : ZMod p) := by
  rw [ZMod.natCast_mod]
  simpa only [Int.coe_castRingHom, Int.cast_natCast] using
    (Polynomial.eval₂_at_apply (p := f) (Int.castRingHom (ZMod p)) (a : ℤ))

private theorem mark_congruence (a b p : ℕ) :
    a % p = b % p ↔ (p : ℤ) ∣ (a : ℤ) - b := by
  rw [← ZMod.natCast_eq_natCast_iff', ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    Int.cast_sub, Int.cast_natCast, Int.cast_natCast, sub_eq_zero]

/-- Every prime factor of an actual retained mark has its simple residue row
in the output list. This connects the integer Horner/mark guards to the
valuation theorem for an arbitrary root in a number field. -/
theorem stageOne_affine_rows {s : Input} {rel : Relations} (ok : stageOne s = some rel) (side : Bool) :
    AffineMarkRows (polynomial (s.coeffs side)) (fun j => (rel.marks.get j : ℤ)) rel.matrix := by
  classical
  let f := polynomial (s.coeffs side)
  have data (j : Fin rel.marks.length) :=
    (retained_iff ok _).mp (List.get_mem rel.marks j)
  have smooth (j : Fin rel.marks.length) : SquarefreeSmooth s.base
      ((f.eval (rel.marks.get j : ℤ)).natAbs) := by
    cases side with
    | false => simpa only [f, Input.coeffs, Bool.false_eq_true, if_false, ← value_eq] using (data j).2.1
    | true => simpa only [f, Input.coeffs, if_true, ← value_eq] using (data j).2.2.1
  have listed (p : ℕ) (hp : p.Prime) (j : Fin rel.marks.length)
      (div : (p : ℤ) ∣ f.eval (rel.marks.get j : ℤ)) :
      let row := Row.mk side p (rel.marks.get j % p)
      row ∈ s.clean := by
    let a := rel.marks.get j
    let row := Row.mk side p (a % p)
    have hpn : p ∣ (f.eval (a : ℤ)).natAbs := by simpa only [a, Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr div
    have base := (smooth j).2.2 p hp hpn
    have root : row ∈ s.rows := mem_rows.mpr ⟨base, Nat.mod_lt _ hp.pos, by
      change f.eval₂ (Int.castRingHom (ZMod p)) ((a%p : ℕ) : ZMod p) = 0
      rw [eval_mod]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr div⟩
    change row ∈ s.rows.filter _
    apply List.mem_filter.mpr
    refine ⟨root, ?_⟩
    cases hbad : row.bad s with
    | false => rfl
    | true =>
      have bad : row ∈ s.badRows := List.mem_filter.mpr ⟨root,hbad⟩
      exact ((data j).2.2.2.2 row bad rfl).elim
  constructor
  · intro p hp j hd
    have h := (mem_clean.mp (listed p hp j hd)).2.1
    have evalD := eval_mod f.derivative (rel.marks.get j) p
    refine ⟨?_,fun he => h (evalD.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr he))⟩
    intro square
    have sq := (Nat.squarefree_iff_prime_squarefree.mp (smooth j).2.1) p hp
    apply sq
    simpa only [f, pow_two, Int.natAbs_mul, Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr square
  · intro p hp j hd
    let row := Row.mk side p (rel.marks.get j % p)
    obtain ⟨_,_,_,eq,_⟩ := rows_and_guards ok
    have mem : row ∈ rel.rows := eq ▸ listed p hp j hd
    obtain ⟨id, hid⟩ := List.mem_iff_get.mp mem
    refine ⟨id.succ, fun k => ?_⟩
    change (if rel.marks.get k % (rel.rows.get id).q = (rel.rows.get id).r then _ else _) = _
    rw [hid]
    simp only [row, mark_congruence]


/-- The actual independently scaled vectors emitted by executable rational
elimination span the same archimedean space as all integer relations. -/
theorem stageTwo_observation_span {ν : Type*} {rel : Relations} {out : Elimination.IntegerFamily rel.marks.length}
    (ok : Elimination.stageTwo rel = some out) (U : Matrix ν (Fin rel.marks.length) ℝ)
    (sp : Submodule.span ℝ {y : ν → ℝ | ∃ z : Fin rel.marks.length → ℤ,
      (∀ i, ∑ j, rel.matrix i j * z j = 0) ∧ y = U *ᵥ (fun j => (z j : ℝ))} = ⊤) :
    Submodule.span ℝ (Set.range (fun k => U *ᵥ
      (fun j => ((out.directions.get k).get j : ℝ)))) = ⊤ := by
  classical
  let S := Submodule.span ℝ (Set.range (fun k => U *ᵥ (fun j => ((out.directions.get k).get j : ℝ))))
  change S = ⊤
  rw [← top_le_iff, ← sp]
  apply Submodule.span_le.mpr
  rintro _ ⟨z,hz,rfl⟩
  let x (j) : ℚ := z j
  have hq (i) : ∑ j, (rel.matrix i j : ℚ) * x j = 0 := by dsimp only [x]; exact_mod_cast hz i
  have rep := (Elimination.stageTwo_verified ok).2.2.2 x hq
  let coeff (k) := x (out.position k) / (out.scales.get k : ℚ)
  have decomp : ∑ k, (coeff k : ℝ) • (fun j => ((out.directions.get k).get j : ℝ)) =
      fun j => (z j : ℝ) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have h := (rep j).symm
    change ∑ k, coeff k * ((out.directions.get k).get j : ℚ) = (z j : ℚ) at h
    exact_mod_cast h
  change U *ᵥ (fun j => (z j : ℝ)) ∈ S
  rw [← decomp, Matrix.mulVec_sum]
  exact S.sum_mem (fun k _ => by
    rw [Matrix.mulVec_smul]
    exact S.smul_mem _ (Submodule.subset_span ⟨k,rfl⟩))

/-- A successful marking and elimination run supplies the actual free columns
from which a full paired integer unit minor can be selected. -/
theorem computed_field_unit_minor {K₁ K₂ α β : Type*} [Field K₁] [Field K₂]
    [NumberField K₁] [NumberField K₂] [Fintype α] [Fintype β]
    {s : Input} {rel : Relations} {out : Elimination.IntegerFamily rel.marks.length}
    (marked : stageOne s = some rel) (solved : Elimination.stageTwo rel = some out)
    (σ₁ : α → K₁ →+* ℝ) (σ₂ : β → K₂ →+* ℝ) (θ₁ : K₁) (θ₂ : K₂)
    (root₁ : (polynomial s.first).eval₂ (Int.castRingHom K₁) θ₁ = 0)
    (root₂ : (polynomial s.second).eval₂ (Int.castRingHom K₂) θ₂ = 0)
    (A : ℝ) (hA : 0 < A) (H : Matrix (UnitRankRows K₁ K₂) (α ⊕ β) ℝ)
    (sp : let U := H * markLogs σ₁ σ₂ (fun j => (rel.marks.get j : K₁)-θ₁)
              (fun j => (rel.marks.get j : K₂)-θ₂) A
          Submodule.span ℝ {y : UnitRankRows K₁ K₂ → ℝ | ∃ z : Fin rel.marks.length → ℤ,
            (∀ i, ∑ j, rel.matrix i j * z j = 0) ∧ y = U *ᵥ (fun j => (z j : ℝ))} = ⊤) :
    ∃ (select : UnitRankRows K₁ K₂ → Fin out.free)
      (u₁ : UnitRankRows K₁ K₂ → (𝓞 K₁)ˣ) (u₂ : UnitRankRows K₁ K₂ → (𝓞 K₂)ˣ),
      (∀ k, (u₁ k : K₁) = ∏ j, ((rel.marks.get j : K₁)-θ₁)^((out.directions.get (select k)).get j)) ∧
      (∀ k, (u₂ k : K₂) = ∏ j, ((rel.marks.get j : K₂)-θ₂)^((out.directions.get (select k)).get j)) ∧
      ((pairedUnitBasis K₁ K₂).toMatrix (fun k => (unitClass (u₁ k), unitClass (u₂ k)))).det ≠ 0 := by
  have null := (Elimination.stageTwo_verified solved).2.2.1
  have rows₁ := stageOne_affine_rows marked false
  have rows₂ := stageOne_affine_rows marked true
  have span := stageTwo_observation_span solved _ sp
  simpa only [Int.cast_natCast] using select_clean_unit_columns σ₁ σ₂ (fun j => (rel.marks.get j : ℤ))
    rel.matrix (polynomial s.first) (polynomial s.second) θ₁ θ₂ root₁ root₂ rows₁ rows₂ 0 (fun _ => rfl)
    A hA H (fun k j => (out.directions.get k).get j) (fun k => (null k).2.1) (by simpa only [Int.cast_natCast] using span)

end Cogentic
