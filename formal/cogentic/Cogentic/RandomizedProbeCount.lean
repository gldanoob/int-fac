import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Mul

/-! Exact counts for finite-field scalar probes. -/

namespace Cogentic.RandomizedProbeCount

section Fiber

variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

private def extendAtZero (j : I) (free : {i : I // i ≠ j} → K) (i : I) : K :=
  if hi : i = j then 0 else free ⟨i, hi⟩

/-- A nonzero pivot entry makes every assignment away from the pivot extend uniquely
    to a probe giving the specified scalar. -/
def probeFiberEquiv (w : I → K) (j : I) (hj : w j ≠ 0) (target : K) :
    {u : I → K // w ⬝ᵥ u = target} ≃ ({i : I // i ≠ j} → K) where
  toFun u i := u.val i
  invFun free :=
    let z := extendAtZero j free
    ⟨z + Pi.single j ((target - w ⬝ᵥ z) / w j), by
      rw [dotProduct_add, dotProduct_single, mul_comm (w j), div_mul_cancel₀ _ hj]
      simp⟩
  left_inv u := by
    apply Subtype.ext
    let z := extendAtZero j (fun i => u.val i)
    have hsplit : z + Pi.single j (u.val j) = u.val := by
      funext i
      by_cases hi : i = j
      · subst i
        simp [z, extendAtZero]
      · simp [z, extendAtZero, hi]
    have hsum : w ⬝ᵥ z + w j * u.val j = target := by
      rw [← dotProduct_single w (u.val j) j, ← dotProduct_add, hsplit]
      exact u.property
    have hpivot : u.val j = (target - w ⬝ᵥ z) / w j := by
      apply (eq_div_iff hj).2
      exact eq_sub_of_add_eq (by simpa [mul_comm, add_comm] using hsum)
    change z + Pi.single j ((target - w ⬝ᵥ z) / w j) = u.val
    rw [← hpivot, hsplit]
  right_inv free := by
    funext i
    simp [extendAtZero, i.property]

variable [Fintype K] [DecidableEq K]

/-- Every scalar fiber has q to the (n − 1) probes. -/
theorem card_probe_fiber (w : I → K) (j : I) (hj : w j ≠ 0) (target : K) :
    Fintype.card {u : I → K // w ⬝ᵥ u = target} =
      Fintype.card K ^ (Fintype.card I - 1) := by
  have hsingle : Fintype.card {i : I // i = j} = 1 := by simp
  rw [Fintype.card_congr (probeFiberEquiv w j hj target), Fintype.card_fun,
    Fintype.card_subtype_compl, hsingle]

/-- A nonzero vector determines a uniform scalar under a uniform probe. -/
theorem card_probe_fiber_of_nonzero (w : I → K) (hw : w ≠ 0) (target : K) :
    Fintype.card {u : I → K // w ⬝ᵥ u = target} =
      Fintype.card K ^ (Fintype.card I - 1) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  exact card_probe_fiber w i hi target

/-- The zero probes of a family of nonzero vectors obey the counting union bound. -/
theorem card_bad_probe_union {J : Type*} (tests : Finset J) (vectors : J → I → K)
    (hnonzero : ∀ j ∈ tests, vectors j ≠ 0) :
    (tests.biUnion fun j => Finset.univ.filter fun u : I → K => vectors j ⬝ᵥ u = 0).card ≤
      tests.card * Fintype.card K ^ (Fintype.card I - 1) := by
  apply Finset.card_biUnion_le_card_mul
  intro j hj
  rw [← Fintype.card_subtype]
  exact le_of_eq (card_probe_fiber_of_nonzero (vectors j) (hnonzero j hj) 0)

/-- Multiplying by the field size gives the union bound in the full probe space. -/
theorem card_bad_probe_union_mul_field_le [Nonempty I] {J : Type*}
    (tests : Finset J) (vectors : J → I → K) (hnonzero : ∀ j ∈ tests, vectors j ≠ 0) :
    (tests.biUnion fun j => Finset.univ.filter fun u : I → K => vectors j ⬝ᵥ u = 0).card *
      Fintype.card K ≤ tests.card * Fintype.card (I → K) := by
  have hpos : 0 < Fintype.card I := Fintype.card_pos
  calc
    _ ≤ (tests.card * Fintype.card K ^ (Fintype.card I - 1)) * Fintype.card K :=
      Nat.mul_le_mul_right _ (card_bad_probe_union tests vectors hnonzero)
    _ = _ := by
      rw [Nat.mul_assoc, ← pow_succ, Nat.sub_add_cancel hpos, Fintype.card_fun]

end Fiber

#print axioms probeFiberEquiv
#print axioms card_probe_fiber
#print axioms card_probe_fiber_of_nonzero
#print axioms card_bad_probe_union
#print axioms card_bad_probe_union_mul_field_le

end Cogentic.RandomizedProbeCount
