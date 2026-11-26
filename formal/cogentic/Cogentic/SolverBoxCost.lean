import Cogentic.SolverArithmeticCost
import Cogentic.ExhaustiveMarkCost

namespace Cogentic.SolverStage
open Concrete Elimination Finset

/-- A stage-one hit always reaches relation elimination. Later guards enable
the enumeration and the square solves on every selected minor. -/
def trialWork (n g u v w z : ℕ) : ℕ :=
  let s := TryPair.fixedInput n g (Construction.construct n g u v w z)
  match Marking.stageOne s with
  | none => 0
  | some rel =>
    solverWork (relationRows rel) + match stageTwo rel with
    | none => 0
    | some lat => if lat.free < rel.marks.length ∧ 2*s.degree-2 ≤ lat.free then
        match markColumns s rel with
        | none => 0
        | some cols =>
          let P := TryPair.localBits s rel
          let rhs := observation cols lat.particular P
          let obs := lat.directions.map (fun dir => observation cols dir P)
          (MinorEnumeration.counted (2*s.degree-2) (List.finRange lat.free) id []).2 +
          ((selections (2*s.degree-2) lat.free).map (minorWork rhs obs)).sum
      else 0

theorem exhaustive_solver_gates {n : ℕ} (hn : 2≤n) (big : 10004≤Fixed.d (n.log2+1)) :
    boxWork n (trialWork n) ≤ 2^(10441014*TwoThirdsCost.scale (n.log2+1)) := by
  apply boxWork_le n 10020002
  intro g target u hu v hv w hw z hz
  let b := n.log2+1
  let S := TwoThirdsCost.scale b
  have vs : Fixed.v b ≤ S := (Fixed.scale_bounds (Nat.succ_pos _)).1
  have sp : 0<S := (Nat.mul_pos (Fixed.degree_pos (Nat.succ_pos _))
    (Nat.mul_pos (Fixed.degree_pos (Nat.succ_pos _)) (Nat.succ_pos _))).trans_le vs
  dsimp only [trialWork]
  split
  next => exact Nat.zero_le _
  next rel stage =>
    have relCost := relation_work stage
    have relax : solverWork (relationRows rel) ≤ 2^(10020001*S) := relCost.trans
      (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : 10000000*S ≤ 10020001*S))
    apply (Nat.add_le_add relax _).trans
    · calc
        _ = 2^(1+10020001*S) := by rw [pow_add,pow_one,two_mul]
        _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by change 1+10020001*S ≤ 10020002*S; omega)
    · split
      next => exact Nat.zero_le _
      next lat success =>
        split
        next guard =>
          split
          next => exact Nat.zero_le _
          next cols marked =>
            let C := 2^(10000000*S)
            let s := TryPair.fixedInput n g (Construction.construct n g u v w z)
            let rhs := observation cols lat.particular (TryPair.localBits s rel)
            let obs := lat.directions.map (fun dir => observation cols dir (TryPair.localBits s rel))
            have one (idx : List (Fin lat.free)) : minorWork rhs obs idx ≤ C := minor_work hn big target
              ⟨(mem_Icc.mp hu).2,(mem_Icc.mp hv).2,(mem_Icc.mp hw).2,(mem_Icc.mp hz).2⟩ stage success marked idx
            have total (xs : List (List (Fin lat.free))) : (xs.map (minorWork rhs obs)).sum≤xs.length*C := by
              induction xs with
              | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,le_refl]
              | cons x xs ih =>
                simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
                exact (Nat.add_le_add (one x) ih).trans_eq (Nat.add_comm ..)
            have count := (per_candidate_minor_count stage guard.1).trans
              (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_left 20000 vs))
            have work := (total (selections (2*s.degree-2) lat.free)).trans
              ((Nat.mul_le_mul_right C count).trans_eq
                (by dsimp only [C]; rw [←pow_add]; congr 1; ring : _ = 2^(10020000*S)))
            have visits := (MinorEnumeration.fixed_selection_visits stage guard.1).trans
              (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : 20005*Fixed.v b ≤ 10020000*S))
            exact (Nat.add_le_add visits work).trans (calc
              _ = 2^(1+10020000*S) := by rw [pow_add,pow_one,two_mul]
              _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
        next => exact Nat.zero_le _

end Cogentic.SolverStage

#print axioms Cogentic.SolverStage.exhaustive_solver_gates
