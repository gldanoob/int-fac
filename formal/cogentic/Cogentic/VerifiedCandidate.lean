import Cogentic.Concrete

namespace Cogentic.Concrete
open Marking TwoThirdsSearch

/-- Passing first and second stages and one nonsingular verifiable minor
produces a checked hit from this exact grid point in the outer search. -/
theorem candidate_of_minor {n g a b c d : ℕ} :
    let s := TryPair.fixedInput n g (Construction.construct n g a b c d)
    ∀ {rel : Relations}, stageOne s = some rel →
    ∀ {lattice : Elimination.IntegerFamily rel.marks.length}, Elimination.stageTwo rel = some lattice →
    lattice.free < rel.marks.length ∧ 2*s.degree-2 ≤ lattice.free →
    ∀ {cols}, markColumns s rel = some cols →
    let P := TryPair.localBits s rel
    let rhs := observation cols lattice.particular P
    let obs := lattice.directions.map (fun direction => observation cols direction P)
    let Q := TryPair.denominatorCap s rel
    let cap := min P (Fixed.precision (n.log2+1))
    ∀ idx : List (Fin lattice.free), idx.Sublist (List.finRange lattice.free) →
    ∀ len : idx.length = 2*s.degree-2,
    let M := minorMatrix obs ((Vector.ofFn idx.get).cast len)
    M.det ≠ 0 → (∀ y, M.mulVec y = (fun i => -(rhs.get i:ℚ)) →
      verify n g (reconstructedProposal y Q lattice.scale cap) ≠ none) →
    verify n g (candidate n g a b c d) ≠ none := by
  intro s rel first lattice second guard cols columns P rhs obs Q cap idx sub len M det cert
  obtain ⟨x,found,valid⟩ := minor_search_verifies rhs obs idx sub len det cert
  have success : arch s rel lattice = some x := by
    unfold arch
    rw [columns]
    exact found
  change verify n g ((stageOne s).bind (fun r =>
    (Elimination.stageTwo r).bind (TryPair.finish arch s r))) ≠ none
  rw [first]
  change verify n g ((Elimination.stageTwo rel).bind (TryPair.finish arch s rel)) ≠ none
  rw [second]
  change verify n g (TryPair.finish arch s rel lattice) ≠ none
  unfold TryPair.finish
  rw [if_pos guard,success]
  exact valid

end Cogentic.Concrete
