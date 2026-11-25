import Cogentic.PeeledCandidate
import Cogentic.TotalFactor

namespace Cogentic.Concrete
open Marking TwoThirdsSearch

/-- A purely algebraic witness at one grid point for the given target. All
rows, marks, polynomials, and root brackets are those selected by the program. -/
def BoxHasRank (n ell : ℕ) : Prop :=
  let b := n.log2+1
  let w₁ := 2*b^2*Fixed.U b
  let w₀ := w₁*Fixed.A b
  ∃ a a' c c', (1 ≤ a ∧ a ≤ w₀) ∧ (1 ≤ a' ∧ a' ≤ w₁) ∧
    (1 ≤ c ∧ c ≤ w₀) ∧ (1 ≤ c' ∧ c' ≤ w₁) ∧
    let s := TryPair.fixedInput n ell (Construction.construct n ell a a' c c')
    ∃ rel, stageOne s = some rel ∧ ∃ x : Bool → Fin s.degree → ℝ,
      (∀ side i, x side i ∈ Set.Icc ((RootLogs.bracket s side i).left:ℝ)
        ((RootLogs.bracket s side i).right:ℝ) ∧ RootLogs.normalized s.A (s.coeffs side) (x side i)=0) ∧
      PositiveMarkCore s rel x

theorem witness_of_box_rank {n ell : ℕ} (hn : 2 ≤ n) (big : 130000 ≤ Fixed.d (n.log2+1))
    (composite : ¬n.Prime) (target : ell ∈ dyadicTargets (Fixed.beta (n.log2+1)))
    (sieved : presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = none)
    (rank : BoxHasRank n ell) :
    let b := n.log2+1
    BoxWitness n (2*b^2*Fixed.U b*Fixed.A b) (2*b^2*Fixed.U b) (candidate n) ell := by
  obtain ⟨a,a',c,c',ha,ha',hc,hc',rel,marked,x,roots,core⟩ := rank
  refine ⟨a,a',c,c',ha,ha',hc,hc',?_⟩
  apply candidate_of_positive_mark_core hn big composite target sieved ⟨ha.2,ha'.2,hc.2,hc'.2⟩
  intro rel' h
  cases Option.some.inj (h.symm.trans marked)
  exact ⟨x,roots,core⟩

/-- On every sufficiently large composite surviving the preliminary tests,
a full-rank tuple for each dyadic target forces the actual splitter to
succeed before the total driver's trial-division fallback. -/
theorem fast_split_of_box_rank (line : DirichletLZerosOnLine) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (hn : 2 ≤ n) (bases : List ℕ), generatesUnits n bases →
      ¬n.Prime → ¬2 ∣ n → ¬IsPrimePow n →
      presieve n (n.log2+1) (Fixed.beta (n.log2+1)) (Fixed.A (n.log2+1)) (Fixed.rootBase n) = none →
      (∀ ell ∈ dyadicTargets (Fixed.beta (n.log2+1)), BoxHasRank n ell) →
      tryDivisor n hn bases ≠ none := by
  obtain ⟨m,fast⟩ := tryDivisor_of_coverage line
  obtain ⟨b₀,grow⟩ := Fixed.degree_grows 130000
  refine ⟨max m (2^b₀),fun n large hn bases gen composite odd npp absent ranks => ?_⟩
  apply fast n ((le_max_left ..).trans large) hn bases gen composite odd npp absent
  intro _ _ _ _ ell target
  have big := (Nat.le_log2 (show n≠0 by omega)).mpr ((le_max_right ..).trans large)
  exact witness_of_box_rank hn (grow _ (by omega)) composite target absent (ranks ell target)

end Cogentic.Concrete
