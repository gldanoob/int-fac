import Cogentic.RandomizedPadeSolver
import Cogentic.RandomizedTaggedDependency

open scoped Polynomial

namespace Cogentic.RandomizedTaggedDependency

open Polynomial
open Cogentic.RandomizedGramMinor Cogentic.RandomizedKrylovProbe
open Cogentic.RandomizedPadeRecurrence Cogentic.RandomizedSingularProbe

variable {K Row Col Tag BasisIndex : Type*} [Field K] [Algebra (ZMod 2) K]
variable [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]
variable [DecidableEq K] [Fintype K]

/-- Success of the Euclidean tagged solver means that one binary coordinate
of the quotient action satisfies the constraints and has a nonzero tag. -/
def TaggedSolverSucceeds (M : Matrix Row Col (ZMod 2)) (H : Matrix Tag Col (ZMod 2))
    (b : Module.Basis BasisIndex (ZMod 2) K) (d : Row → K) (e : Col → K)
    (x u : Col → K) : Prop :=
  let S := taggedOperator M d e
  let g := euclideanRecurrence (Fintype.card Col) (fun j => dotProbe u ((S ^ j) x))
  g.coeff 0 = 0 ∧ ∃ bit : BasisIndex,
    let v := (aeval S (g /ₘ X)) x
    M.mulVec (fun j => b.coord bit (v j)) = 0 ∧
      H.mulVec (fun j => b.coord bit (v j)) ≠ 0

/-- The Euclidean output itself gives a tagged binary dependency for a good
scaled Gram matrix, tagged kernel component, and detecting left probe. -/
theorem tagged_solver_of_good_probe
    (M : Matrix Row Col (ZMod 2)) (H : Matrix Tag Col (ZMod 2))
    (b : Module.Basis BasisIndex (ZMod 2) K) (d : Row → K) (e : Col → K)
    (hdiag : (scaledGram (M.map (algebraMap (ZMod 2) K)) d e).charpoly.coeff
      (Fintype.card Col - (M.map (algebraMap (ZMod 2) K)).rank) ≠ 0)
    (x u z w : Col → K) (hx : x = z + w)
    (hz : z ∈ (M.map (algebraMap (ZMod 2) K)).mulVecLin.ker)
    (hw : w ∈ (taggedOperator M d e).range)
    (hTag : (H.map (algebraMap (ZMod 2) K)).mulVec z ≠ 0)
    (p : K[X]) (hp : p.Monic) (hpann : (aeval (taggedOperator M d e) p) x = 0)
    (hpdeg : p.natDegree ≤ Fintype.card Col)
    (pmin : ∀ r : K[X], r ≠ 0 → (aeval (taggedOperator M d e) r) x = 0 →
      p.natDegree ≤ r.natDegree)
    (hprobe : u ∉ missedFactorProbes (taggedOperator M d e) x p) :
    euclideanRecurrence (Fintype.card Col)
        (fun j => dotProbe u (((taggedOperator M d e) ^ j) x)) = p ∧
      TaggedSolverSucceeds M H b d e x u := by
  let S := taggedOperator M d e
  let n := Fintype.card Col
  let a := fun j : ℕ => dotProbe u ((S ^ j) x)
  have hpfit : FitsTruncatedRecurrence (2 * n) p.natDegree a p := by
    intro j _
    exact (shift_probe_eq_sum S x (dotProbe u) p j).symm.trans
      (probe_annihilates_of_vector S x (dotProbe u) p hpann (X ^ j))
  obtain ⟨hg, hgn, hgfit, hgmin⟩ := euclideanRecurrence_spec n a p hp hpdeg hpfit
  have hfitmin (q : K[X]) (hq : q ≠ 0) (hqn : q.natDegree ≤ n)
      (hqfit : KrylovRecurrenceFits S x (dotProbe u) n q) :
      (euclideanRecurrence n a).natDegree ≤ q.natDegree := by
    have hqann := probe_annihilates_of_prefix S x (dotProbe u) p q hp hpann (fun j hj => by
      rw [shift_probe_eq_sum]
      exact hqfit j (hj.trans_le hpdeg))
    let c := q.leadingCoeff⁻¹
    have hdeg : (q * C c).natDegree = q.natDegree :=
      natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hq))
    have hfit : FitsTruncatedRecurrence (2 * n) (q * C c).natDegree a (q * C c) := by
      intro j _
      rw [← shift_probe_eq_sum S x (dotProbe u) (q * C c) j]
      rw [show X ^ j * (q * C c) = (X ^ j * C c) * q by ac_rfl]
      exact hqann _
    exact (hgmin (q * C c) (monic_mul_leadingCoeff_inv hq) (hdeg.trans_le hqn) hfit).trans_eq hdeg
  exact tagged_dependency_of_good_finite_probe M H b d e hdiag x u z w hx hz hw hTag
    p (euclideanRecurrence n a) hp hg hpann pmin hpdeg hgn hprobe
    (fits_first_n_of_truncated n _ a _ hgn rfl hgfit) hfitmin

/-- Left probes for which the actual Euclidean output has no tagged binary
coordinate or its constant coefficient is nonzero. -/
noncomputable def badTaggedSolverProbes (M : Matrix Row Col (ZMod 2))
    (H : Matrix Tag Col (ZMod 2)) (b : Module.Basis BasisIndex (ZMod 2) K)
    (d : Row → K) (e : Col → K) (x : Col → K) : Finset (Col → K) := by
  classical
  exact Finset.univ.filter (fun u => ¬TaggedSolverSucceeds M H b d e x u)

/-- For fixed good diagonals and a tagged start, the fraction of probes
on which the actual solver fails is at most the column count divided by
the field size. The vector annihilator is chosen in the proof. -/
theorem card_bad_tagged_solver_probes [Nonempty Col]
    (M : Matrix Row Col (ZMod 2)) (H : Matrix Tag Col (ZMod 2))
    (b : Module.Basis BasisIndex (ZMod 2) K) (d : Row → K) (e : Col → K)
    (hdiag : (scaledGram (M.map (algebraMap (ZMod 2) K)) d e).charpoly.coeff
      (Fintype.card Col - (M.map (algebraMap (ZMod 2) K)).rank) ≠ 0)
    (x z w : Col → K) (hx : x = z + w)
    (hz : z ∈ (M.map (algebraMap (ZMod 2) K)).mulVecLin.ker)
    (hw : w ∈ (taggedOperator M d e).range)
    (hTag : (H.map (algebraMap (ZMod 2) K)).mulVec z ≠ 0) :
    (badTaggedSolverProbes M H b d e x).card * Fintype.card K ≤
      Fintype.card Col * Fintype.card (Col → K) := by
  classical
  let S := taggedOperator M d e
  obtain ⟨p, hp, hpann, hpdeg, pmin⟩ := exists_minimal_vector_annihilator S x
  have hsub : badTaggedSolverProbes M H b d e x ⊆ missedFactorProbes S x p := by
    intro u hu
    by_contra hprobe
    have hfail : ¬TaggedSolverSucceeds M H b d e x u :=
      (Finset.mem_filter.mp hu).2
    exact hfail (tagged_solver_of_good_probe M H b d e hdiag x u z w hx hz hw hTag
      p hp hpann hpdeg pmin hprobe).2
  exact ((Nat.mul_le_mul_right _ (Finset.card_le_card hsub)).trans
    (card_missed_factor_probes S x p hp pmin)).trans (Nat.mul_le_mul_right _ hpdeg)

#print axioms tagged_solver_of_good_probe
#print axioms card_bad_tagged_solver_probes

end Cogentic.RandomizedTaggedDependency
