import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Algebraic verification of the null vectors used by the sparse Wiedemann extractor. -/

namespace Cogentic.RandomizedSparseDependency

open Polynomial

section PolynomialAction

variable {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]

/-- Evaluating the quotient of an annihilator by X gives a kernel candidate. -/
theorem quotient_action_in_kernel (M : Module.End K V) (q : K[X]) (v : V)
    (h : (aeval M (X * q)) v = 0) :
    M ((aeval M q) v) = 0 := by
  rw [map_mul, aeval_X] at h
  exact h

/-- A minimal vector annihilator ensures that its quotient gives a nonzero candidate. -/
theorem quotient_action_ne_zero_of_minimal [Nontrivial K]
    (M : Module.End K V) (q : K[X]) (v : V) (hq : q ≠ 0)
    (minimal : ∀ r : K[X], r ≠ 0 → (aeval M r) v = 0 →
      (X * q).natDegree ≤ r.natDegree) :
    (aeval M q) v ≠ 0 := by
  intro hz
  have h := minimal q hq hz
  rw [monic_X.natDegree_mul' hq, natDegree_X] at h
  omega

end PolynomialAction

section Descent

variable {R K Row Col BasisIndex : Type*} [CommSemiring R] [Semiring K]
variable [Algebra R K] [Fintype Col]

/-- Any base-linear projection commutes with the action of a base-field matrix. -/
theorem project_mulVec (A : Matrix Row Col R) (w : Col → K) (project : K →ₗ[R] R)
    (hw : (A.map (algebraMap R K)).mulVec w = 0) :
    A.mulVec (fun j => project (w j)) = 0 := by
  funext i
  have hi := congrFun hw i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hi ⊢
  simpa only [← Algebra.smul_def, map_sum, map_smul, smul_eq_mul, map_zero]
    using congrArg project hi

/-- A nonzero extension-field kernel vector has a nonzero base-field kernel coordinate. -/
theorem exists_nonzero_kernel_coordinate (A : Matrix Row Col R) (w : Col → K)
    (b : Module.Basis BasisIndex R K) (hne : w ≠ 0)
    (hw : (A.map (algebraMap R K)).mulVec w = 0) :
    ∃ i : BasisIndex, (fun j => b.coord i (w j)) ≠ 0 ∧
      A.mulVec (fun j => b.coord i (w j)) = 0 := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  change w j ≠ 0 at hj
  obtain ⟨i, hi⟩ := not_forall.mp (mt b.forall_coord_eq_zero_iff.mp hj)
  refine ⟨i, ?_, project_mulVec A w (b.coord i) hw⟩
  intro hz
  exact hi (congrFun hz j)

/-- For a binary matrix the selected coordinate is a binary dependency. -/
theorem exists_binary_dependency [Algebra (ZMod 2) K]
    (A : Matrix Row Col (ZMod 2)) (w : Col → K) (b : Module.Basis BasisIndex (ZMod 2) K)
    (hne : w ≠ 0) (hw : (A.map (algebraMap (ZMod 2) K)).mulVec w = 0) :
    ∃ i : BasisIndex, (fun j => b.coord i (w j)) ≠ 0 ∧
      A.mulVec (fun j => b.coord i (w j)) = 0 :=
  exists_nonzero_kernel_coordinate A w b hne hw

end Descent

section PaddedMatrix

variable {K Row BasisIndex : Type*} [Field K] [Algebra (ZMod 2) K] [Fintype Row]

/-- Add one zero row at the extra index to square a rectangular binary matrix. -/
def padZeroRow (A : Matrix Row (Option Row) (ZMod 2)) : Matrix (Option Row) (Option Row) (ZMod 2)
  | none, _ => 0
  | some i, j => A i j

/-- The extension-field operator on the padded rows. -/
def paddedOperator (A : Matrix Row (Option Row) (ZMod 2)) : Module.End K (Option Row → K) :=
  ((padZeroRow A).map (algebraMap (ZMod 2) K)).mulVecLin

/-- A minimal vector annihilator with zero constant coefficient yields a binary
    dependency of the original rectangular matrix. -/
theorem binary_dependency_of_padded_minimal_annihilator
    (A : Matrix Row (Option Row) (ZMod 2)) (b : Module.Basis BasisIndex (ZMod 2) K)
    (v : Option Row → K) (p : K[X]) (hp : p ≠ 0) (hp0 : p.coeff 0 = 0)
    (hann : (aeval (paddedOperator A) p) v = 0)
    (minimal : ∀ r : K[X], r ≠ 0 → (aeval (paddedOperator A) r) v = 0 →
      p.natDegree ≤ r.natDegree) :
    ∃ w : Option Row → ZMod 2, w ≠ 0 ∧ A.mulVec w = 0 := by
  obtain ⟨q, rfl⟩ := X_dvd_iff.mpr hp0
  have hq : q ≠ 0 := by
    intro hz
    exact hp (by simp [hz])
  let w := (aeval (paddedOperator A) q) v
  have hne : w ≠ 0 := quotient_action_ne_zero_of_minimal (paddedOperator A) q v hq minimal
  have hker : ((padZeroRow A).map (algebraMap (ZMod 2) K)).mulVec w = 0 :=
    quotient_action_in_kernel (paddedOperator A) q v hann
  obtain ⟨i, hi, hz⟩ := exists_binary_dependency (padZeroRow A) w b hne hker
  refine ⟨fun j => b.coord i (w j), hi, ?_⟩
  funext j
  exact congrFun hz (some j)

end PaddedMatrix

#print axioms quotient_action_in_kernel
#print axioms quotient_action_ne_zero_of_minimal
#print axioms project_mulVec
#print axioms exists_nonzero_kernel_coordinate
#print axioms exists_binary_dependency
#print axioms binary_dependency_of_padded_minimal_annihilator

end Cogentic.RandomizedSparseDependency
