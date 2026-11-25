import Cogentic.GramCandidate
import Cogentic.Rank

/-! Sufficient positivity condition on subsets of the executable incidence
rows and retained marks. -/

namespace Cogentic
open scoped Matrix BigOperators
open Marking TwoThirdsSearch

/-- A weighted joint Gram on selected incidence rows and mark columns.
An omitted row has zero target and vanishes on every selected column. -/
def PositiveMarkCore (s : Input) (rel : Relations) (x : Bool → Fin s.degree → ℝ) : Prop :=
  ∃ (I : Finset (Fin (rel.rows.length+1))) (J : Finset (Fin rel.marks.length))
    (scale : I → ℝ) (W : Matrix J J ℝ),
    (∀ i, scale i ≠ 0) ∧ (∀ i ∉ I, rel.rhs i = 0) ∧
    (∀ i ∉ I, ∀ j ∈ J, rel.matrix i j = 0) ∧
    let V : Matrix (I ⊕ Fin (2*s.degree-2)) J ℝ := jointRows (rel.matrix.submatrix Subtype.val Subtype.val) scale
      ((bracketMarkMatrix s rel x).submatrix id Subtype.val)
    (V * W * V.transpose).PosDef

private def zeroExtend {ι R : Type*} [DecidableEq ι] [Zero R] (S : Finset ι) (c : S → R) (j : ι) : R :=
  if h : j ∈ S then c ⟨j,h⟩ else 0

private theorem sum_mul_zeroExtend {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]
    (S : Finset ι) (a : ι → R) (c : S → R) :
    ∑ j, a j * zeroExtend S c j = ∑ j : S, a j.val * c j := by
  calc
    _ = ∑ j ∈ S, a j * zeroExtend S c j := (Finset.sum_subset (Finset.subset_univ S)
      (fun j _ hj => by simp [zeroExtend,hj])).symm
    _ = ∑ j : S, a j.val * zeroExtend S c j.val := (Finset.sum_coe_sort S _).symm
    _ = _ := Finset.sum_congr rfl (fun j _ => by simp [zeroExtend,j.prop])

/-- Padding an exact relation on selected marks by zero restores all the
original incidence and archimedean coordinates. -/
theorem PositiveMarkCore.descent {s : Input} {rel : Relations} {x : Bool → Fin s.degree → ℝ}
    (core : PositiveMarkCore s rel x) :
    (∃ t : Fin rel.marks.length → ℚ, ∀ i, ∑ j, (rel.matrix i j:ℚ)*t j = -(rel.rhs i:ℚ)) ∧
      Submodule.span ℝ {y : Fin (2*s.degree-2) → ℝ | ∃ z : Fin rel.marks.length → ℤ,
        (∀ i, ∑ j, rel.matrix i j*z j=0) ∧ y=bracketMarkMatrix s rel x *ᵥ (fun j => (z j:ℝ))} = ⊤ := by
  classical
  obtain ⟨I,J,scale,W,nz,target,support,gram⟩ := core
  let A : Matrix I J ℤ := rel.matrix.submatrix Subtype.val Subtype.val
  let M := bracketMarkMatrix s rel x
  let U : Matrix (Fin (2*s.degree-2)) J ℝ := M.submatrix id Subtype.val
  obtain ⟨affine,span⟩ := positive_gram_descent A scale nz U W gram
  constructor
  · obtain ⟨c,hc⟩ := affine (fun i => -rel.rhs i.val)
    refine ⟨zeroExtend J c,fun i => ?_⟩
    rw [sum_mul_zeroExtend]
    by_cases h : i∈I
    · simpa only [A,Matrix.submatrix_apply,Int.cast_neg] using hc ⟨i,h⟩
    · simp [fun j : J => support i h j j.prop,target i h]
  · rw [← top_le_iff,← span]
    apply Submodule.span_le.mpr
    rintro y ⟨z,hz,rfl⟩
    apply Submodule.subset_span
    refine ⟨zeroExtend J z,fun i => ?_,?_⟩
    · rw [sum_mul_zeroExtend]
      by_cases h : i∈I
      · exact hz ⟨i,h⟩
      · simp [fun j : J => support i h j j.prop]
    · funext i
      have cast (j) : ((zeroExtend J z j : ℤ):ℝ) = zeroExtend J (fun k => (z k:ℝ)) j := by
        by_cases h : j∈J <;> simp [zeroExtend,h]
      simp only [Matrix.mulVec,dotProduct,cast,sum_mul_zeroExtend]
      rfl

/-- A positive Gram on the surviving rows and columns at one concrete grid
point suffices for the executable to return a separately verified proposal. -/
theorem candidate_of_positive_mark_core {N ell a b c d : ℕ} (hn : 2 ≤ N)
    (big : 130000 ≤ Fixed.d (N.log2+1)) (composite : ¬N.Prime)
    (target : ell ∈ dyadicTargets (Fixed.beta (N.log2+1)))
    (sieved : presieve N (N.log2+1) (Fixed.beta (N.log2+1)) (Fixed.A (N.log2+1))
      (Fixed.rootBase N) = none)
    (box : let bits := N.log2+1
      a ≤ 2*bits^2*Fixed.U bits*Fixed.A bits ∧ b ≤ 2*bits^2*Fixed.U bits ∧
      c ≤ 2*bits^2*Fixed.U bits*Fixed.A bits ∧ d ≤ 2*bits^2*Fixed.U bits) :
    let s := TryPair.fixedInput N ell (Construction.construct N ell a b c d)
    (∀ rel, stageOne s = some rel → ∃ x : Bool → Fin s.degree → ℝ,
      (∀ side i, x side i ∈ Set.Icc ((RootLogs.bracket s side i).left:ℝ)
        ((RootLogs.bracket s side i).right:ℝ) ∧ RootLogs.normalized s.A (s.coeffs side) (x side i)=0) ∧
      PositiveMarkCore s rel x) →
    verify N ell (Concrete.candidate N ell a b c d) ≠ none := by
  intro s core
  apply candidate_of_concrete_spans hn big composite target sieved box
  intro rel marked
  obtain ⟨x,roots,positive⟩ := core rel marked
  obtain ⟨feasible,spans⟩ := positive.descent
  exact ⟨feasible,x,roots,spans⟩

end Cogentic

#print axioms Cogentic.candidate_of_positive_mark_core
