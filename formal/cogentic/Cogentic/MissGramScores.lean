import Cogentic.EmpiricalPairEntries
import Cogentic.MissLogMoments

namespace Cogentic.Construction
open Finset Real Window
open scoped Classical
noncomputable section

def rawMeshCount (b : ℕ) : ℝ :=
  (Fintype.card (Option (Bool×Fin (Fixed.d b))):ℝ)*cellMarkCount b

theorem rawMeshCount_pos (b : ℕ) : 0<rawMeshCount b :=
  mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr (Nat.pow_pos (by decide : 0<2)))

def missLogWeight (n ell : ℕ) (i j : Option (Bool×Fin (Fixed.d (n.log2+1)))) (a : ℕ) : ℝ :=
  let b := n.log2+1
  let f := fun t=>nominalLogFactor b i t*nominalLogFactor b j t
  let θ := (∑ c,∑ k∈range (cellMarkCount b),f (firstCellMark b c+k))/rawMeshCount b
  pooledMarkWeight univ (constructorCellMarks n ell)
    (fun _ t=>(if hitsTarget n ell t false then 0 else f t)-(1-(Fixed.d b:ℝ)/ell)*θ) a /
    smoothMarkProbability (PrescribedRows.unrestricted n ell) (PrescribedRows.unrestricted n ell) a

def missLogCost (n ell : ℕ) (x y : ℤ×ℤ) : ℝ :=
  let b := n.log2+1
  let O := PrescribedRows.unrestricted n ell
  let X := univ.biUnion (constructorCellMarks n ell)
  (∑ i,∑ j,(twoFieldScore X (missLogWeight n ell i j) (smoothMarkEvent O false)
    (smoothMarkEvent O true) x y)^2)/(rawMeshCount b)^2

def missPairCost (n ell : ℕ) (β : ℝ) (x y : ℤ×ℤ) : ℝ :=
  boxedPhysicalPairCost β (physicalPairMissWeight (n:=n) (ell:=ell) β) x y /
    (rawMeshCount (n.log2+1))^2

end
end Cogentic.Construction
