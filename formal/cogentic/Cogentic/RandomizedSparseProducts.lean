import Cogentic.RandomizedTaggedDependency
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basis

/-! The counters account for field operations. Indexed reads, writes, and
zero initialization are outside this arithmetic cost model. -/

namespace Cogentic.RandomizedSparseProducts

open Matrix
open Cogentic.RandomizedGramMinor Cogentic.RandomizedTaggedDependency Cogentic.RandomizedKrylovProbe

variable {K L E Row Col : Type*}
variable [DecidableEq Row] [DecidableEq Col]

/-- Each occurrence contributes one to its entry, including repeated pairs. -/
def occurrenceMatrix (K : Type*) [AddMonoid K] [One K]
    (row : E → Row) (col : E → Col) : List E → Matrix Row Col K
  | [] => 0
  | edge :: edges => Matrix.single (row edge) (col edge) 1 + occurrenceMatrix K row col edges

/-- One addition per occurrence, accumulated at the destination index. -/
def scatterPass [AddMonoid K] (row : E → Row) (col : E → Col) (x : Col → K) :
    List E → (Row → K) × ℕ
  | [] => (0, 0)
  | edge :: edges =>
    let tail := scatterPass row col x edges
    let i := row edge
    (Function.update tail.1 i (tail.1 i + x (col edge)), tail.2 + 1)

theorem scatterPass_spec [Semiring K] [Fintype Col]
    (row : E → Row) (col : E → Col) (x : Col → K) (edges : List E) :
    scatterPass row col x edges = ((occurrenceMatrix K row col edges).mulVec x, edges.length) := by
  induction edges with
  | nil => simp [scatterPass, occurrenceMatrix]
  | cons edge edges ih =>
    simp only [scatterPass, ih, occurrenceMatrix, add_mulVec, single_mulVec, one_mul, List.length_cons]
    congr 1
    funext i
    by_cases h : i = row edge
    · subst i
      simp [add_comm]
    · simp [Function.update_of_ne h]

theorem occurrenceMatrix_transpose [AddMonoid K] [One K]
    (row : E → Row) (col : E → Col) (edges : List E) :
    (occurrenceMatrix K row col edges)ᵀ = occurrenceMatrix K col row edges := by
  induction edges with
  | nil => simp [occurrenceMatrix]
  | cons edge edges ih => simp [occurrenceMatrix, transpose_add, transpose_single, ih]

theorem occurrenceMatrix_map [Semiring K] [Semiring L] (f : K →+* L)
    (row : E → Row) (col : E → Col) (edges : List E) :
    (occurrenceMatrix K row col edges).map f = occurrenceMatrix L row col edges := by
  induction edges with
  | nil => simp [occurrenceMatrix, Matrix.map_zero]
  | cons edge edges ih =>
    simp [occurrenceMatrix, Matrix.map_add f f.map_add, Matrix.map_single, ih]

/-- Multiply and store one value per index before the next sparse pass. -/
private def scaleOn [MulZeroClass K] (d x : Row → K) : List Row → (Row → K) × ℕ
  | [] => (0, 0)
  | i :: indices =>
    let tail := scaleOn d x indices
    (Function.update tail.1 i (d i * x i), tail.2 + 1)

private theorem scaleOn_spec [MulZeroClass K] (d x : Row → K) (indices : List Row) :
    (scaleOn d x indices).1 = (fun i => if i ∈ indices then d i * x i else 0) ∧
    (scaleOn d x indices).2 = indices.length := by
  induction indices with
  | nil => simp [scaleOn, Pi.zero_def]
  | cons index indices ih =>
    refine ⟨?_, by simp [scaleOn, ih.2]⟩
    funext i
    by_cases hi : i = index
    · subst i
      simp [scaleOn]
    · simp [scaleOn, hi, ih.1]

/-- An executable enumeration of the indices. With dimensions m and n, use
`IndexList.ofFin m` and `IndexList.ofFin n`. -/
structure IndexList (I : Type*) where
  indices : List I
  covers : ∀ i, i ∈ indices
  nodup : indices.Nodup

def IndexList.ofFin (n : ℕ) : IndexList (Fin n) :=
  ⟨List.finRange n, List.mem_finRange, List.nodup_finRange n⟩

private theorem IndexList.perm_univ {I : Type*} [Fintype I] (ix : IndexList I) :
    ix.indices.Perm (Finset.univ : Finset I).toList :=
  (List.perm_ext_iff_of_nodup ix.nodup (Finset.nodup_toList _)).mpr
    (fun i => iff_of_true (ix.covers i) (Finset.mem_toList.mpr (Finset.mem_univ i)))

private theorem IndexList.length {I : Type*} [Fintype I] (ix : IndexList I) :
    ix.indices.length = Fintype.card I := by
  simpa using ix.perm_univ.length_eq

private theorem scalePass_spec [MulZeroClass K] [Fintype Row] (d x : Row → K)
    (ix : IndexList Row) :
    scaleOn d x ix.indices = ((fun i => d i * x i), Fintype.card Row) := by
  obtain ⟨hv, hc⟩ := scaleOn_spec d x ix.indices
  exact Prod.ext (by simpa [ix.covers] using hv) (hc.trans ix.length)

/-- Two sparse passes through the same list. Counters are additions followed
by multiplications. Row and column weights are evaluated once per coordinate. -/
def gramPass [Semiring K] (rowIndices : IndexList Row) (colIndices : IndexList Col)
    (edges : List (Row × Col)) (d : Row → K) (e x : Col → K) : (Col → K) × ℕ × ℕ :=
  let forward := scatterPass Prod.fst Prod.snd x edges
  let rows := scaleOn d forward.1 rowIndices.indices
  let backward := scatterPass Prod.snd Prod.fst rows.1 edges
  let columns := scaleOn e backward.1 colIndices.indices
  (columns.1, forward.2 + backward.2, rows.2 + columns.2)

theorem gramPass_spec [CommRing K] [Fintype Row] [Fintype Col]
    (rowIndices : IndexList Row) (colIndices : IndexList Col) (edges : List (Row × Col)) (d : Row → K) (e x : Col → K) :
    gramPass rowIndices colIndices edges d e x =
      ((scaledGram (occurrenceMatrix K Prod.fst Prod.snd edges) d e).mulVec x,
        2 * edges.length, Fintype.card Row + Fintype.card Col) := by
  simp only [gramPass, scatterPass_spec, scalePass_spec, two_mul]
  congr 1
  rw [← occurrenceMatrix_transpose Prod.fst Prod.snd edges]
  have hrow : (fun i => d i * (occurrenceMatrix K Prod.fst Prod.snd edges *ᵥ x) i) =
      diagonal d *ᵥ (occurrenceMatrix K Prod.fst Prod.snd edges *ᵥ x) :=
    (funext (mulVec_diagonal _ _)).symm
  rw [hrow]
  funext j
  simp only [scaledGram, ← mulVec_mulVec, mulVec_diagonal]

/-- Application over a characteristic-two extension agrees with the tagged
operator for the binary matrix represented by the occurrences. -/
theorem tagged_gramPass_spec [Field K] [Algebra (ZMod 2) K] [Fintype Row] [Fintype Col]
    (rowIndices : IndexList Row) (colIndices : IndexList Col) (edges : List (Row × Col)) (d : Row → K) (e x : Col → K) :
    gramPass rowIndices colIndices edges d e x =
      (taggedOperator (occurrenceMatrix (ZMod 2) Prod.fst Prod.snd edges) d e x,
        2 * edges.length, Fintype.card Row + Fintype.card Col) := by
  rw [gramPass_spec, taggedOperator, mulVecLin_apply, occurrenceMatrix_map]

/-- A left-probe dot product uses one addition and multiplication per entry. -/
private def dotOn [AddMonoid K] [Mul K] (u x : Col → K) : List Col → K × ℕ
  | [] => (0, 0)
  | i :: indices =>
    let tail := dotOn u x indices
    (x i * u i + tail.1, tail.2 + 1)

omit [DecidableEq Col] in
private theorem dotOn_spec [AddMonoid K] [Mul K] (u x : Col → K) (indices : List Col) :
    dotOn u x indices = ((indices.map (fun i => x i * u i)).sum, indices.length) := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp [dotOn, ih]

/-- Record the moment at the current vector, then apply the sparse operator. -/
def taggedKrylovStep [Field K] (rowIndices : IndexList Row) (colIndices : IndexList Col)
    (edges : List (Row × Col)) (d : Row → K) (e u x : Col → K) :
    (Col → K) × K × ℕ × ℕ :=
  let gram := gramPass rowIndices colIndices edges d e x
  let moment := dotOn u x colIndices.indices
  (gram.1, moment.1, gram.2.1 + moment.2, gram.2.2 + moment.2)

/-- One moment and transition have exact field-operation counts, even for
rectangular matrices, empty rows and columns, or repeated occurrences. -/
theorem taggedKrylovStep_spec [Field K] [Algebra (ZMod 2) K] [Fintype Row] [Fintype Col]
    (rowIndices : IndexList Row) (colIndices : IndexList Col) (edges : List (Row × Col)) (d : Row → K) (e u x : Col → K) :
    taggedKrylovStep rowIndices colIndices edges d e u x =
      (taggedOperator (occurrenceMatrix (ZMod 2) Prod.fst Prod.snd edges) d e x,
        dotProbe u x, 2 * edges.length + Fintype.card Col,
        Fintype.card Row + Fintype.card Col + Fintype.card Col) := by
  simp only [taggedKrylovStep, tagged_gramPass_spec, dotOn_spec, colIndices.length]
  congr 1
  rw [(colIndices.perm_univ.map (fun i => x i * u i)).sum_eq]
  simp only [dotProbe, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Finset.sum_eq_multiset_sum,
    ← Finset.coe_toList, Multiset.map_coe, Multiset.sum_coe]

#print axioms scatterPass_spec
#print axioms tagged_gramPass_spec
#print axioms taggedKrylovStep_spec

end Cogentic.RandomizedSparseProducts
