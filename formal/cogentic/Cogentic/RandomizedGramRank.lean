import Cogentic.RandomizedGramMinor
import Cogentic.RandomizedSemisimpleZero
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Rank and kernel consequences of a nonzero scaled Gram coefficient. -/

namespace Cogentic.RandomizedGramRank

open Matrix Module RandomizedGramMinor
open scoped BigOperators

variable {K Row Col : Type*} [Field K]
variable [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]

private theorem det_ne_zero_of_full_rank (A : Matrix Col Col K)
    (h : A.rank = Fintype.card Col) : A.det ≠ 0 := by
  have hd := A.mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank, h, finrank_pi] at hd
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    omega
  have hi : Function.Injective A.mulVec := LinearMap.ker_eq_bot.mp hker
  exact ((A.isUnit_iff_isUnit_det).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp (Matrix.mulVec_injective_iff.mp hi))).ne_zero

omit [Fintype Row] [DecidableEq Row] [DecidableEq Col] in
private theorem exists_columns_with_rank (M : Matrix Row Col K) :
    ∃ J : Finset Col, J.card = M.rank ∧
      (M.submatrix id (Subtype.val : J → Col)).rank = M.rank := by
  classical
  obtain ⟨s, -, -, hsp, hli⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty K M.col) (Set.empty_subset (Set.univ : Set Col))
  let J := (Set.toFinite s).toFinset
  have hJ : (J : Set Col) = s := (Set.toFinite s).coe_toFinset
  have hjli : LinearIndependent K (fun j : J => M.col j) := by
    change LinearIndepOn K M.col (J : Set Col)
    rwa [hJ]
  have hrange : Set.range (fun j : J => M.col j) = M.col '' s := by
    rw [← hJ]
    ext x
    simp
  have hspan : Submodule.span K (Set.range (fun j : J => M.col j)) =
      Submodule.span K (Set.range M.col) := by
    rw [hrange]
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_subset_range _ _)
    · exact Submodule.span_le.mpr (by simpa using hsp)
  have hrank : (M.submatrix id (Subtype.val : J → Col)).rank = M.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, M.rank_eq_finrank_span_cols, ← hspan]
    rfl
  refine ⟨J, ?_, hrank⟩
  rw [M.rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hjli, Fintype.card_coe]

omit [DecidableEq Row] in
/-- Two successive selections of a basis from the columns give a rank-sized nonsingular minor. -/
theorem exists_rank_minor (M : Matrix Row Col K) :
    ∃ (I : Finset Row) (J : Finset Col) (index : J ≃ I), J.card = M.rank ∧
      (selectedMinor M I J index).det ≠ 0 := by
  obtain ⟨J, hJ, hj⟩ := exists_columns_with_rank M
  let A := M.submatrix id (Subtype.val : J → Col)
  obtain ⟨I, hI, hi⟩ := exists_columns_with_rank Aᵀ
  have heq : Fintype.card J = Fintype.card I := by
    rw [Fintype.card_coe, Fintype.card_coe, hJ, hI, Matrix.rank_transpose, hj]
  let index := Fintype.equivOfCardEq heq
  refine ⟨I, J, index, hJ, det_ne_zero_of_full_rank _ ?_⟩
  have he : selectedMinor M I J index =
      ((Aᵀ.submatrix id (Subtype.val : I → Row))ᵀ).submatrix index (Equiv.refl J) := by
    ext i j
    rfl
  rw [he, Matrix.rank_submatrix, Matrix.rank_transpose, hi, Matrix.rank_transpose, hj,
    Fintype.card_coe, hJ]

/-- The Gram coefficient indexed by the actual matrix rank is a nonzero polynomial. -/
theorem gramCoeff_rank_ne_zero (M : Matrix Row Col K) :
    gramCoeff M M.rank ≠ 0 := by
  obtain ⟨I, J, index, hJ, hdet⟩ := exists_rank_minor M
  rw [← hJ]
  exact gramCoeff_ne_zero M I J index hdet

/-- A nonzero coefficient at index card Col minus r witnesses a principal minor of size r. -/
theorem rank_ge_of_charpoly_coeff_ne_zero (A : Matrix Col Col K) (r : ℕ)
    (hr : r ≤ Fintype.card Col)
    (h : A.charpoly.coeff (Fintype.card Col - r) ≠ 0) : r ≤ A.rank := by
  obtain ⟨J, hJ, hdet⟩ : ∃ J ∈ Finset.univ.powersetCard r,
      (A.submatrix (Subtype.val : J → Col) Subtype.val).det ≠ 0 := by
    by_contra! hz
    apply h
    rw [Matrix.charpoly_coeff_eq_sum_minors A r hr, Finset.sum_eq_zero hz, mul_zero]
  have hminor := A.rank_submatrix_le (Subtype.val : J → Col) (Subtype.val : J → Col)
  rwa [Matrix.rank_of_det_ne_zero hdet, Fintype.card_coe, (Finset.mem_powersetCard.mp hJ).2]
    at hminor

/-- The nonzero coefficient at the input rank certifies that the compression preserved the kernel. -/
theorem scaledGram_rank_and_ker (M : Matrix Row Col K) (d : Row → K) (e : Col → K)
    (h : (scaledGram M d e).charpoly.coeff (Fintype.card Col - M.rank) ≠ 0) :
    (scaledGram M d e).rank = M.rank ∧ (scaledGram M d e).mulVecLin.ker = M.mulVecLin.ker := by
  have hrle : (scaledGram M d e).rank ≤ M.rank := by
    unfold scaledGram
    exact (rank_mul_le_right _ _).trans ((rank_mul_le_right _ _).trans (rank_mul_le_right _ _))
  have heq := hrle.antisymm
    (rank_ge_of_charpoly_coeff_ne_zero _ _ M.rank_le_card_width h)
  refine ⟨heq, ?_⟩
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · simp only [scaledGram, ← Matrix.mul_assoc, Matrix.mulVecLin_mul]
    exact LinearMap.ker_le_ker_comp _ _
  · have hS := (scaledGram M d e).mulVecLin.finrank_range_add_finrank_ker
    have hM := M.mulVecLin.finrank_range_add_finrank_ker
    rw [← Matrix.rank, heq] at hS
    rw [← Matrix.rank] at hM
    omega

/-- The same coefficient certifies a kernel equal to the input kernel and complementary to the range. -/
theorem scaledGram_isCompl (M : Matrix Row Col K) (d : Row → K) (e : Col → K)
    (h : (scaledGram M d e).charpoly.coeff (Fintype.card Col - M.rank) ≠ 0) :
    IsCompl M.mulVecLin.ker (scaledGram M d e).mulVecLin.range := by
  obtain ⟨hrank, hker⟩ := scaledGram_rank_and_ker M d e h
  rw [← hker]
  apply Randomized.isCompl_ker_range_of_charpoly_coeff_ne_zero
  rw [← Matrix.rank, hrank, finrank_pi, ← Matrix.toLin'_apply', Matrix.charpoly_toLin']
  exact h

end Cogentic.RandomizedGramRank
