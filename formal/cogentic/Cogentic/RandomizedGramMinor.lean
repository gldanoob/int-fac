import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! A specialization witnessing the nonzero principal-minor coefficient for a scaled Gram matrix. -/

namespace Cogentic.RandomizedGramMinor

open Matrix
open scoped BigOperators

variable {K Row Col : Type*} [CommRing K]
variable [Fintype Row] [DecidableEq Row] [Fintype Col] [DecidableEq Col]

/-- Scale the rows of the Gram matrix after inserting the diagonal row weights. -/
def scaledGram (M : Matrix Row Col K) (d : Row → K) (e : Col → K) : Matrix Col Col K :=
  diagonal e * (Mᵀ * (diagonal d * M))

theorem scaledGram_apply (M : Matrix Row Col K) (d : Row → K) (e : Col → K) (i j : Col) :
    scaledGram M d e i j = e i * ∑ a, M a i * (d a * M a j) := by
  rw [scaledGram, diagonal_mul, Matrix.mul_apply]
  simp only [transpose_apply, diagonal_mul]

/-- A rectangular minor with chosen row and column sets, indexed by its column set. -/
def selectedMinor (M : Matrix Row Col K) (I : Finset Row) (J : Finset Col)
    (index : J ≃ I) : Matrix J J K :=
  M.submatrix (fun j => (index j : Row)) Subtype.val

/-- Zero-one weights retain the chosen square minor and its transpose on the principal block. -/
theorem scaledGram_submatrix_indicator (M : Matrix Row Col K)
    (I : Finset Row) (J : Finset Col) (index : J ≃ I) :
    (scaledGram M (fun i => if i ∈ I then 1 else 0)
      (fun j => if j ∈ J then 1 else 0)).submatrix
        (Subtype.val : J → Col) Subtype.val =
      (selectedMinor M I J index)ᵀ * selectedMinor M I J index := by
  ext i j
  simp only [submatrix_apply, scaledGram_apply, i.property, if_true, one_mul, Matrix.mul_apply,
    transpose_apply, selectedMinor]
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_zero]
  rw [← Finset.sum_filter, Finset.sum_subtype _ (p := fun a => a ∈ I) (fun a => by simp)]
  exact (index.sum_comp (fun a : I => M a i * M a j)).symm

/-- At the zero-one weights, only the selected principal minor contributes at its size. -/
theorem charpoly_coeff_indicator (M : Matrix Row Col K)
    (I : Finset Row) (J : Finset Col) (index : J ≃ I) :
    (scaledGram M (fun i => if i ∈ I then 1 else 0)
      (fun j => if j ∈ J then 1 else 0)).charpoly.coeff (Fintype.card Col - J.card) =
      (-1) ^ J.card * (selectedMinor M I J index).det ^ 2 := by
  rw [Matrix.charpoly_coeff_eq_sum_minors _ _ (by simpa using J.card_le_univ)]
  congr 1
  calc
    _ = ((scaledGram M (fun i => if i ∈ I then 1 else 0)
          (fun j => if j ∈ J then 1 else 0)).submatrix
            (Subtype.val : J → Col) Subtype.val).det := by
      apply Finset.sum_eq_single J
      · intro S hS hSJ
        have hcard := (Finset.mem_powersetCard.mp hS).2
        have hsub : ¬ S ⊆ J := fun h => hSJ (Finset.eq_of_subset_of_card_le h hcard.ge)
        obtain ⟨i, hiS, hiJ⟩ := Finset.not_subset.mp hsub
        apply Matrix.det_eq_zero_of_row_eq_zero ⟨i, hiS⟩
        intro j
        simp [scaledGram_apply, hiJ]
      · intro h
        exact (h (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ J, rfl⟩)).elim
    _ = _ := by
      rw [scaledGram_submatrix_indicator M I J index, Matrix.det_mul, Matrix.det_transpose, pow_two]


/-- The rank-index coefficient of the Gram characteristic polynomial, in independent weights. -/
noncomputable def gramCoeff (M : Matrix Row Col K) (r : ℕ) : MvPolynomial (Row ⊕ Col) K :=
  (scaledGram (M.map MvPolynomial.C)
    (fun i => MvPolynomial.X (Sum.inl i))
    (fun j => MvPolynomial.X (Sum.inr j))).charpoly.coeff (Fintype.card Col - r)

theorem eval_gramCoeff (M : Matrix Row Col K) (r : ℕ) (d : Row → K) (e : Col → K) :
    MvPolynomial.eval (Sum.elim d e) (gramCoeff M r) =
      (scaledGram M d e).charpoly.coeff (Fintype.card Col - r) := by
  let S : Matrix Col Col (MvPolynomial (Row ⊕ Col) K) := scaledGram (M.map MvPolynomial.C)
    (fun i => MvPolynomial.X (Sum.inl i))
    (fun j => MvPolynomial.X (Sum.inr j))
  let f := MvPolynomial.eval (Sum.elim d e)
  have hmap : S.map f = scaledGram M d e := by
    ext i j
    simp [S, f, scaledGram_apply]
  change f (S.charpoly.coeff (Fintype.card Col - r)) = _
  rw [← hmap, Matrix.charpoly_map, Polynomial.coeff_map]

/-- A nonsingular square minor certifies that the corresponding coefficient polynomial is nonzero. -/
theorem gramCoeff_ne_zero [IsDomain K] (M : Matrix Row Col K)
    (I : Finset Row) (J : Finset Col) (index : J ≃ I)
    (h : (selectedMinor M I J index).det ≠ 0) :
    gramCoeff M J.card ≠ 0 := by
  intro hz
  have heval := eval_gramCoeff M J.card (fun i => if i ∈ I then 1 else 0)
    (fun j => if j ∈ J then 1 else 0)
  rw [hz, map_zero, charpoly_coeff_indicator M I J index] at heval
  exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ h)) heval.symm


/-- Every degree-r principal minor contributes at most 2r to the diagonal-weight degree. -/
theorem totalDegree_gramCoeff [Nontrivial K] (M : Matrix Row Col K) (r : ℕ)
    (hr : r ≤ Fintype.card Col) :
    (gramCoeff M r).totalDegree ≤ 2 * r := by
  let S : Matrix Col Col (MvPolynomial (Row ⊕ Col) K) := scaledGram
    (M.map MvPolynomial.C) (fun i => MvPolynomial.X (Sum.inl i))
    (fun j => MvPolynomial.X (Sum.inr j))
  change (S.charpoly.coeff (Fintype.card Col - r)).totalDegree ≤ _
  rw [Matrix.charpoly_coeff_eq_sum_minors S r hr]
  have hsign : ((-1 : MvPolynomial (Row ⊕ Col) K) ^ r).totalDegree = 0 := by
    rw [← show MvPolynomial.C ((-1 : K) ^ r) =
      ((-1 : MvPolynomial (Row ⊕ Col) K) ^ r) by simp, MvPolynomial.totalDegree_C]
  refine (MvPolynomial.totalDegree_mul ..).trans ?_
  simp only [hsign, zero_add]
  have hentry (i j : Col) : (S i j).totalDegree ≤ 2 := by
    simp only [S, scaledGram_apply, Matrix.map_apply]
    refine (MvPolynomial.totalDegree_mul ..).trans ?_
    rw [MvPolynomial.totalDegree_X]
    refine Nat.add_le_add_left (MvPolynomial.totalDegree_finsetSum_le (d := 1) ?_) 1
    intro a _
    refine (MvPolynomial.totalDegree_mul ..).trans ?_
    simp only [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_mul ..).trans ?_
    simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro J hJ
  rw [Matrix.det_apply']
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  refine (MvPolynomial.totalDegree_mul ..).trans ?_
  rw [← map_intCast (MvPolynomial.C : K →+* MvPolynomial (Row ⊕ Col) K),
    MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd ..).trans ?_
  calc
    _ ≤ ∑ _i : J, 2 := Finset.sum_le_sum fun j _ => hentry (σ j) j
    _ = _ := by simp [(Finset.mem_powersetCard.mp hJ).2, Nat.mul_comm]


/-- The vanishing fraction for independent uniform weights in a common finite sample set. -/
theorem vanishing_fraction_le [IsDomain K] [DecidableEq K] (M : Matrix Row Col K)
    (I : Finset Row) (J : Finset Col) (index : J ≃ I)
    (h : (selectedMinor M I J index).det ≠ 0)
    {n : ℕ} (numbering : Row ⊕ Col ≃ Fin n) (samples : Finset K) :
    (((Fintype.piFinset fun _ : Fin n => samples).filter (fun x =>
      (scaledGram M (fun i => x (numbering (Sum.inl i)))
        (fun j => x (numbering (Sum.inr j)))).charpoly.coeff
        (Fintype.card Col - J.card) = 0)).card : ℚ≥0) / (samples.card : ℚ≥0) ^ n ≤
      (2 * J.card : ℕ) / (samples.card : ℚ≥0) := by
  let p := MvPolynomial.rename numbering (gramCoeff M J.card)
  have hp : p ≠ 0 :=
    (MvPolynomial.rename_eq_zero_iff_of_injective _ numbering.injective).not.mpr (gramCoeff_ne_zero M I J index h)
  have heval (x : Fin n → K) : MvPolynomial.eval x p =
      (scaledGram M (fun i => x (numbering (Sum.inl i)))
        (fun j => x (numbering (Sum.inr j)))).charpoly.coeff
        (Fintype.card Col - J.card) := by
    dsimp only [p]
    rw [MvPolynomial.eval_rename, ← eval_gramCoeff]
    congr 2
    exact funext (fun a => by cases a <;> rfl)
  simp_rw [← heval]
  refine (MvPolynomial.schwartz_zippel_totalDegree hp samples).trans ?_
  have hd := (MvPolynomial.totalDegree_rename_le numbering _).trans
    (totalDegree_gramCoeff M J.card (by simpa using J.card_le_univ))
  gcongr

end Cogentic.RandomizedGramMinor
