import Cogentic.Rank

/-! Deterministic removal of low-mass error rows in the centered Gram. -/

namespace Cogentic
open scoped BigOperators
open Finset

/-- Large row errors can be discarded in one pass. The threshold charges the
entire mass of every newly discarded row to its squared error; the surviving
rows have uniformly small interaction with the final deleted set. -/
theorem stable_gram_deletion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (initial targetRows : Finset ι) (mass : ι → ℝ) (err : ι → ι → ℝ)
    (cap δ : ℝ) (cm : 0 < cap) (dp : 0 < δ) (mp : ∀ i, 0 < mass i)
    (clean : Disjoint initial targetRows) (init : ∑ i ∈ initial, mass i ≤ cap/2)
    (small : 8*(∑ i, ∑ j, (err i j)^2) ≤ δ^2)
    (targets : ∀ i ∈ targetRows, 4*cap*(∑ j, (err i j)^2) < δ^2*mass i) :
    ∃ D : Finset ι, initial ⊆ D ∧ Disjoint D targetRows ∧ (∑ i ∈ D, mass i) ≤ cap ∧
      ∀ i ∉ D, 2*∑ j ∈ D, Real.sqrt (mass j)*|err i j| ≤ δ*Real.sqrt (mass i) := by
  classical
  let R := fun i => ∑ j, (err i j)^2
  let bad := univ.filter (fun i => δ^2*mass i ≤ 4*cap*R i)
  let D := initial ∪ bad
  have Rpos (i) : 0 ≤ R i := sum_nonneg (fun j _ => sq_nonneg _)
  have badCharge : δ^2*(∑ i ∈ bad, mass i) ≤ 4*cap*(∑ i ∈ bad, R i) := by
    simp only [mul_sum]
    exact sum_le_sum fun i hi => (mem_filter.mp hi).2
  have restrictedRows : ∑ i ∈ bad, R i ≤ ∑ i, R i :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => Rpos i)
  have badCap : ∑ i ∈ bad, mass i ≤ cap/2 := by
    apply le_of_mul_le_mul_left (a:=δ^2) _ (sq_pos_of_pos dp)
    have h := badCharge.trans (mul_le_mul_of_nonneg_left restrictedRows (by positivity : 0≤4*cap))
    have bound := mul_le_mul_of_nonneg_left small cm.le
    change cap*(8*∑ i, R i) ≤ _ at bound
    linarith
  have total : ∑ j ∈ D, mass j ≤ cap := by
    have both := sum_union_inter (s₁:=initial) (s₂:=bad) (f:=mass)
    have overlap : 0 ≤ ∑ i ∈ initial ∩ bad, mass i := sum_nonneg (fun i _ => (mp i).le)
    dsimp [D]
    linarith
  refine ⟨D,subset_union_left,?_,total,?_⟩
  · apply Finset.disjoint_left.mpr
    intro i inD pro
    rcases mem_union.mp inD with orig|large
    · exact disjoint_left.mp clean orig pro
    · exact (not_lt_of_ge (mem_filter.mp large).2) (targets i pro)
  · intro i keep
    have good : 4*cap*R i < δ^2*mass i := lt_of_not_ge (fun e =>
      keep (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,e⟩)))
    have restricted : ∑ j ∈ D, (err i j)^2 ≤ R i :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
    have cs := sum_mul_sq_le_sq_mul_sq D (fun j => Real.sqrt (mass j)) (fun j => |err i j|)
    simp only [Real.sq_sqrt (mp _).le,sq_abs] at cs
    have mpos : 0 ≤ ∑ j ∈ D, mass j := sum_nonneg (fun j _ => (mp j).le)
    have ene := cs.trans ((mul_le_mul_of_nonneg_left restricted mpos).trans
      (mul_le_mul_of_nonneg_right total (Rpos i)))
    have sqrtSq := Real.sq_sqrt (mp i).le
    have sign : 0 ≤ δ*Real.sqrt (mass i) := by positivity
    have sq : (2*∑ j ∈ D, Real.sqrt (mass j)*|err i j|)^2 ≤ (δ*Real.sqrt (mass i))^2 := by
      rw [mul_pow δ, sqrtSq]
      nlinarith
    exact le_of_sq_le_sq sq sign

end Cogentic

#print axioms Cogentic.stable_gram_deletion
