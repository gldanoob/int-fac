import Mathlib.LinearAlgebra.Eigenspace.Zero

namespace Cogentic.Randomized

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A nonzero coefficient at the nullity forces the generalized zero
eigenspace to equal the kernel. -/
theorem maxGenEigenspace_zero_eq_ker_of_charpoly_coeff_ne_zero (S : End K V)
    (hcoeff : S.charpoly.coeff (finrank K (LinearMap.ker S)) ≠ 0) :
    S.maxGenEigenspace 0 = LinearMap.ker S := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · intro v hv
    exact (S.mem_maxGenEigenspace 0 v).mpr ⟨1, by simpa using hv⟩
  · rw [S.finrank_maxGenEigenspace_zero_eq]
    exact Polynomial.natTrailingDegree_le_of_ne_zero hcoeff

/-- For an endomorphism of dimension `s` and rank `r`, a nonzero
coefficient of `X^(s-r)` implies that the kernel complements the range. -/
theorem isCompl_ker_range_of_charpoly_coeff_ne_zero (S : End K V)
    (hcoeff : S.charpoly.coeff (finrank K V - finrank K (LinearMap.range S)) ≠ 0) :
    IsCompl (LinearMap.ker S) (LinearMap.range S) := by
  have hdim := S.finrank_range_add_finrank_ker
  have hn : finrank K V - finrank K (LinearMap.range S) = finrank K (LinearMap.ker S) := by
    rw [← hdim, Nat.add_sub_cancel_left]
  rw [hn] at hcoeff
  have hgen := maxGenEigenspace_zero_eq_ker_of_charpoly_coeff_ne_zero S hcoeff
  apply (Submodule.isCompl_iff_disjoint _ _ (by rw [add_comm, hdim])).mpr
  apply Submodule.disjoint_def.mpr
  intro z hz hr
  obtain ⟨v, rfl⟩ := hr
  have hv : v ∈ S.maxGenEigenspace 0 := by
    refine (S.mem_maxGenEigenspace 0 v).mpr ⟨2, ?_⟩
    simpa [pow_two, Module.End.mul_apply] using hz
  rw [hgen] at hv
  exact LinearMap.mem_ker.mp hv

end Cogentic.Randomized
