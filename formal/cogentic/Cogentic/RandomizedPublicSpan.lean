import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity

namespace Cogentic.Randomized

variable {K X Y V : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup V] [Module K V]

/-- There is no dependency using a nonzero anchored vector exactly when the
anchored map is injective modulo the public span. -/
theorem injective_mod_public_iff_no_anchored_dependency
    (P : X →ₗ[K] V) (A : Y →ₗ[K] V) :
    Function.Injective ((LinearMap.range P).mkQ.comp A) ↔
      ¬ ∃ x y, y ≠ 0 ∧ P x + A y = 0 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  have hmem (y : Y) : ((LinearMap.range P).mkQ.comp A) y = 0 ↔ A y ∈ LinearMap.range P := by
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro h ⟨x, y, hy, hxy⟩
    apply hy (h y ((hmem y).2 ?_))
    refine ⟨-x, ?_⟩
    rw [map_neg, eq_neg_of_add_eq_zero_left hxy, neg_neg]
  · intro h y hy
    obtain ⟨x, hx⟩ := (hmem y).1 hy
    by_contra hne
    apply h ⟨-x, y, hne, ?_⟩
    rw [map_neg, hx, neg_add_cancel]

/-- The dimension of the quotient bounds how many independent anchored
coordinates the public span can leave without any tagged dependency. -/
theorem anchored_dependency_of_finrank_quotient_lt [Module.Finite K V]
    (P : X →ₗ[K] V) (A : Y →ₗ[K] V)
    (h : Module.finrank K (V ⧸ LinearMap.range P) < Module.finrank K Y) :
    ∃ x y, y ≠ 0 ∧ P x + A y = 0 := by
  by_contra hnone
  have hinj := (injective_mod_public_iff_no_anchored_dependency P A).2 hnone
  exact (not_lt_of_ge (LinearMap.finrank_le_finrank_of_injective hinj)) h

/-- For a finite column index, exceeding the public quotient dimension forces
a dependency with at least one nonzero anchored coordinate. -/
theorem anchored_dependency_of_card_quotient_lt [Module.Finite K V]
    {ι : Type*} [Fintype ι] (P : X →ₗ[K] V) (A : (ι → K) →ₗ[K] V)
    (h : Module.finrank K (V ⧸ LinearMap.range P) < Fintype.card ι) :
    ∃ x y, y ≠ 0 ∧ P x + A y = 0 := by
  apply anchored_dependency_of_finrank_quotient_lt P A
  rwa [Module.finrank_fintype_fun_eq_card]

end Cogentic.Randomized
