import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace Cogentic.RandomizedGenusMixing

open scoped BigOperators

variable {I X G : Type*} {Ω : I → Type*}
variable [Fintype I] [DecidableEq I] [Fintype X] [CommMonoid G] [∀ i, Fintype (Ω i)]

/-- Product law for independent choices from the retained bands. -/
noncomputable def identityMass [DecidableEq G] (point : ∀ i, Ω i → G)
    (weight : ∀ i, Ω i → ℝ) : ℝ :=
  ∑ sample : ∀ i, Ω i,
    if (∏ i, point i (sample i)) = 1 then ∏ i, weight i (sample i) else 0

/-- The mean of a sign character on one retained band. -/
noncomputable def bandMean (point : ∀ i, Ω i → G) (weight : ∀ i, Ω i → ℝ)
    (χ : X → G →* ℝ) (i : I) (ξ : X) : ℝ :=
  ∑ v : Ω i, χ ξ (point i v) * weight i v

/-- Orthogonality only on single group elements suffices to factor the
Fourier expression into one empirical mean per band. -/
theorem identity_mass_fourier [DecidableEq G] (point : ∀ i, Ω i → G)
    (weight : ∀ i, Ω i → ℝ) (χ : X → G →* ℝ)
    (orthogonal : ∀ g : G, (∑ ξ, χ ξ g) = if g = 1 then (Fintype.card X : ℝ) else 0) :
    (Fintype.card X : ℝ) * identityMass point weight =
      ∑ ξ : X, ∏ i, bandMean point weight χ i ξ := by
  classical
  calc
    _ = ∑ sample : ∀ i, Ω i, (∑ ξ, χ ξ (∏ i, point i (sample i))) *
        (∏ i, weight i (sample i)) := by
      unfold identityMass
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun sample _ => ?_
      rw [orthogonal]
      split <;> simp_all
    _ = ∑ ξ : X, ∑ sample : ∀ i, Ω i,
        ∏ i, χ ξ (point i (sample i)) * weight i (sample i) := by
      simp only [Finset.sum_mul, map_prod, Finset.prod_mul_distrib]
      exact Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun ξ _ => ?_
      exact (Fintype.prod_sum (fun i v => χ ξ (point i v) * weight i v)).symm

/-- For empirical bands, the product law is the count of accepted tuples
divided by the product of the band sizes. Indexing by samples retains repetitions. -/
theorem empirical_identity_mass [DecidableEq G] (point : ∀ i, Ω i → G) :
    identityMass point (fun i _ => 1 / (Fintype.card (Ω i) : ℝ)) =
      (((Finset.univ : Finset (∀ i, Ω i)).filter
        (fun sample => (∏ i, point i (sample i)) = 1)).card : ℝ) /
        ∏ i, (Fintype.card (Ω i) : ℝ) := by
  unfold identityMass
  simp only [one_div, Finset.prod_inv_distrib]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- The exact Fourier formula for independently sampled empirical lists. -/
theorem empirical_identity_fourier [DecidableEq G] (point : ∀ i, Ω i → G) (χ : X → G →* ℝ)
    (orthogonal : ∀ g : G, (∑ ξ, χ ξ g) = if g = 1 then (Fintype.card X : ℝ) else 0) :
    (Fintype.card X : ℝ) *
        ((((Finset.univ : Finset (∀ i, Ω i)).filter
          (fun sample => (∏ i, point i (sample i)) = 1)).card : ℝ) /
          ∏ i, (Fintype.card (Ω i) : ℝ)) =
      ∑ ξ : X, ∏ i, (∑ v : Ω i, χ ξ (point i v)) / (Fintype.card (Ω i) : ℝ) := by
  rw [← empirical_identity_mass]
  simpa only [bandMean, div_eq_mul_inv, one_mul, ← Finset.sum_mul] using
    identity_mass_fourier point (fun i _ => 1 / (Fintype.card (Ω i) : ℝ)) χ orthogonal

/-- Per-band biases multiply. The scaled probability of the identity differs
from one by at most the number of nontrivial characters times that product. -/
theorem identity_mass_bias [DecidableEq G] (point : ∀ i, Ω i → G)
    (weight : ∀ i, Ω i → ℝ) (χ : X → G →* ℝ) (trivial : X) (bias : I → ℝ)
    (orthogonal : ∀ g : G, (∑ ξ, χ ξ g) = if g = 1 then (Fintype.card X : ℝ) else 0)
    (htrivial : ∀ g, χ trivial g = 1) (hnormal : ∀ i, (∑ v : Ω i, weight i v) = 1)
    (hbias : ∀ i ξ, ξ ≠ trivial → |bandMean point weight χ i ξ| ≤ bias i) :
    |(Fintype.card X : ℝ) * identityMass point weight - 1| ≤
      ((Fintype.card X : ℝ) - 1) * ∏ i, bias i := by
  classical
  let term (ξ : X) := ∏ i, bandMean point weight χ i ξ
  have ht : term trivial = 1 := by
    simp [term, bandMean, htrivial, hnormal]
  have hsum := Finset.sum_erase_add (Finset.univ : Finset X) term (Finset.mem_univ trivial)
  rw [identity_mass_fourier point weight χ orthogonal]
  change |(∑ ξ, term ξ) - 1| ≤ _
  rw [← hsum, ht, add_sub_cancel_right]
  calc
    _ ≤ ∑ ξ ∈ (Finset.univ : Finset X).erase trivial, |term ξ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ξ ∈ (Finset.univ : Finset X).erase trivial, ∏ i, bias i := by
      refine Finset.sum_le_sum fun ξ hξ => ?_
      rw [show |term ξ| = ∏ i, |bandMean point weight χ i ξ| by simp [term, Finset.abs_prod]]
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ =>
        hbias i ξ (Finset.ne_of_mem_erase hξ)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ trivial),
        Finset.card_univ, Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨trivial⟩), Nat.cast_one]

end Cogentic.RandomizedGenusMixing
